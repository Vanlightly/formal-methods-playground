-------------------------------- MODULE swim_stats --------------------------------

(*
Originally based on the Atomix SWIM TLA+ specification (https://github.com/atomix/atomix-tlaplus/blob/master/SWIM/SWIM.tla) 
but now heavily modified. The original spec was designed entirely on safety properties, allowing each action equal probability, 
and without any features related to optimising time to convergence (as those features are not for safety). 

This spec cares a great deal about modelling all the aspects of the SWIM paper related to optimising time to convergence and modelling
some fairness of scheduling of probes.

Summary of modifications:
- Message passing modified to a request/response mechanism without duplication. For simulation
  we want to measure statistical properties under normal network conditions (for now).
- As per the SWIM paper:
    - Gossip messages (peer states) are piggybacked on probe and ack messages.
    - The number of peer states per probe/ack is limited
    - When there are more peer states than can fit, those with the fewest disseminations are prioritised.
    - Suspected members are marked as dead after a timeout (number of protocol rounds)
- Fair scheduling is modelled to ensure that:
    - the probe rate of each member is balanced
    - each member randomly picks another member to probe, but with guaranteed bounds 
      (i.e. cannot randomly pick the same member over and over again)
- The ensemble of members start all seeing each other as alive, but one being recently dead. 
  The aim is to measure the number of probes in order for the ensemble to converge on this new state.
  Shortly after reaching convergence, the spec will deadlock. This is by design as it helps
  simulation by halting when we reach the objective. On deadlocking, any statistical properties
  being tracked are printed out in a csv format.
Not implemented:
- Probe requests
*)

EXTENDS Naturals, FiniteSets, Sequences, TLC, TLCExt, Integers


CONSTANTS Member,                \* The set of possible members
          Nil,                   \* Empty numeric value
          
          Alive,                 \* Numeric member state 
          Suspect,               \* Numeric member state
          Dead,                  \* Numeric member state
          
          ProbeMessage,          \* Message type: probe
          AckMessage,            \* Message type: ack
          ProbeRequestMessage,   \* Message type: probe request
          ForwardedAckMessage,   \* Message type: indirect ack forwarded
          
          PeerGroupSize,          \* The number of peers to send probe requests when a direct probe fails
          SuspectTimeout,         \* The number of failed probes before suspected node made dead
          DisseminationLimit,     \* The lambda log n value (the maximum number of times a given update can be piggybacked)
          MaxUpdatesPerPiggyBack, \* The maximum  number of state updates to be included in
                                  \* any given piggybacked gossip message
          
          DeadMemberCount,        \* The number of dead members the ensemble need to detect
          ForceRunToRound

\* The values of member states must be sequential
ASSUME Alive > Suspect /\ Suspect > Dead
ASSUME DeadMemberCount \in Nat
ASSUME SuspectTimeout \in Nat
ASSUME MaxUpdatesPerPiggyBack \in (Nat \ {0})
            
VARIABLES \* actual state in the protocol
          incarnation,          \* Member incarnation numbers
          peer_states,          \* The known state that each member has on its peers
          round,                \* Each member keeps track of which round of the protocol it is in
          pending_direct_ack,   \* Each member keeps track of members it is pending a direct ack from
          pending_indirect_ack, \* Each member keeps track of members it is pending an idirect ack from
          probe_ctr,            \* Each member keeps track of how many probes it has sent to each peer
                                \* It randomly selects peers, but keeps the number of probes balanced
          \* messaging passing
          messages,             \* a function of all messages       
                    
          \* to end simulation once convergence reached
          sim_complete
          
vars == <<incarnation, peer_states, messages, pending_direct_ack, pending_indirect_ack, probe_ctr, round, sim_complete>>

updates_pr_ctr(r) ==
    (r * 100)

eff_updates_pr_ctr(r) ==
    (r * 100) + 1

suspect_ctr(r) ==
    (r * 100) + 2
    
suspect_states_ctr(r) ==
    (r * 100) + 3
    
dead_ctr(r) ==
    (r * 100) + 4
    
dead_states_ctr(r) ==
    (r * 100) + 5     
    

ResetStats ==
    \A r \in 1..1000 : 
        /\ TLCSet(updates_pr_ctr(r), 0)
        /\ TLCSet(eff_updates_pr_ctr(r), 0)
        /\ TLCSet(suspect_ctr(r), 0)
        /\ TLCSet(dead_ctr(r), 0)
        /\ TLCSet(suspect_states_ctr(r), 0)
        /\ TLCSet(dead_states_ctr(r), 0)

Init ==
    LET dead_members == CHOOSE s \in SUBSET Member : Cardinality(s) = DeadMemberCount
    IN 
        /\ incarnation = [m \in Member |-> IF m \in dead_members THEN Nil ELSE 1]
        /\ peer_states = [m \in Member |-> [m1 \in Member |-> 
                                                [incarnation    |-> 1, 
                                                 state          |-> Alive, 
                                                 round          |-> 1, 
                                                 disseminations |-> DisseminationLimit]]]
        /\ round = [m \in Member |-> 1]
        /\ messages = [msg \in {} |-> 0]
        /\ pending_direct_ack = [m \in Member |-> Nil]
        /\ pending_indirect_ack = [m \in Member |-> Nil]
        /\ probe_ctr = [m \in Member |-> [m1 \in Member |-> 0]]
        /\ sim_complete = 0
        /\ ResetStats

(*****************************************************)
(*************** Messaging passing *******************)
(*****************************************************)

MessageDoesNotArrive(msg) ==
    IF incarnation[msg.dest] = Nil THEN TRUE ELSE FALSE

\* Send a request only if the request has already not been sent
SendMessage(msg) ==
    /\ msg \notin DOMAIN messages
    /\ IF MessageDoesNotArrive(msg)
       THEN messages' = messages @@ (msg :> 0)
       ELSE messages' = messages @@ (msg :> 1)

SendMessages(send_msgs) ==
    /\ \A msg \in send_msgs : msg \notin DOMAIN messages
    /\ messages' = messages @@ [msg \in send_msgs |-> IF MessageDoesNotArrive(msg) THEN 0 ELSE 1]
    
\* Mark one message as processed and send a new message   
ProcessedOneAndSendAnother(received_msg, send_msg) ==
    /\ received_msg \in DOMAIN messages
    /\ send_msg \notin DOMAIN messages
    /\ messages[received_msg] >= 1
    /\ IF MessageDoesNotArrive(send_msg)
       THEN messages' = [messages EXCEPT ![received_msg] = 0] @@ (send_msg :> 0)
       ELSE messages' = [messages EXCEPT ![received_msg] = 0] @@ (send_msg :> 1)
   
MessageProcessed(msg) ==
    /\ msg \in DOMAIN messages
    /\ messages[msg] >= 1
    /\ messages' = [messages EXCEPT ![msg] = @ - 1]

RegisterPendingDirectAck(member, peer) ==
    /\ pending_direct_ack' = [pending_direct_ack EXCEPT ![member] = peer]
    /\ probe_ctr' = [probe_ctr EXCEPT ![member][peer] = @ + 1]

RegisterReceivedDirectAck(member) ==
    pending_direct_ack' = [pending_direct_ack EXCEPT ![member] = Nil]

(*****************************************************)
(*************** Helper operators ********************)
(*****************************************************)

MaxRound ==
    LET highest == CHOOSE m1 \in Member :
        \A m2 \in Member: round[m1] >= round[m2]
    IN round[highest]

\* The set of all members that are alive
LiveMembers ==
    { m \in Member : incarnation[m] # Nil }
    
\* The real state being either dead or alive. The real state of a member 
\* cannot be "suspected".
RealStateOfMember(member) ==
    IF incarnation[member] = Nil THEN Dead ELSE Alive

\* TRUE when all live members see the true state of the universe
Converged ==
    \A m1 \in Member :
        \/ incarnation[m1] = Nil
        \/ /\ incarnation[m1] # Nil
           /\ \A m2 \in Member :
                \/ m1 = m2
                \/ /\ m1 # m2
                   /\ peer_states[m1][m2].state = RealStateOfMember(m2)

\* TRUE when all live members see the true state of the universe in the next state
WillBeConverged ==
    \A m1 \in Member :
        \/ incarnation[m1] = Nil
        \/ /\ incarnation[m1] # Nil
           /\ \A m2 \in Member :
                \/ m1 = m2
                \/ /\ m1 # m2
                   /\ peer_states'[m1][m2].state = RealStateOfMember(m2)
                   

(************************************************************************) 
(******************** OUTGOING GOSSIP ***********************************)
(************************************************************************)

(* NOTES
Peer states are selected for piggybacking on probes, probe requests and acks based on:
1. The maximum number of times a peer state can be disseminated (lambda log n in the paper
   but in this spec the constant DisseminationLimit.
2. The maximum number of peer states that can be piggybacked on any given probe or ack.
   In this spec the constant MaxUpdatesPerPiggyBack.
3. In the case that all valid peer states do not fit, prioritise those that have been 
   disseminated fewer times.
*)

\* Returns TRUE or FALSE as to whether an individual peer state is new for this member
\* It is new only if:
\* - its incarnation number is > than the known incarnation number of the target member
\* - its incarnation number equals the known incarnation number of the target member but its state has higher precedence
IsNewInformation(member, peer, peer_state) ==
    \/ peer_state.incarnation > peer_states[member][peer].incarnation
    \/ /\ peer_state.incarnation = peer_states[member][peer].incarnation
       /\ peer_state.state < peer_states[member][peer].state

PeersUnderDisseminationsLimit(member, incoming_gossip) ==
    { m1 \in Member : 
        /\ m1 # member
        /\ peer_states[member][m1].disseminations < DisseminationLimit
        \* peer not a candidate if incoming gossip contains more up to date information
        /\ IF m1 \in DOMAIN incoming_gossip
           THEN IF IsNewInformation(member, m1, incoming_gossip[m1]) THEN FALSE ELSE TRUE
           ELSE TRUE
    }
    
\* Choose the peer states to gossip based on the MaxUpdatesPerGossip and when there is more
\* gossip than can be accomodated in a single message, choose the peer states
\* in order of fewest disseminations first
Prioritise(member, candidate_peers, limit) ==
    CHOOSE peer_subset \in SUBSET candidate_peers :
        /\ Cardinality(peer_subset) = limit
        /\ \A peer1 \in peer_subset :
            \A peer2 \in candidate_peers \ peer_subset :
                peer_states[member][peer1].disseminations <= peer_states[member][peer2].disseminations

SelectOutgoingGossip(member, incoming_gossip) ==
    LET candidate_peers == PeersUnderDisseminationsLimit(member, incoming_gossip)
    IN
        IF Cardinality(candidate_peers) <= MaxUpdatesPerPiggyBack 
        THEN [peer \in candidate_peers |-> peer_states[member][peer]]
        ELSE LET peers == Prioritise(member, candidate_peers, MaxUpdatesPerPiggyBack)
             IN [peer \in peers |-> peer_states[member][peer]]
            
IncrementPiggybackCount(member, updates_to_send) ==
    peer_states' = [peer_states EXCEPT ![member] = 
                    [peer \in Member |-> IF peer \in DOMAIN updates_to_send
                                         THEN [peer_states[member][peer] EXCEPT !.disseminations = @ + 1]
                                         ELSE peer_states[member][peer]]]          


(************************************************************************) 
(******************** RECORD STATISTICS *********************************)
(************************************************************************)

MemberCount(state, target_peer_states) ==
    Cardinality({dest \in Member : 
        \E source \in Member :
            target_peer_states[source][dest].state = state})
            
CurrentMemberCount(state) == MemberCount(state, peer_states)
NextStateMemberCount(state) == MemberCount(state, peer_states')  
            
StateCount(state, target_peer_states) ==
    LET pairs == { s \in SUBSET Member : Cardinality(s) = 2 }
    IN
    LET lower_to_higher == Cardinality({s \in pairs :
                                            \E m1, m2 \in s : 
                                                /\ target_peer_states[m1][m2].state = state
                                                /\ m1 < m2})
        higher_to_lower == Cardinality({s \in pairs :
                                            \E m1, m2 \in s : 
                                                /\ target_peer_states[m1][m2].state = state
                                                /\ m1 > m2})
    IN lower_to_higher + higher_to_lower

CurrentStateCount(state) == StateCount(state, peer_states)
NextStateStateCount(state) == StateCount(state, peer_states')
                

IsNewRoundTransitionStep(i, r1, r2, nil, mem) ==
    /\ \E m1, m2 \in mem: i[m1] # nil /\ i[m2] # nil /\ r1[m1] # r1[m2] 
    /\ \A m3, m4 \in mem: 
        \/ i[m3] = Nil
        \/ i[m4] = Nil
        \/ /\ i[m3] # nil 
           /\ i[m4] # nil 
           /\ r2[m3] = r2[m4]

MayBeRecordMemberCounts ==
    \* Is this is a step that leads to all members being on the same round then record the member count stats
        IF  IsNewRoundTransitionStep(incarnation, round, round', Nil, Member)
        THEN
            LET r == MaxRound
            IN
                /\ TLCSet(suspect_ctr(r), NextStateMemberCount(Suspect))
                /\ TLCSet(dead_ctr(r), NextStateMemberCount(Dead))
                /\ TLCSet(suspect_states_ctr(r), NextStateStateCount(Suspect))
                /\ TLCSet(dead_states_ctr(r), NextStateStateCount(Dead))
        ELSE TRUE

RecordIncomingGossipStats(member, gossip_source, incoming_updates) ==
    LET updates_ctr_id     == updates_pr_ctr(round[gossip_source])
        eff_updates_ctr_id == eff_updates_pr_ctr(round[gossip_source])
    IN 
       \* gossip cardinality
       /\ TLCSet(updates_ctr_id, TLCGet(updates_ctr_id) + Cardinality(DOMAIN incoming_updates))
       \* effective gossip cardinality
       /\ LET effective_count == Cardinality({ m \in DOMAIN incoming_updates :
                                                    IsNewInformation(member, m, incoming_updates[m])}) 
          IN TLCSet(eff_updates_ctr_id, TLCGet(eff_updates_ctr_id) + effective_count)
       \* suspect and dead counts
       /\ MayBeRecordMemberCounts         

MessageLoad(r, member) ==
    Cardinality({
        msg \in DOMAIN messages : 
            /\ \/ msg.source = member
               \/ msg.dest = member
            /\ msg.round = r
    })

PrintStats ==
    /\ LET max_stats_round == MaxRound
           cfg_str == "," \o ToString(Cardinality(Member)) 
                        \o "," \o ToString(DeadMemberCount)
                        \o "," \o ToString(SuspectTimeout)
                        \o "," \o ToString(DisseminationLimit)
                        \o "," \o ToString(MaxUpdatesPerPiggyBack)
                        \o "," \o ToString(MaxRound)
                        \o ","
       IN
        /\ PrintT("rounds" \o cfg_str \o ToString(max_stats_round))
        /\ \A r \in 1..max_stats_round : 
            \A member \in Member : PrintT("message_load_in_round" \o cfg_str \o ToString(r) \o "," \o ToString(member) \o "," \o ToString(MessageLoad(r, member)))
        /\ \A r \in 1..max_stats_round : PrintT("updates_in_round" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(updates_pr_ctr(r))))
        /\ \A r \in 1..max_stats_round : PrintT("eff_updates_in_round" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(eff_updates_pr_ctr(r))))
        /\ \A r \in 1..max_stats_round : 
            IF r = max_stats_round 
            THEN PrintT("suspected_members_count" \o cfg_str \o ToString(r) \o "," \o ToString(CurrentMemberCount(Suspect)))
            ELSE PrintT("suspected_members_count" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(suspect_ctr(r))))
        /\ \A r \in 1..max_stats_round :
            IF r = max_stats_round 
            THEN PrintT("dead_members_count" \o cfg_str \o ToString(r) \o "," \o ToString(CurrentMemberCount(Dead)))
            ELSE PrintT("dead_members_count" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(dead_ctr(r))))
        /\ \A r \in 1..max_stats_round : 
            IF r = max_stats_round 
            THEN PrintT("suspect_states_count" \o cfg_str \o ToString(r) \o "," \o ToString(CurrentStateCount(Suspect)))
            ELSE PrintT("suspect_states_count" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(suspect_states_ctr(r))))
        /\ \A r \in 1..max_stats_round :
            IF r = max_stats_round 
            THEN PrintT("dead_states_count" \o cfg_str \o ToString(r) \o "," \o ToString(CurrentStateCount(Dead)))
            ELSE PrintT("dead_states_count" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(dead_states_ctr(r))))
    /\ PrintT("converged")
    /\ ResetStats
    
MaybeEndSim ==
    \/ /\ ForceRunToRound > 0
       /\ IF \A member \in Member : round[member] <= ForceRunToRound 
          THEN UNCHANGED sim_complete
          ELSE sim_complete' = 1
    \/ /\ ForceRunToRound <= 0
       /\ IF WillBeConverged THEN sim_complete' = 1 ELSE UNCHANGED sim_complete    
    
EndSim ==
    /\ sim_complete = 1
    /\ TLCDefer(PrintStats)
    /\ sim_complete' = 2
    /\ UNCHANGED <<incarnation, peer_states, messages, pending_direct_ack, pending_indirect_ack, probe_ctr, round>>    
           
(************************************************************************) 
(******************** INCOMING GOSSIP ***********************************)
(************************************************************************)

(* NOTES
Gossip can come in on probes and acks. Any incoming gossip is merged with existing peer state,
with stale peer states being replaced by any newer gossiped state. 
Stale peer state is that which has a lower incarnation number than the gossiped state or 
which has the same incarnation number, but a lower precedence state. 
The precedence order is (highest to lowest) Dead, Suspect, Alive.
*)

ResetCountersOfRecord(record, member_round) ==
    [incarnation    |-> record.incarnation,
     state          |-> record.state,
     disseminations |-> 0,
     round          |-> member_round]

NewAliveMemberRecord(incarnation_number, member_round) ==
    [incarnation    |-> incarnation_number, 
     state          |-> Alive, 
     disseminations |-> 0, 
     round          |-> member_round]

\* updates the state of a member's peers based on incoming and outgoing gossip
\* If member's incarnation for the gossip source is stale then update it
\* Increment dissemination counters of outgoing gossip
\* Replace any peer state that is stale
MergeGossip(member, gossip_source, source_incarnation, incoming_updates, sent_updates) ==
    [peer \in Member |-> 
        IF peer = gossip_source
        THEN IF peer_states[member][gossip_source].incarnation < source_incarnation
             THEN NewAliveMemberRecord(source_incarnation, round[member])
             ELSE peer_states[member][gossip_source]
        ELSE
            LET is_in_gossip == peer \in DOMAIN incoming_updates
                is_in_sent   == peer \in DOMAIN sent_updates
            IN    
                IF is_in_gossip
                THEN IF IsNewInformation(member, peer, incoming_updates[peer])
                     THEN ResetCountersOfRecord(incoming_updates[peer], round[member])
                     ELSE IF is_in_sent
                          THEN [peer_states[member][peer] EXCEPT !.disseminations = @ + 1]
                          ELSE peer_states[member][peer]
                ELSE IF is_in_sent
                     THEN [peer_states[member][peer] EXCEPT !.disseminations = @ + 1]
                     ELSE peer_states[member][peer]]

\* Merges incoming gossip with existing state
\* increments dissemination counters of sent updates
\* records statistics
HandleGossip(member, gossip_source, source_incarnation, incoming_updates, sent_updates) ==
    LET merged == MergeGossip(member, gossip_source, source_incarnation, incoming_updates, sent_updates)
    IN /\ peer_states' = [peer_states EXCEPT ![member] = merged]
       /\ TLCDefer(RecordIncomingGossipStats(member, gossip_source, incoming_updates))
       /\ MaybeEndSim

\* Updates the state and counters of a peer of the given member
\* This is not called when an incarnation has changed, only a state change 
\* like Alive->Suspect or Suspect->Dead
UpdateState(member, peer, state) ==
    peer_states' = [peer_states EXCEPT ![member][peer] =
                        [@ EXCEPT !.state          = state,
                                  !.disseminations = 0,
                                  !.round          = round[member]]]

(************************************************************************) 
(******************** ACTION: PROBE *************************************)
(************************************************************************)

(* Notes
Triggers a probe request to a peer
* 'source' is the source of the probe
* 'dest' is the destination to which to send the probe
- Uses fair scheduling to ensure that each member more or less is sending out a similar number of probes
  and that each member is choosing other members to probe in a balanced but random fashion
- Piggybacks any gossip that will fit, incrementing its dissemination counters
- In addtion to fair scheduling controlling whether enabled or not, will not be enabled if:
   - convergence has been reached, ensuring deadlock will occur
   - there are members to expire
   - has no pending probes to the destination (probes either get an ack or fail)
*)

HasNoMembersToExpire(member) ==
    ~\E peer \in Member :
        /\ peer_states[member][peer].state = Suspect
        /\ round[member] - peer_states[member][peer].round > SuspectTimeout

IsValidProbeTarget(member, peer) ==
    /\ member # peer
    /\ peer_states[member][peer].state # Dead               \* The member believes the peer to be alive or suspect
    /\ \/ peer_states[member][peer].state # Suspect         \* If suspect, we haven't reached the suspect timeout
       \/ /\ peer_states[member][peer].state = Suspect
          /\ round[member] - peer_states[member][peer].round <= SuspectTimeout

\* This is necessary for statistics simulation to ensure that all members are
\* sending out probes at the same rate and stay within one round of each other
\* 'probe_ctr' ensures that we are balancing our probes evenly across peers 
\* 'round' keeps all members within one round of each other
IsFairlyScheduled(member, peer) ==
    /\ \A m \in Member : 
         IF IsValidProbeTarget(member, m) 
         THEN probe_ctr[member][peer] <= probe_ctr[member][m]
         ELSE TRUE
    /\ \A m1 \in Member : 
        \/ incarnation[m1] = Nil
        \/ /\ incarnation[m1] # Nil
           /\ round[member] <= round[m1]

\* The sending of a direct probe is the beginning of a new protocol period and so we need
\* to ensure some things TODO
SendDirectProbe(member, peer) ==
    /\ member # peer
    /\ sim_complete = 0
    /\ incarnation[member] # Nil            \* The member is alive
    /\ pending_indirect_ack[member] = Nil   \* The member is not waiting on a direct ack
    /\ pending_direct_ack[member] = Nil     \* The member is not waiting on an indirect ack
    /\ HasNoMembersToExpire(member)         \* Only send a probe if we have no pending expiries
    /\ IsValidProbeTarget(member, peer)     \* The peer is valid (the member think it's not dead for example)
    /\ IsFairlyScheduled(member, peer)      \* We aim to make the rate probe sending more or less balanced
    /\ LET gossip_to_send == SelectOutgoingGossip(member, <<>>)
       IN
        /\ SendMessage([type         |-> ProbeMessage,
                        source       |-> member,
                        dest         |-> peer,
                        round        |-> round[member],
                        on_behalf_of |-> Nil,
                        payload      |-> peer_states[member][peer],
                        gossip       |-> gossip_to_send])
        /\ IncrementPiggybackCount(member, gossip_to_send)
        /\ RegisterPendingDirectAck(member, peer)
        /\ UNCHANGED <<incarnation, pending_indirect_ack, round, sim_complete >>


        
(************************************************************************) 
(******************** ACTION: ReceiveProbe ******************************)
(************************************************************************)

(* Notes
Handles a probe message from a peer.
If the received incarnation is greater than the destination's incarnation number, update the
destination's incarnation number to 1 plus the received number. This can happen after a node
leaves and rejoins the cluster. If the destination is suspected by the source, increment the
destination's incarnation, enqueue an update to be gossipped, and respond with the updated
incarnation. If the destination's incarnation is greater than the source's incarnation, just
send an ack.
- Adds pending gossip (that will fit) to the ack (piggybacking)
- Adds any incoming gossip that is valid, to the local updates to be gossiped later
- May add gossip to refute being Suspect (not currently a possibility as false positives not modelled)
*)

\* Send an ack and piggyback gossip if any to send
SendAck(probe, payload, piggyback_gossip) ==
    ProcessedOneAndSendAnother(probe, 
                       [type         |-> AckMessage,
                        source       |-> probe.dest,
                        dest         |-> probe.source,
                        round        |-> probe.round,
                        on_behalf_of |-> probe.on_behalf_of,
                        payload      |-> payload,
                        gossip       |-> piggyback_gossip])
 
ReceiveProbe ==
    /\ sim_complete = 0
    /\ \E msg \in DOMAIN messages :
        /\ msg.type = ProbeMessage
        /\ messages[msg] >= 1
        /\ incarnation[msg.dest] # Nil
        /\ LET send_gossip == SelectOutgoingGossip(msg.dest, msg.gossip)
           IN 
                /\ \/ /\ msg.payload.incarnation > incarnation[msg.dest]
                      /\ incarnation' = [incarnation EXCEPT ![msg.dest] = msg.payload.incarnation + 1]
                      /\ SendAck(msg, [incarnation |-> incarnation'[msg.dest]], send_gossip)
                   \/ /\ msg.payload.state = Suspect
                      /\ incarnation' = [incarnation EXCEPT ![msg.dest] = incarnation[msg.dest] + 1]
                      /\ SendAck(msg, [incarnation |-> incarnation'[msg.dest]], send_gossip)
                   \/ /\ msg.payload.incarnation <= incarnation[msg.dest]
                      /\ SendAck(msg, [incarnation |-> incarnation[msg.dest]], send_gossip)
                      /\ UNCHANGED <<incarnation>>
                /\ HandleGossip(msg.dest, msg.source, msg.payload.incarnation, msg.gossip, send_gossip) 
    /\ UNCHANGED <<round, pending_direct_ack, pending_indirect_ack, probe_ctr >>

(************************************************************************) 
(******************** ACTION: ReceiveAck ********************************)
(************************************************************************)

(* Notes
Handles an ack message from a peer
- If the acknowledged message is greater than the incarnation for the member on the destination
node, update the member's state and add an update for gossip.
- Also adds any piggybacked gossip on ack to pending updates.
- Increments this member's round amd untracks the original request - required for fair scheduling
*)
ReceiveAck ==
    /\ sim_complete = 0
    /\ \E msg \in DOMAIN messages :
        /\ msg.type = AckMessage
        /\ messages[msg] >= 1
        /\ msg.on_behalf_of = Nil
        /\ msg.round = round[msg.dest]
        /\ round' = [round EXCEPT ![msg.dest] = @ + 1]
        /\ HandleGossip(msg.dest, 
                        msg.source, 
                        msg.payload.incarnation, 
                        msg.gossip, 
                        <<>>)
        /\ RegisterReceivedDirectAck(msg.dest)
        /\ MessageProcessed(msg)
        /\ UNCHANGED <<incarnation, pending_indirect_ack, probe_ctr>>

(************************************************************************) 
(******************** ACTION: Expire ************************************)
(************************************************************************)

(* Notes
Expires a suspected peer once it has reached the timeout
* 'source' is the node on which to expire the peer
* 'dest' is the peer to expire
If the destination's state is Suspect, change its state to Dead and add a gossip
update to notify peers of the state change.
Set the sim_complete variable to 1 if this action will cause convergence (so we deadlock soon after)
*)
Expire(member, peer) ==
    /\ sim_complete = 0
    /\ member # peer
    /\ peer_states[member][peer].state = Suspect
    /\ round[member] - peer_states[member][peer].round > SuspectTimeout
    /\ UpdateState(member, peer, Dead)
    /\ MaybeEndSim
    /\ UNCHANGED <<incarnation, messages, pending_direct_ack, pending_indirect_ack, probe_ctr, round >>


(************************************************************************) 
(******************** ACTION: DirectProbeFails **************************)
(************************************************************************)

ProbeRequestMessages(member, peers, failed_peer, gossip_to_send) ==
    {
        [type    |-> ProbeRequestMessage,
         source  |-> member,
         dest    |-> peer,
         target  |-> failed_peer,
         payload |-> peer_states[member][peer],
         round   |-> round[member],
         gossip  |-> gossip_to_send] : peer \in peers
    }

EligiblePeerGroups(member) ==
    LET valid_peers == { peer \in Member : IsValidProbeTarget(member, peer) }
    IN IF Cardinality(valid_peers) <= PeerGroupSize THEN { valid_peers }
       ELSE 
            { peer_group \in SUBSET valid_peers :          
                Cardinality(peer_group) = PeerGroupSize }

SendProbeRequests(failed_probe) ==
    LET member      == failed_probe.source
        failed_peer == failed_probe.dest
    IN
        \E peer_group \in EligiblePeerGroups(member) :
           LET gossip_to_send == SelectOutgoingGossip(member, <<>>)
           IN
            /\ SendMessages(ProbeRequestMessages(member, peer_group, failed_peer, gossip_to_send))
            /\ IncrementPiggybackCount(member, gossip_to_send)
            /\ pending_direct_ack' = [pending_direct_ack EXCEPT ![member] = Nil]
            /\ pending_indirect_ack' = [pending_indirect_ack EXCEPT ![member] = failed_peer]

DirectProbeFails ==
    /\ sim_complete = 0
    /\ \E msg \in DOMAIN messages :
        /\ msg.type = ProbeMessage
        /\ messages[msg] <= 0
        /\ msg.round = round[msg.source]
        /\ msg.on_behalf_of = Nil
        /\ pending_direct_ack[msg.source] = msg.dest
        /\ ~\E ack \in DOMAIN messages : 
            /\ ack.type = AckMessage
            /\ ack.dest = msg.source
            /\ ack.round = msg.round
            /\ messages[ack] >= 1
        /\ SendProbeRequests(msg)
        /\ UNCHANGED <<incarnation, probe_ctr, round, sim_complete>>

(************************************************************************) 
(******************** ACTION: ReceiveProbeRequest ***********************)
(************************************************************************)

ReceiveProbeRequest ==
    /\ sim_complete = 0
    /\ \E msg \in DOMAIN messages :
        /\ msg.type = ProbeRequestMessage
        /\ messages[msg] >= 1
        /\ LET gossip_to_send == SelectOutgoingGossip(msg.dest, <<>>)
           IN
            /\ ProcessedOneAndSendAnother(msg,
                           [type         |-> ProbeMessage,
                            source       |-> msg.dest,
                            dest         |-> msg.target,
                            round        |-> msg.round,
                            on_behalf_of |-> msg.source,
                            payload      |-> peer_states[msg.dest][msg.target],
                            gossip       |-> gossip_to_send])
            /\ HandleGossip(msg.dest, msg.source, msg.payload.incarnation, msg.gossip, gossip_to_send)
            /\ UNCHANGED <<incarnation, pending_direct_ack, pending_indirect_ack, probe_ctr, round >>


(************************************************************************) 
(******************** ACTION: ReceiveProbeRequestAck ********************)
(************************************************************************)

ReceiveProbeRequestAck ==
    /\ sim_complete = 0
    /\ \E msg \in DOMAIN messages :
        /\ msg.type = AckMessage
        /\ msg.on_behalf_of # Nil
        /\ messages[msg] >= 1
        /\ HandleGossip(msg.dest, 
                        msg.source, 
                        msg.payload.incarnation, 
                        msg.gossip, 
                        <<>>)
        /\ ProcessedOneAndSendAnother(msg, [msg EXCEPT !.type = ForwardedAckMessage,
                                                       !.dest = msg.on_behalf_of])
        /\ UNCHANGED <<incarnation>>

(************************************************************************) 
(******************** ACTION: ReceiveForwardedAck ***********************)
(************************************************************************)

ReceiveForwardedAck ==
    /\ sim_complete = 0
    /\ \E msg \in DOMAIN messages :
        /\ msg.type = ForwardedAckMessage
        /\ messages[msg] >= 1
        /\ HandleGossip(msg.dest, 
                        msg.source, 
                        msg.payload.incarnation, 
                        msg.gossip, 
                        <<>>)
        /\ IF pending_indirect_ack[msg.dest] # Nil 
           THEN /\ round' = [round EXCEPT ![msg.dest] = @ + 1]
                /\ pending_indirect_ack' = [pending_indirect_ack EXCEPT ![msg.dest] = Nil] 
           ELSE UNCHANGED << round, pending_direct_ack, probe_ctr >>
        /\ MessageProcessed(msg)
        /\ UNCHANGED <<incarnation>>


(************************************************************************) 
(******************** ACTION: ProbeRequestFails *************************)
(************************************************************************)

IndirectProbeChainBroken(member) ==
    LET round_of_chain == round[member]
    IN
        \A msg \in DOMAIN messages :
            IF /\ msg.round = round_of_chain
               /\ \/ /\ msg.type = ProbeRequestMessage 
                     /\ msg.source = member
                  \/ /\ msg.type = ProbeMessage
                     /\ msg.on_behalf_of = member
                  \/ /\ msg.type = AckMessage
                     /\ msg.on_behalf_of = member
                  \/ /\ msg.type = ForwardedAckMessage
                     /\ msg.dest = member
            THEN
                messages[msg] <= 0
            ELSE
                TRUE

ProbeRequestFails ==
    /\ sim_complete = 0
    /\ \E member \in Member :
        /\ pending_indirect_ack[member] # Nil
        /\ IndirectProbeChainBroken(member)
        /\ LET pr == CHOOSE msg \in DOMAIN messages :
                        /\ msg.type = ProbeRequestMessage
                        /\ msg.source = member
                        /\ msg.round = round[member]
           IN
                /\ IF pr.payload.incarnation > 0
                        /\ pr.payload.incarnation = peer_states[pr.source][pr.target].incarnation
                        /\ peer_states[member][pr.target].state = Alive
                   THEN
                        UpdateState(member, pr.target, Suspect)
                   ELSE UNCHANGED << peer_states >>
                /\ pending_indirect_ack' = [pending_indirect_ack EXCEPT ![member] = Nil]
                /\ round' = [round EXCEPT ![member] = @ + 1]
                /\ UNCHANGED <<incarnation, messages, pending_direct_ack, probe_ctr, sim_complete>>

(* 
Next state predicate
Due to a convergence check in the Probe operator, it will
eventually deadlock when converged as we want the simulation 
to stop at that point and print out the statistics
*)
Next ==
    \/ \E member, peer \in Member : 
        \/ SendDirectProbe(member, peer)
        \/ Expire(member, peer)
    \/ ReceiveProbe
    \/ ReceiveAck
    \/ DirectProbeFails
    \/ ReceiveProbeRequest
    \/ ReceiveProbeRequestAck
    \/ ReceiveForwardedAck
    \/ ProbeRequestFails
    \/ EndSim

MemberOrNil ==
    Member \union {Nil}

TypeOK ==
    /\ incarnation \in [Member -> Nat \union {Nil}]
    /\ peer_states \in [Member -> [Member -> [incarnation    : Nat, 
                                              state          : { Alive, Suspect, Dead }, 
                                              round          : Nat, 
                                              disseminations : 0..DisseminationLimit]]]
    /\ round \in [Member -> Nat]
    /\ pending_direct_ack \in [Member -> MemberOrNil]
    /\ pending_indirect_ack \in [Member -> MemberOrNil]
    /\ probe_ctr \in [Member -> [Member -> Nat]]

Inv ==
    IF (~ ENABLED Next) THEN
        sim_complete = 2
    ELSE
        TRUE

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Ensemble ==
    1..20

============================================================================
\* Modification History
\* Last modified Mon Aug 31 04:39:12 PDT 2020 by jack
\* Last modified Thu Oct 18 12:45:40 PDT 2018 by jordanhalterman
\* Created Mon Oct 08 00:36:03 PDT 2018 by jordanhalterman