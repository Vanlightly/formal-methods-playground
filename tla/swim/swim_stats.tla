-------------------------------- MODULE swim_stats --------------------------------

(*
Originally based on the Atomix SWIM TLA+ specification (https://github.com/atomix/atomix-tlaplus/blob/master/SWIM/SWIM.tla) 
but now heavily modified. The original spec was a subset of the SWIM protocol that focused on safety only, and only verifying that
the state a member has on its peer, for a given incarnation can only go from alive to suspect to dead.
  
This specification implements the variants 2 (SWIM+Inf.) and 3 (SWIM+Inf.+Susp.) of the SWIM paper. It can be run in TLC as v2 or v3
via the constants.

Summary of modifications:
- As per the SWIM paper:
    - Indirect probing via probe requests
    - Gossip messages (peer states) are piggybacked on probe, probe request and ack messages.
    - The number of gossiped peer states per probe/probeReq/ack is limited
    - When there are more infective peer states than can fit, those with the fewest disseminations are prioritised.
    - Suspected members are marked as dead after a timeout (number of protocol rounds). This can be deactivated to make it v2.
    - each member randomly picks another member to probe, but with guaranteed bounds 
      (i.e. cannot randomly pick the same member over and over again)

- For simulation/stats
    - The initial state can be configured such that some members start out dead, or ready to join, but
      that state is undetected by the rest of the members. 
      The aim is to measure the number of protocol rounds, and other metrics, in order for the ensemble 
      to converge on this new state. Shortly after reaching convergence, the spec will deadlock. 
      This is by design as it helps simulation by halting when we reach the objective. On deadlocking, 
      any statistical properties being tracked are printed out in a csv format.
      
    - Fair scheduling is modelled to ensure that the probe rate of each member is balanced. Each member 
      is always within 1 protocol round of each other
        
*)

EXTENDS Naturals, FiniteSets, Sequences, TLC, TLCExt, Integers


CONSTANTS Nil,                      \* Empty numeric value
          
          AliveState,               \* Numeric member state 
          SuspectState,             \* Numeric member state
          DeadState,                \* Numeric member state
          UnknownState,             \* Numeric member state
          
          ProbeMessage,             \* Message type: probe
          AckMessage,               \* Message type: ack
          ProbeRequestMessage,      \* Message type: probe request
          ForwardedAckMessage,      \* Message type: indirect ack forwarded
          
          \* CONFIGURABLE PARAMETERS
          Member,                   \* The set of possible members
          PeerGroupSize,            \* The number of peers to send probe requests when a direct probe fails
          SuspectTimeout,           \* The number of protocol rounds before a suspected node is made dead
          DisseminationLimit,       \* The lambda log n value (the maximum number of times a given update can be piggybacked)
          MaxUpdatesPerPiggyBack,   \* The maximum  number of state updates to be included in
                                    \* any given piggybacked gossip message
          MessageLossMode,          \* "none" = no message loss
                                    \* "probabilistic" randomly drops messages, based on LoseEveryNth 
                                    \* "exhaustive" chooses both (model checking mode)     
          LoseEveryNth,             \* Each message has a 1/n chance of being lost. For use in simulation.
          InitialContactMemberCount,\* The number of members that newly added members know of
                                    \* used to bootstrap the new member into the cluster
          MemberLeavesEnabled,      \* TRUE or FALSE as to the MemberLeaves action is enabled
          NewMemberCount,           \* The number of new members the ensemble need to detect
          DeadMemberCount,          \* The number of dead members the ensemble need to detect
          UnjoinedMemberCount,      \* The number of members yet to join
          ForceRunToRound,          \* For use in simulation. When 0, the simulation will stop at convergence
                                    \* When > 0, the simulation will run to this number of rounds
          PrintStatsOnDeadlock      \* For use in simulation. TRUE/FALSE as to whether to print the obtained stats when the simulation ends.

\* Precedence of the different states
ASSUME AliveState > SuspectState /\ SuspectState > DeadState /\ DeadState > UnknownState

ASSUME DeadMemberCount \in Nat
ASSUME InitialContactMemberCount \in Nat
ASSUME SuspectTimeout \in Nat
ASSUME MaxUpdatesPerPiggyBack \in (Nat \ {0})
ASSUME DisseminationLimit \in (Nat \ {0})

ASSUME PrintStatsOnDeadlock \in BOOLEAN

ASSUME MessageLossMode \in {"none", "exhaustive", "probabilistic"}
ASSUME LoseEveryNth \in Nat
ASSUME ForceRunToRound \in Nat
ASSUME MemberLeavesEnabled \in BOOLEAN

ASSUME DeadMemberCount \in Nat
ASSUME NewMemberCount \in Nat
ASSUME UnjoinedMemberCount \in Nat

ASSUME DeadMemberCount < Cardinality(Member)
ASSUME NewMemberCount < Cardinality(Member)
ASSUME UnjoinedMemberCount < Cardinality(Member)

ASSUME DeadMemberCount + NewMemberCount + InitialContactMemberCount <= Cardinality(Member) - UnjoinedMemberCount
            
VARIABLES \* actual state in the protocol
          incarnation,          \* Member incarnation numbers
          peer_states,          \* The known state that each member has on its peers
          round,                \* Each member keeps track of which round of the protocol it is in
          pending_direct_ack,   \* Each member keeps track of members it is pending a direct ack from
          pending_indirect_ack, \* Each member keeps track of members it is pending an idirect ack from
          probe_req_counter,    \* Each member keeps track of the number of probe requests it has sent in any given round
          probe_ctr,            \* Each member keeps track of how many probes it has sent to each peer
                                \* It randomly selects peers, but keeps the number of probes balanced
          \* messaging passing
          messages,             \* a function of all messages       
                    
          \* to end simulation once convergence reached
          sim_complete
          
vars == <<incarnation, peer_states, messages, pending_direct_ack, pending_indirect_ack, probe_req_counter, probe_ctr, round, sim_complete>>

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
    

ResetStats(max_round) ==
    \A r \in 1..max_round : 
        /\ TLCSet(updates_pr_ctr(r), 0)
        /\ TLCSet(eff_updates_pr_ctr(r), 0)
        /\ TLCSet(suspect_ctr(r), 0)
        /\ TLCSet(dead_ctr(r), 0)
        /\ TLCSet(suspect_states_ctr(r), 0)
        /\ TLCSet(dead_states_ctr(r), 0)

UnknownStateRecord ==
    [incarnation    |-> 0, 
     state          |-> UnknownState, 
     round          |-> 0, 
     disseminations |-> DisseminationLimit]
     
KnownAliveStateRecord ==
    [incarnation    |-> 1, 
     state          |-> AliveState, 
     round          |-> 1, 
     disseminations |-> DisseminationLimit]

\* We can configure the initial state to start with a certain number of undetected states
\* such as undetected dead members or undetected newly joined members.
\* We can also configure some members to not have joined yet
\* The rest will be started, and already know about each other and their peer state they have not being infective.
\* This all allows us to test various scenarios easily
Init ==
    LET undetected_dead == CHOOSE s \in SUBSET Member : Cardinality(s) = DeadMemberCount
    IN LET undetected_joined == CHOOSE s \in SUBSET (Member \ undetected_dead) : Cardinality(s) = NewMemberCount
       IN LET contact_members == CHOOSE s \in SUBSET (Member \ (undetected_dead \union undetected_joined)) : Cardinality(s) = InitialContactMemberCount
          IN LET unjoined == CHOOSE s \in SUBSET (Member \ (undetected_dead \union undetected_joined \union contact_members)) : Cardinality(s) = UnjoinedMemberCount
             IN
                /\ incarnation = [m \in Member |-> IF m \in undetected_dead THEN Nil ELSE 1]
                /\ peer_states = [m \in Member |-> [m1 \in Member |-> 
                                                        CASE m \in undetected_joined -> IF m1 \in contact_members
                                                                                        THEN KnownAliveStateRecord
                                                                                        ELSE UnknownStateRecord
                                                          [] m \in undetected_dead   -> UnknownStateRecord
                                                          [] m \in unjoined          -> UnknownStateRecord
                                                          [] OTHER                   -> IF m1 \in undetected_joined \/ m1 \in unjoined
                                                                                        THEN UnknownStateRecord
                                                                                        ELSE KnownAliveStateRecord]]
                /\ round = [m \in Member |-> 1]
                /\ messages = [msg \in {} |-> 0]
                /\ pending_direct_ack = [m \in Member |-> Nil]
                /\ pending_indirect_ack = [m \in Member |-> Nil]
                /\ probe_req_counter = [m \in Member |-> 0]
                /\ probe_ctr = [m \in Member |-> [m1 \in Member |-> 0]]
                /\ sim_complete = 0
                /\ ResetStats(1000)

(*****************************************************)
(*************** Messaging passing *******************)
(*****************************************************)

\* if the dest is dead, it never gets delivered
\* or if the dest thinks the source is dead, it ignores it (SWIM makes no provision for dead members playing an active role)
\* else if we have turned on message loss, then there are two modes:
\*  'probabilistic' is a random chance of losing the message
\*  'exhaustive' is for model checking where both options are explored
GetDeliveredCount(msg) ==
    IF incarnation[msg.dest] = Nil \/ peer_states[msg.dest][msg.source].state = DeadState 
    THEN {0}
    ELSE
        CASE MessageLossMode = "probabilistic" -> IF RandomElement(1..LoseEveryNth) = LoseEveryNth THEN {0} ELSE {1}
          [] MessageLossMode = "exhaustive"    -> {0,1}
          [] OTHER                             -> {1}

\* Send a message only if the message has not already been sent
SendMessage(msg) ==
    /\ msg \notin DOMAIN messages
    /\ \E delivered_count \in GetDeliveredCount(msg) :
        messages' = messages @@ (msg :> delivered_count)

\* Mark one message as processed and send a new message   
ProcessedOneAndSendAnother(received_msg, send_msg) ==
    /\ received_msg \in DOMAIN messages
    /\ send_msg \notin DOMAIN messages
    /\ messages[received_msg] >= 1
    /\ \E delivered_count \in GetDeliveredCount(send_msg) :
        messages' = [messages EXCEPT ![received_msg] = @-1] @@ (send_msg :> delivered_count)

\* Mark one message as processed   
MessageProcessed(msg) ==
    /\ msg \in DOMAIN messages
    /\ messages[msg] >= 1
    /\ messages' = [messages EXCEPT ![msg] = @ - 1]
    
\* When a member sends a probe to a peer, it needs to keep track of that
\* and additionally increment its probe_ctr (required for balanced probing)
\* and reset its probe request counter for this new protocol round
RegisterPendingDirectAck(member, peer) ==
    /\ pending_direct_ack' = [pending_direct_ack EXCEPT ![member] = peer]
    /\ probe_ctr' = [probe_ctr EXCEPT ![member][peer] = @ + 1]
    /\ probe_req_counter' = [probe_req_counter EXCEPT ![member] = 0]

RegisterReceivedDirectAck(member) ==
    pending_direct_ack' = [pending_direct_ack EXCEPT ![member] = Nil]

(*****************************************************)
(*************** Helper operators ********************)
(*****************************************************)

\* What is the highest protocol round of the ensemble
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
    IF incarnation[member] = Nil THEN DeadState ELSE AliveState

\* TRUE when:
\* for each member, it's live peers all agree on the same thing, specifically that:
\*    - either they all see the true state
\*    - or they all (falsely) think that it is dead
\* SWIM does not prevent false positives (just mitigates them)
\* and makes no provision for coming back from the dead - once you a member thinks you're dead 
\* they cannot be convinced otherwise.
IsConverged(inc, pstates) ==
    \A member \in Member :
        \A peer \in Member :
            \/ inc[peer] = Nil
            \/ member = peer
            \/ /\ member # peer
               /\ \/ pstates[peer][member].state = RealStateOfMember(member)
                  \/ pstates[peer][member].state = DeadState                      


WillBeConverged ==
    IsConverged(incarnation, peer_states')

\* Returns TRUE or FALSE as to whether an individual peer state is new for this member
\* It is new only if:
\* - its incarnation number is > than the known incarnation number of the target member
\* - its incarnation number equals the known incarnation number of the target member but its state has higher precedence
IsNewInformation(member, peer, peer_state) ==
    \/ peer_state.incarnation > peer_states[member][peer].incarnation
    \/ /\ peer_state.incarnation = peer_states[member][peer].incarnation
       /\ peer_state.state < peer_states[member][peer].state

(************************************************************************) 
(******************** RECORD STATISTICS *********************************)
(************************************************************************)

(* Notes

Records various metrics using TLCSet and TLCGet. Some metrics are already available in the variables
such as round and messages.

At the end of a simulation, the statistics are gathered from the counters and variables and printed
in CSV format.
*)

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
                /\ TLCSet(suspect_ctr(r), NextStateMemberCount(SuspectState))
                /\ TLCSet(dead_ctr(r), NextStateMemberCount(DeadState))
                /\ TLCSet(suspect_states_ctr(r), NextStateStateCount(SuspectState))
                /\ TLCSet(dead_states_ctr(r), NextStateStateCount(DeadState))
        ELSE TRUE

RecordIncomingGossipStats(member, gossip_source, incoming_peer_states, end_of_round) ==
    LET updates_ctr_id     == updates_pr_ctr(round[gossip_source])
        eff_updates_ctr_id == eff_updates_pr_ctr(round[gossip_source])
    IN 
       \* gossip counts
       /\ TLCSet(updates_ctr_id, TLCGet(updates_ctr_id) + Cardinality(DOMAIN incoming_peer_states))
       \* effective gossip counts
       /\ LET effective_count == Cardinality({ m \in DOMAIN incoming_peer_states :
                                                    IsNewInformation(member, m, incoming_peer_states[m])}) 
          IN TLCSet(eff_updates_ctr_id, TLCGet(eff_updates_ctr_id) + effective_count)
       \* suspect and dead counts
       /\ IF end_of_round THEN MayBeRecordMemberCounts ELSE TRUE         

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
            \A member \in Member : 
                IF incarnation[member] # Nil
                THEN PrintT("message_load_in_round" \o cfg_str \o ToString(r) \o "," \o ToString(member) \o "," \o ToString(MessageLoad(r, member)))
                ELSE TRUE
        /\ \A r \in 1..max_stats_round : PrintT("updates_in_round" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(updates_pr_ctr(r))))
        /\ \A r \in 1..max_stats_round : PrintT("eff_updates_in_round" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(eff_updates_pr_ctr(r))))
        /\ \A r \in 1..max_stats_round : 
            IF r = max_stats_round 
            THEN PrintT("suspected_members_count" \o cfg_str \o ToString(r) \o "," \o ToString(CurrentMemberCount(SuspectState)))
            ELSE PrintT("suspected_members_count" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(suspect_ctr(r))))
        /\ \A r \in 1..max_stats_round :
            IF r = max_stats_round 
            THEN PrintT("dead_members_count" \o cfg_str \o ToString(r) \o "," \o ToString(CurrentMemberCount(DeadState)))
            ELSE PrintT("dead_members_count" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(dead_ctr(r))))
        /\ \A r \in 1..max_stats_round : 
            IF r = max_stats_round 
            THEN PrintT("suspect_states_count" \o cfg_str \o ToString(r) \o "," \o ToString(CurrentStateCount(SuspectState)))
            ELSE PrintT("suspect_states_count" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(suspect_states_ctr(r))))
        /\ \A r \in 1..max_stats_round :
            IF r = max_stats_round 
            THEN PrintT("dead_states_count" \o cfg_str \o ToString(r) \o "," \o ToString(CurrentStateCount(DeadState)))
            ELSE PrintT("dead_states_count" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(dead_states_ctr(r))))
        /\ PrintT("converged")
        /\ ResetStats(max_stats_round)
    
MaybeEndSim ==
    \/ /\ ForceRunToRound > 0
       /\ IF \A member \in Member : round[member] <= ForceRunToRound 
          THEN UNCHANGED sim_complete
          ELSE sim_complete' = 1
    \/ /\ ForceRunToRound <= 0
       /\ IF WillBeConverged THEN sim_complete' = 1 ELSE UNCHANGED sim_complete    
    
EndSim ==
    /\ \/ sim_complete = 1
       \/ sim_complete = 0 /\ IsConverged(incarnation, peer_states)
    /\ IF PrintStatsOnDeadlock = TRUE THEN PrintStats ELSE TRUE
    /\ sim_complete' = 2
    /\ UNCHANGED <<incarnation, peer_states, messages, pending_direct_ack, pending_indirect_ack, probe_req_counter, probe_ctr, round>>

RecordGossipStats(member, gossip_source, incoming_states, end_of_round) ==
    TLCDefer(RecordIncomingGossipStats(member, gossip_source, incoming_states, end_of_round))
    
RecordStateStats ==
    TLCDefer(MayBeRecordMemberCounts)

(************************************************************************) 
(******************** SELECTING OUTGOING GOSSIP *************************)
(************************************************************************)

(* NOTES
Peer states are selected for piggybacking on probes, probe requests and acks based on:
1. The maximum number of times a peer state can be disseminated (lambda log n in the paper
   but in this spec the constant DisseminationLimit. When under this limit, the state is
   still infective.
2. The maximum number of peer states that can be piggybacked.
   In this spec the constant MaxUpdatesPerPiggyBack.
3. In the case that all valid peer states do not fit, prioritise those that have been 
   disseminated fewer times.
*)

\* For the given member, returns the peers it has state on that is still infective
PeersUnderDisseminationsLimit(member, peer, new_peer_states) ==
    { m1 \in Member : 
        /\ m1 # member
        /\ m1 # peer
        /\ new_peer_states[m1].disseminations < DisseminationLimit
    }
    
\* Choose the peer states to gossip based on the MaxUpdatesPerGossip and when there is more
\* gossip than can be accomodated in a single message, choose the peer states
\* in order of fewest disseminations first
Prioritise(candidate_peers, limit, new_peer_states) ==
    CHOOSE peer_subset \in SUBSET candidate_peers :
        /\ Cardinality(peer_subset) = limit
        /\ \A peer1 \in peer_subset :
            \A peer2 \in candidate_peers \ peer_subset :
                new_peer_states[peer1].disseminations <= new_peer_states[peer2].disseminations

ShareableState(peer_state) ==
    [incarnation |-> peer_state.incarnation,
     state       |-> peer_state.state]

\* Select outgoing gossip based on multiple factors, including whether incoming gossip
\* is newer than existing information
SelectOutgoingGossip(member, dest_peer, merged_peer_states) ==
    LET candidate_peers == PeersUnderDisseminationsLimit(member, dest_peer, merged_peer_states)
    IN
        IF Cardinality(candidate_peers) <= MaxUpdatesPerPiggyBack 
        THEN [peer \in candidate_peers |-> ShareableState(merged_peer_states[peer])]
        ELSE LET peers == Prioritise(candidate_peers, MaxUpdatesPerPiggyBack, merged_peer_states)
             IN [peer \in peers |-> ShareableState(merged_peer_states[peer])]
             
\* Increment the dissemination counter of the peer states that have been gossiped             
UpdatePeerStates(member, updated_peer_states, sent_peer_states) ==
    /\ peer_states' = [peer_states EXCEPT ![member] =  
                        [peer \in Member |-> IF peer \in DOMAIN sent_peer_states
                                             THEN [updated_peer_states[peer] EXCEPT !.disseminations = @ + 1]
                                             ELSE updated_peer_states[peer]]]         
    /\ MaybeEndSim

(************************************************************************) 
(******************** INCOMING GOSSIP ***********************************)
(************************************************************************)

(* NOTES
Gossip can come in on probes, probe requests and acks. Any incoming gossip is 
merged with existing peer state, with stale peer states being replaced by any newer gossiped state. 
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
     state          |-> AliveState, 
     disseminations |-> 0, 
     round          |-> member_round]

(*
\* updates the state of a member's peers based on incoming and outgoing gossip
\* If member's incarnation for the gossip source is stale then update it
\* Increment dissemination counters of outgoing gossip
\* Replace any peer state that is stale
MergeGossip(member, gossip_source, source_incarnation, incoming_updates, sent_updates) ==
    [peer \in Member |-> 
        IF peer = member 
        THEN peer_states[member][member] \* it holds no data about itself 
        ELSE 
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
       /\ MaybeEndSim*)

MergeGossipWithCurrentState(member, gossip_source, source_incarnation, incoming_peer_states) ==
    [peer \in Member |-> 
        IF peer = member 
        THEN peer_states[member][member] \* it holds no data about itself 
        ELSE 
            IF peer = gossip_source
            THEN IF peer_states[member][gossip_source].incarnation < source_incarnation
                 THEN NewAliveMemberRecord(source_incarnation, round[member])
                 ELSE peer_states[member][gossip_source]
            ELSE
                IF peer \in DOMAIN incoming_peer_states
                THEN IF IsNewInformation(member, peer, incoming_peer_states[peer])
                     THEN ResetCountersOfRecord(incoming_peer_states[peer], round[member])
                     ELSE peer_states[member][peer]
                ELSE peer_states[member][peer]]
                    

\* Updates the state and counters of a peer of the given member
\* This is not called when an incarnation has changed, only a state change 
\* like Alive->Suspect or Suspect->Dead
UpdateState(member, peer, state) ==
    peer_states' = [peer_states EXCEPT ![member][peer] =
                        [@ EXCEPT !.state          = state,
                                  !.disseminations = 0,
                                  !.round          = round[member]]]

MayBeIncrementIncarnation(msg) ==
    IF msg.dest_state.state = SuspectState /\ msg.dest_state.incarnation = incarnation[msg.dest]
    THEN incarnation[msg.dest] + 1 
    ELSE incarnation[msg.dest]

MayBeUpdateIncarnation(member, new_incarnation) ==
    IF incarnation[member] < new_incarnation
    THEN incarnation' = [incarnation EXCEPT ![member] = new_incarnation]
    ELSE UNCHANGED incarnation

(************************************************************************) 
(******************** ACTION: SendDirectProbe****************************)
(************************************************************************)

(* Notes
Triggers a probe request from a member to a peer and is the beginning of a new protocol round
for that member.

A new protocol round can only commence when the prior one is complete. That can occur when:
- there are no pending expirations (suspect to dead) to apply
- there are no pending acks to direct probes
- there are no pending indirect acks via probe requests that have a chance of completing
  (message loss and dead members can cause there to be no reply from any probe requests sent out). 
*)

\* The current round is complete only if:
\* - The member has no pending expirations
\* - The member is not waiting on a direct ack
\* - The member is not waiting on an indirect ack
CurrentRoundComplete(member) ==
    /\ ~\E peer \in Member :
        /\ peer_states[member][peer].state = SuspectState
        /\ round[member] - peer_states[member][peer].round > SuspectTimeout
    /\ pending_indirect_ack[member] = Nil   
    /\ pending_direct_ack[member] = Nil     

\* The member knows of the peer's existence and it is not pending expiry
IsValidProbeTarget(member, peer) ==
    /\ member # peer
    /\ \/ peer_states[member][peer].state = AliveState       
       \/ /\ peer_states[member][peer].state = SuspectState
          /\ round[member] - peer_states[member][peer].round <= SuspectTimeout

\* Peers picked in a random but time bounded manner
IsValidRandomPick(member, peer) ==
    \A m \in Member : 
        IF IsValidProbeTarget(member, m) 
        THEN probe_ctr[member][peer] <= probe_ctr[member][m]
        ELSE TRUE

\* This is necessary for statistics simulation to ensure that all members are
\* sending out probes at the same rate and stay within one round of each other
IsFairlyScheduled(member, peer) ==
    \A m1 \in Member : 
        \/ incarnation[m1] = Nil
        \/ /\ incarnation[m1] # Nil
           /\ round[member] <= round[m1]

\* The sending of a direct probe is the beginning of a new protocol period.
SendDirectProbe(member, peer) ==
    /\ member # peer
    /\ sim_complete = 0
    /\ incarnation[member] # Nil            \* The member is alive
    /\ CurrentRoundComplete(member)         \* This member can initiate its next protocol round
    /\ IsValidProbeTarget(member, peer)     \* The peer is valid (the member think it's not dead for example)
    /\ IsValidRandomPick(member, peer)      \* Peers are picked randomly, but in a balanced way
    /\ IsFairlyScheduled(member, peer)      \* For simulation - we keep all members within 1 round of each other
    /\ LET gossip_to_send == SelectOutgoingGossip(member, peer, peer_states[member])
       IN
        /\ SendMessage([type         |-> ProbeMessage,
                        source       |-> member,
                        dest         |-> peer,
                        round        |-> round[member],
                        on_behalf_of |-> Nil,
                        dest_state   |-> ShareableState(peer_states[member][peer]),
                        source_inc   |-> incarnation[member],
                        gossip       |-> gossip_to_send])
        /\ UpdatePeerStates(member, peer_states[member], gossip_to_send)
        /\ RegisterPendingDirectAck(member, peer)
        /\ UNCHANGED <<incarnation, pending_indirect_ack, round >>


        
(************************************************************************) 
(******************** ACTION: ReceiveProbe ******************************)
(************************************************************************)

(* Notes
Handles a probe message from a peer, either a direct or an indirect probe.
If the received incarnation is greater than the destination's incarnation number, update the
destination's incarnation number to 1 plus the received number. This can happen after a node
leaves and rejoins the cluster. If the destination is suspected by the source, increment the
destination's incarnation and respond with the updated incarnation, this will tell the source
that the destination is in fact alive. 
If the destination's incarnation is greater than the source's incarnation, just send an ack.

Adds pending gossip (that will fit) to the ack (piggybacking).
Adds any incoming gossip that is new, to the peer state to be gossiped later.
*)

\* Send an ack and piggyback gossip if any to send
SendAck(probe, source_incarnation, merged_peer_state, piggyback_gossip) ==
    ProcessedOneAndSendAnother(probe, 
                       [type         |-> AckMessage,
                        source       |-> probe.dest,
                        dest         |-> probe.source,
                        round        |-> probe.round,
                        on_behalf_of |-> probe.on_behalf_of,
                        dest_state   |-> ShareableState(merged_peer_state[probe.source]),
                        source_inc   |-> source_incarnation,
                        gossip       |-> piggyback_gossip])
 
ReceiveProbe ==
    /\ sim_complete = 0
    /\ \E msg \in DOMAIN messages :
        /\ msg.type = ProbeMessage
        /\ messages[msg] >= 1
        /\ incarnation[msg.dest] # Nil
        /\ LET merged_peer_state == MergeGossipWithCurrentState(msg.dest, 
                                                              msg.source, 
                                                              msg.source_inc, 
                                                              msg.gossip)
               new_incarnation   == MayBeIncrementIncarnation(msg)
           IN LET send_gossip == SelectOutgoingGossip(msg.dest, msg.source, merged_peer_state)
              IN
               /\ MayBeUpdateIncarnation(msg.dest, new_incarnation)
               /\ SendAck(msg, new_incarnation, merged_peer_state, send_gossip)
               /\ UpdatePeerStates(msg.dest, merged_peer_state, send_gossip)
               /\ RecordGossipStats(msg.dest, msg.source, msg.gossip, FALSE)
    /\ UNCHANGED <<round, pending_direct_ack, pending_indirect_ack, probe_req_counter, probe_ctr >>

(************************************************************************) 
(******************** ACTION: ReceiveAck ********************************)
(************************************************************************)

(* Notes
Handles an ack message (from a direct probe only) from a peer.
Increments this member's round as this is the end of a protocol round 
*)
ReceiveAck ==
    /\ sim_complete = 0
    /\ \E msg \in DOMAIN messages :
        /\ msg.type = AckMessage
        /\ messages[msg] >= 1
        /\ msg.on_behalf_of = Nil
        /\ msg.round = round[msg.dest]
        /\ LET merged_peer_state == MergeGossipWithCurrentState(msg.dest, 
                                                                msg.source, 
                                                                msg.source_inc, 
                                                                msg.gossip)
               new_incarnation   == MayBeIncrementIncarnation(msg)
           IN
            /\ MayBeUpdateIncarnation(msg.dest, new_incarnation)
            /\ UpdatePeerStates(msg.dest, merged_peer_state, <<>>)
            /\ RegisterReceivedDirectAck(msg.dest)
            /\ MessageProcessed(msg)
            /\ round' = [round EXCEPT ![msg.dest] = @ + 1]
            /\ RecordGossipStats(msg.dest, msg.source, msg.gossip, TRUE)
            /\ UNCHANGED << pending_indirect_ack, probe_req_counter, probe_ctr>>

(************************************************************************) 
(******************** ACTION: Expire ************************************)
(************************************************************************)

(* Notes
Expires a suspected peer once it has reached the timeout.
We can simulation variant 2 by setting the timeout to 0 which means
immediate expiry.
*)
Expire(member, peer) ==
    /\ sim_complete = 0
    /\ member # peer
    /\ peer_states[member][peer].state = SuspectState
    /\ round[member] - peer_states[member][peer].round > SuspectTimeout
    /\ UpdateState(member, peer, DeadState)
    /\ MaybeEndSim
    /\ UNCHANGED <<incarnation, messages, pending_direct_ack, pending_indirect_ack, probe_req_counter, probe_ctr, round >>


(************************************************************************) 
(******************** ACTION: SendProbeRequest **************************)
(************************************************************************)

(* Notes

Enabled when a direct probe has failed, there are still probe requests to
be sent out and valid peers to receive them. 

The number of probe requests is bounded by the minimum of:
- The PeerGroupSize value, this is the number of peers a member will send probe requests to
- The number of available peers to send to
*)

NewProbeRequest(member, peer, failed_peer, gossip_to_send) ==
    [type       |-> ProbeRequestMessage,
     source     |-> member,
     dest       |-> peer,
     target     |-> failed_peer,
     dest_state |-> ShareableState(peer_states[member][peer]),
     source_inc |-> incarnation[member],
     round      |-> round[member],
     gossip     |-> gossip_to_send]

AlreadySentProbeRequests(failed_probe) ==
    {
        msg \in DOMAIN messages :
            /\ msg.type = ProbeRequestMessage
            /\ msg.round = failed_probe.round
            /\ msg.source = failed_probe.source
    }

EligibleProbeRequestPeer(member, peer, failed_peer, prev_pr) ==
    /\ peer # member
    /\ peer # failed_peer
    /\ IsValidProbeTarget(member, peer)
    /\ ~\E pr \in prev_pr : pr.dest = peer

SendOneProbeRequest(failed_probe) == 
    LET member      == failed_probe.source
        failed_peer == failed_probe.dest
        prev_pr     == AlreadySentProbeRequests(failed_probe)
    IN
        \E peer \in Member : 
            /\ EligibleProbeRequestPeer(member, peer, failed_peer, prev_pr)
            /\ LET gossip_to_send == SelectOutgoingGossip(member, peer, peer_states[member])
               IN
                    /\ SendMessage(NewProbeRequest(member, peer, failed_peer, gossip_to_send))
                    /\ UpdatePeerStates(member, peer_states[member], gossip_to_send)
                    /\ pending_indirect_ack' = [pending_indirect_ack EXCEPT ![member] = failed_peer]
                    /\ pending_direct_ack' = [pending_direct_ack EXCEPT ![member] = Nil]
                    /\ probe_req_counter' = [probe_req_counter EXCEPT ![member] = @ + 1]

DirectProbeFailed(msg) ==
    /\ msg.type = ProbeMessage
    /\ messages[msg] <= 0
    /\ msg.round = round[msg.source]
    /\ msg.on_behalf_of = Nil
    /\ probe_req_counter[msg.source] < PeerGroupSize
    /\ ~\E ack \in DOMAIN messages : 
        /\ ack.type = AckMessage
        /\ ack.dest = msg.source
        /\ ack.round = msg.round
        /\ messages[ack] >= 1
        
SendProbeRequest ==
    /\ sim_complete = 0
    /\ \E msg \in DOMAIN messages :
        /\ DirectProbeFailed(msg)
        /\ SendOneProbeRequest(msg)
        /\ UNCHANGED <<incarnation, probe_ctr, round>>

(************************************************************************) 
(******************** ACTION: NoPeersForProbeRequest ********************)
(************************************************************************)

(* Notes
This is enabled when we haven't reached the PeerGroupSize limit on the number
of probe requests sent, because there are no more valid peers left to send to.
*)

NoEligiblePeersForProbeRequest(failed_probe) == 
    LET member      == failed_probe.source
        failed_peer == failed_probe.dest
        prev_pr     == AlreadySentProbeRequests(failed_probe)
    IN
        ~\E peer \in Member : 
            EligibleProbeRequestPeer(member, peer, failed_peer, prev_pr)

NoPeersForProbeRequest ==
    /\ sim_complete = 0
    /\ \E msg \in DOMAIN messages :
        /\ DirectProbeFailed(msg)
        /\ NoEligiblePeersForProbeRequest(msg)
        \* if there are no peers for sending out a probe request, and we haven't sent
        \* any previously, then this is the end of this round for this member
        /\ IF peer_states[msg.source][msg.dest].state = AliveState
           THEN UpdateState(msg.source, msg.dest, SuspectState)
           ELSE UNCHANGED peer_states
        /\ IF pending_indirect_ack[msg.source] = Nil
           THEN /\ round' = [round EXCEPT ![msg.source] = @ + 1]
                /\ RecordStateStats
           ELSE UNCHANGED round
        /\ pending_direct_ack' = [pending_direct_ack EXCEPT ![msg.source] = Nil]
        /\ probe_req_counter' = [probe_req_counter EXCEPT ![msg.source] = PeerGroupSize]
        /\ UNCHANGED <<incarnation, messages, probe_ctr, pending_indirect_ack, sim_complete>>
    

(************************************************************************) 
(******************** ACTION: ReceiveProbeRequest ***********************)
(************************************************************************)

(* Notes
Receives a probe request and then sends a probe to the target peer.
*)

ReceiveProbeRequest ==
    /\ sim_complete = 0
    /\ \E msg \in DOMAIN messages :
        /\ msg.type = ProbeRequestMessage
        /\ messages[msg] >= 1
        /\ LET merged_peer_state == MergeGossipWithCurrentState(msg.dest, 
                                                                msg.source, 
                                                                msg.source_inc, 
                                                                msg.gossip)
               new_incarnation   == MayBeIncrementIncarnation(msg)
           IN LET gossip_to_send == SelectOutgoingGossip(msg.dest, msg.target, merged_peer_state)
              IN
                /\ MayBeUpdateIncarnation(msg.dest, new_incarnation)
                /\ ProcessedOneAndSendAnother(msg,
                               [type         |-> ProbeMessage,
                                source       |-> msg.dest,
                                dest         |-> msg.target,
                                round        |-> msg.round,
                                on_behalf_of |-> msg.source,
                                dest_state   |-> ShareableState(merged_peer_state[msg.target]),
                                source_inc   |-> new_incarnation,
                                gossip       |-> gossip_to_send])
                /\ UpdatePeerStates(msg.dest, merged_peer_state, gossip_to_send)
                /\ RecordGossipStats(msg.dest, msg.source, msg.gossip, FALSE)
    /\ UNCHANGED << pending_direct_ack, pending_indirect_ack, probe_req_counter, probe_ctr, round >>


(************************************************************************) 
(******************** ACTION: ReceiveProbeRequestAck ********************)
(************************************************************************)

(*
This is only enabled when the target of the original direct probe is in fact
alive. If the target really were dead, it would not respond to the indirect probe.

The ack from the target peer is forwarded back to the member that sent the probe
request.
*)

ForwardedAck(msg, merged_peer_state, gossip_to_send) ==
    [type       |-> ForwardedAckMessage,
     source     |-> msg.dest,
     dest       |-> msg.on_behalf_of,
     target     |-> msg.source,
     dest_state |-> ShareableState(merged_peer_state[msg.on_behalf_of]),
     source_inc |-> incarnation[msg.dest],
     round      |-> round[msg.dest],
     gossip     |-> gossip_to_send]

ReceiveProbeRequestAck ==
    /\ sim_complete = 0
    /\ \E msg \in DOMAIN messages :
        /\ msg.type = AckMessage
        /\ msg.on_behalf_of # Nil
        /\ messages[msg] >= 1
        /\ LET merged_peer_state == MergeGossipWithCurrentState(msg.dest, 
                                                                msg.source, 
                                                                msg.source_inc, 
                                                                msg.gossip)
               new_incarnation   == MayBeIncrementIncarnation(msg)
           IN LET send_gossip == SelectOutgoingGossip(msg.dest, msg.on_behalf_of, merged_peer_state)
              IN
                /\ MayBeUpdateIncarnation(msg.dest, new_incarnation)
                /\ UpdatePeerStates(msg.dest, merged_peer_state, send_gossip)
                /\ RecordGossipStats(msg.dest, msg.source, msg.gossip, FALSE)
                /\ ProcessedOneAndSendAnother(msg, ForwardedAck(msg, merged_peer_state, send_gossip))
                /\ UNCHANGED << pending_direct_ack, pending_indirect_ack, probe_req_counter, probe_ctr, round>>

(************************************************************************) 
(******************** ACTION: ReceiveForwardedAck ***********************)
(************************************************************************)

(* Notes
This member earlier sent out a direct probe, which failed (not responded to) and
so had sent out up to PeerGroupSize probe requests. If the original target peer
is in fact alive, then the member may receive multiple forwarded acks. On the
first such message that is received, it untracks the target as pending an indirect ack
and increments its own round as this is the end of a protocol round for this member.
*)

ReceiveForwardedAck ==
    /\ sim_complete = 0
    /\ \E msg \in DOMAIN messages :
        /\ msg.type = ForwardedAckMessage
        /\ messages[msg] >= 1
        /\ LET merged_peer_state == MergeGossipWithCurrentState(msg.dest, 
                                                                msg.source, 
                                                                msg.source_inc, 
                                                                msg.gossip)
               new_incarnation   == MayBeIncrementIncarnation(msg)
           IN
            /\ MayBeUpdateIncarnation(msg.dest, new_incarnation)
            /\ UpdatePeerStates(msg.dest, merged_peer_state, <<>>)
            /\ IF pending_indirect_ack[msg.dest] # Nil 
               THEN /\ round' = [round EXCEPT ![msg.dest] = @ + 1]
                    /\ pending_indirect_ack' = [pending_indirect_ack EXCEPT ![msg.dest] = Nil]
                    /\ RecordGossipStats(msg.dest, msg.source, msg.gossip, TRUE) 
               ELSE /\ RecordGossipStats(msg.dest, msg.source, msg.gossip, FALSE)
                    /\ UNCHANGED << round, pending_indirect_ack >>
            /\ MessageProcessed(msg)
            /\ UNCHANGED << pending_direct_ack, probe_req_counter, probe_ctr>>


(************************************************************************) 
(******************** ACTION: ProbeRequestFails *************************)
(************************************************************************)

(* Notes
This is enabled when the chain of up to PeerGroupSize probe requests is broken,
either due to the target peer really being dead, or message loss somewhere.

This is the end of a protocol period of this member, so the round for this member 
is incremented.
*)

IndirectProbeChainBroken(member) ==
    LET round_of_chain == round[member]
    IN
        \E msg \in DOMAIN messages :
           /\ msg.round = round_of_chain
           /\ \/ /\ msg.type = ProbeRequestMessage 
                 /\ msg.source = member
              \/ /\ msg.type = ProbeMessage
                 /\ msg.on_behalf_of = member
              \/ /\ msg.type = AckMessage
                 /\ msg.on_behalf_of = member
              \/ /\ msg.type = ForwardedAckMessage
                 /\ msg.dest = member
           /\ messages[msg] <= 0

NoResponseToProbeRequests ==
    /\ sim_complete = 0
    /\ \E member \in Member :
        /\ pending_indirect_ack[member] # Nil
        /\ IndirectProbeChainBroken(member)
        /\ LET pr == CHOOSE msg \in DOMAIN messages :
                        /\ msg.type = ProbeRequestMessage
                        /\ msg.source = member
                        /\ msg.round = round[member]
           IN
                /\ IF peer_states[member][pr.target].state = AliveState
                   THEN UpdateState(member, pr.target, SuspectState)
                   ELSE UNCHANGED << peer_states >>
                /\ pending_indirect_ack' = [pending_indirect_ack EXCEPT ![member] = Nil]
                /\ round' = [round EXCEPT ![member] = @ + 1]
                /\ RecordStateStats
                /\ UNCHANGED <<incarnation, messages, pending_direct_ack, probe_req_counter, probe_ctr, sim_complete>>

(************************************************************************) 
(******************** ACTION: MemberJoins *******************************)
(************************************************************************)

(* Notes
A member that joins does not have a Nil incarnation prior to joining. A
member that is yet to join is alive but knows of no other peers.
Joining is the act of informing it of the existence of InitialContactMemberCount peers
that it can start probing.
*)


MemberJoins ==
    \E member \in Member :
        /\ incarnation[member] # Nil
        /\ \A m \in Member : \/ member = m
                             \/ peer_states[member][m].state = UnknownState
        /\ \E contact_peers \in SUBSET Member : 
            /\ \A p \in contact_peers : incarnation[p] # Nil
            /\ Cardinality(contact_peers) = InitialContactMemberCount
            /\ peer_states' = [peer_states EXCEPT ![member] =
                                    [m \in Member |-> IF m \in contact_peers
                                                      THEN KnownAliveStateRecord
                                                      ELSE UnknownStateRecord]]
            /\ UNCHANGED <<incarnation, messages, pending_direct_ack, pending_indirect_ack, probe_req_counter, probe_ctr, round, sim_complete>>


(************************************************************************) 
(******************** ACTION: MemberLeaves *******************************)
(************************************************************************)

(* Notes
Only enabled if the constant AllowMembersToLeave is set to TRUE.
Simply changes its incarnation to Nil which represents a dead member.
Once left, a member cannot rejoin. SWIM makes no provision for rejoining members,
it would need to join with a different identifier which is not modelled in this spec.
There must be at least two live members for a member to leave, we do not model all members leaving.
Any messages sent to the leaving member, but not processed are lost.
*)
MemberLeaves ==
    /\ MemberLeavesEnabled
    /\ \E m1, m2 \in Member :
        /\ m1 # m2
        /\ incarnation[m1] # Nil
        /\ incarnation[m2] # Nil
        /\ incarnation' = [incarnation EXCEPT ![m1] = Nil]
        /\ messages' = [msg \in DOMAIN messages |-> IF msg.dest = m1 THEN 0 ELSE messages[msg]]
        /\ UNCHANGED <<peer_states, pending_direct_ack, pending_indirect_ack, probe_req_counter, probe_ctr, round, sim_complete>>


(************************************************************************) 
(******************** Next state and spec *******************************)
(************************************************************************)

Next ==
    \/ \E member, peer \in Member : 
        \/ SendDirectProbe(member, peer)
        \/ Expire(member, peer)
    \/ ReceiveProbe
    \/ ReceiveAck
    \/ SendProbeRequest
    \/ NoPeersForProbeRequest
    \/ ReceiveProbeRequest
    \/ ReceiveProbeRequestAck
    \/ ReceiveForwardedAck
    \/ NoResponseToProbeRequests
    \/ MemberJoins
    \/ MemberLeaves
    \/ EndSim

MemberOrNil ==
    Member \union {Nil}

States ==
    { AliveState, SuspectState, DeadState, UnknownState }

TypeOK ==
    /\ incarnation \in [Member -> Nat \union {Nil}]
    /\ peer_states \in [Member -> [Member -> [incarnation    : Nat, 
                                              state          : States, 
                                              round          : Nat, 
                                              disseminations : 0..DisseminationLimit]]]
    /\ round \in [Member -> Nat]
    /\ pending_direct_ack \in [Member -> MemberOrNil]
    /\ pending_indirect_ack \in [Member -> MemberOrNil]
    /\ probe_ctr \in [Member -> [Member -> Nat]]
    /\ TLCGet("level") < 50

Inv ==
    IF (~ ENABLED Next) THEN
        sim_complete = 2
    ELSE
        TRUE

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Ensemble ==
    1..10

============================================================================
\* Modification History
\* Last modified Fri Sep 04 08:48:01 PDT 2020 by jack
\* Last modified Thu Oct 18 12:45:40 PDT 2018 by jordanhalterman
\* Created Mon Oct 08 00:36:03 PDT 2018 by jordanhalterman