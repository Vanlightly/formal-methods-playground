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
    - Suspected members are marked as dead after a timeout
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
          DeadMemberCount,       \* The number of dead members the ensemble need to detect
          SuspectTimeout,        \* The number of failed probes before suspected node made dead
          DisseminationLimit,    \* The lambda log n value (the maximum number of times a given update can be piggybacked)
          MaxUpdatesPerPiggyBack \* The maximum  number of state updates to be included in
                                 \* any given piggybacked gossip message

\* The values of member states must be sequential
ASSUME Alive > Suspect /\ Suspect > Dead
ASSUME DeadMemberCount \in (Nat \ {0})
ASSUME SuspectTimeout \in (Nat \ {0})
ASSUME MaxUpdatesPerPiggyBack \in (Nat \ {0})


            
VARIABLES \* actual state in the protocol
          incarnation,       \* Member incarnation numbers
          peer_states,       \* The known state that each member has on its peers
          
          \* fair scheduling
          round,            \* A per member counter for the number of probes sent. This is used
                            \* to ensure that members send out probes at the same rate. It is not
                            \* part of the actual state of the system, but a meta variable for this spec.
          pending_req,      \* tracking pending requests per member to member
          
          \* messaging passing
          requests,         \* a function of all requests and their responses       
          responses_seen,   \* the set of all processed responses
          
          \* to end simulation once convergence reached
          sim_complete
          
vars == <<incarnation, peer_states, requests, pending_req, responses_seen, round, sim_complete>>
message_vars == <<requests, pending_req, responses_seen>>

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
    \A r \in 0..1000 : 
        /\ TLCSet(updates_pr_ctr(r), 0)
        /\ TLCSet(eff_updates_pr_ctr(r), 0)
        /\ TLCSet(suspect_ctr(r), -1)
        /\ TLCSet(dead_ctr(r), -1)
        /\ TLCSet(suspect_states_ctr(r), -1)
        /\ TLCSet(dead_states_ctr(r), -1)

----

InitMemberVars ==
    \E dead_members \in SUBSET Member : 
        /\ Cardinality(dead_members) = DeadMemberCount
        /\ incarnation = [m \in Member |-> IF m \in dead_members THEN Nil ELSE 1]
        /\ peer_states = [m \in Member |-> [m1 \in Member |-> 
                                                [incarnation    |-> 1, 
                                                 state          |-> Alive, 
                                                 timeout        |-> SuspectTimeout, 
                                                 disseminations |-> DisseminationLimit]]]
        /\ round = [m \in Member |-> 0]
        /\ sim_complete = 0
        /\ ResetStats

InitMessageVars ==
    /\ requests = [req \in {} |-> 0]
    /\ pending_req = [m \in Member |-> [m1 \in Member |-> [pending |-> FALSE, count |-> 0]]]
    /\ responses_seen = {}

----
(* HELPER Operators for message passing *)

\* Send a request only if the request has already not been sent
SendRequest(request) ==
    /\ request \notin DOMAIN requests
    /\ requests' = requests @@ (request :> [type |-> "-"])
    
\* Send a reply to a request, given the request has been sent
SendReply(request, reply) ==
    /\ request \in DOMAIN requests
    /\ requests' = [requests EXCEPT ![request] = reply]

\* True when a request has not had a reply sent
NotRepliedTo(request) ==
    /\ request \in DOMAIN requests
    /\ requests[request].type = "-"

\* True when a response has been received and processed     
NotProcessedResponse(response) ==
    \/ response.type = "-"
    \/ /\ response.type # "-"
       /\ response \notin responses_seen
    
\* Signals that the response is processed so it is not processed again
ResponseProcessed(response) ==
    responses_seen' = responses_seen \union { response }

\* Signals that the request failed due to whatever reason    
RequestFailed(request) ==
    /\ request \in DOMAIN requests
    /\ requests[request].type = "-"
    /\ requests' = [requests EXCEPT ![request].type = "failed"]

SetAsPending(member, peer) ==
    pending_req' = [pending_req EXCEPT ![member][peer] = 
                            [pending |-> TRUE, count |-> @.count + 1]]

SetAsNotPending(member, peer) ==
    pending_req' = [pending_req EXCEPT ![member][peer] = 
                            [pending |-> FALSE, count |-> @.count]]

(* HELPER Operators to determine if the ensemble has converged 
   on the real state of the system *)

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
Peer states are selected for piggybacking on probes and acks based on:
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
                

MayBeRecordMemberCounts ==
    \* Is this is a step that leads to all members being on the same round then record the member count stats
    LET live_members == LiveMembers
    IN
        IF  /\ \E m1, m2 \in live_members : round[m1] # round[m2] 
            /\ \A m3, m4 \in live_members : round'[m3] = round'[m4]
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
             
             (*         
            \A n \in 0..DisseminationLimit :
                LET count == Cardinality({ g \in new_info_from_source : 
                                            updates[gossip_source][g] = n })
                IN 
                    IF count > 0 
                    THEN TLCSet(eff_gossip_age_ctr(count), TLCGet(eff_gossip_age_ctr(count)) + count)
                    ELSE TRUE*)
(*                    
\A round \in 0..1000 : 
        /\ TLCSet(gossip_card_ctr(round), 0)
        /\ TLCSet(eff_gossip_card_ctr(round), 0)
        /\ TLCSet(suspect_ctr(round), 0)
        /\ TLCSet(dead_ctr(round), 0)
*)
            
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

ResetCountersOfRecord(record) ==
    [incarnation    |-> record.incarnation,
     state          |-> record.state,
     disseminations |-> 0,
     timeout        |-> SuspectTimeout]

NewAliveMemberRecord(incarnation_number) ==
    [incarnation    |-> incarnation_number, 
     state          |-> Alive, 
     disseminations |-> 0, 
     timeout        |-> SuspectTimeout]

\* updates the state of a member's peers based on incoming and outgoing gossip
\* If member's incarnation for the gossip source is stale then update it
\* Increment dissemination counters of outgoing gossip
\* Replace any peer state that is stale
MergeGossip(member, gossip_source, source_incarnation, incoming_updates, sent_updates) ==
    [peer \in Member |-> 
        IF peer = gossip_source
        THEN IF peer_states[member][gossip_source].incarnation < source_incarnation
             THEN NewAliveMemberRecord(source_incarnation)
             ELSE peer_states[member][gossip_source]
        ELSE
            LET is_in_gossip == peer \in DOMAIN incoming_updates
                is_in_sent   == peer \in DOMAIN sent_updates
            IN    
                IF is_in_gossip
                THEN IF IsNewInformation(member, peer, incoming_updates[peer])
                     THEN ResetCountersOfRecord(incoming_updates[peer])
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
       /\ IF WillBeConverged THEN sim_complete' = 1 ELSE UNCHANGED sim_complete

\* Updates the state and counters of a peer of the given member
\* This is not called when an incarnation has changed
UpdateState(member, peer, state) ==
    LET timeout == IF state = Suspect 
                   THEN peer_states[member][peer].timeout - 1
                   ELSE peer_states[member][peer]
        disseminations == IF peer_states[member][peer].state = state
                          THEN peer_states[member][peer].disseminations
                          ELSE 0
    IN                                       
        peer_states' = [peer_states EXCEPT ![member][peer] = 
                                    [@ EXCEPT !.state          = state,
                                              !.disseminations = disseminations,
                                              !.timeout        = timeout]]

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
        /\ peer_states[member][peer].timeout <= 0

IsValidProbeTarget(member, peer) ==
    /\ member # peer
    /\ peer_states[member][peer].state # Dead               \* The member believes the peer to be alive or suspect
    /\ \/ peer_states[member][peer].state # Suspect         \* If suspect, we haven't reached the suspect timeout
       \/ /\ peer_states[member][peer].state = Suspect
          /\ peer_states[member][peer].timeout > 0

\* 'round' balances the probes across the ensemble more or less
\* 'pending_req' ensures we don't have more than one pending request for this source at a time
IsFairlyScheduled(member, peer) ==
    /\ \A m \in Member : pending_req[member][m].pending = FALSE
    /\ \A m \in Member : 
         IF IsValidProbeTarget(member, m) 
         THEN pending_req[member][peer].count <= pending_req[member][m].count
         ELSE TRUE
    /\ \A m1 \in Member : 
        \/ incarnation[m1] = Nil
        \/ /\ incarnation[m1] # Nil
           /\ round[member] <= round[m1]

Probe(member, peer) ==
    /\ member # peer
    /\ sim_complete = 0
    /\ incarnation[member] # Nil        \* The member is alive
    /\ HasNoMembersToExpire(member)     \* Only send a probe if we have no pending expiries
    /\ IsValidProbeTarget(member, peer) \* The peer is valid (not dead for example)
    /\ IsFairlyScheduled(member, peer)  \* We aim to make the rate probe sending more or less balanced
    /\ LET gossip_to_send == SelectOutgoingGossip(member, <<>>)
       IN
        /\ SendRequest([type    |-> ProbeMessage,
                        source  |-> member,
                        dest    |-> peer,
                        round   |-> round[member],
                        payload |-> peer_states[member][peer],
                        gossip  |-> gossip_to_send])
        /\ IncrementPiggybackCount(member, gossip_to_send)
        /\ SetAsPending(member, peer)
        /\ UNCHANGED <<incarnation, round, responses_seen, sim_complete >>


        
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
SendAck(request, payload, piggyback_gossip) ==
    SendReply(request, [type       |-> AckMessage,
                        source     |-> request.dest,
                        dest       |-> request.source,
                        dest_round |-> request.round,
                        payload    |-> payload,
                        gossip     |-> piggyback_gossip])
 
ReceiveProbe ==
    \E r \in DOMAIN requests :
        /\ NotRepliedTo(r)
        /\ incarnation[r.dest] # Nil
        /\ LET send_gossip == SelectOutgoingGossip(r.dest, r.gossip)
           IN 
                /\ \/ /\ r.payload.incarnation > incarnation[r.dest]
                      /\ incarnation' = [incarnation EXCEPT ![r.dest] = r.payload.incarnation + 1]
                      /\ SendAck(r, [incarnation |-> incarnation'[r.dest]], send_gossip)
                   \/ /\ r.payload.state = Suspect
                      /\ incarnation' = [incarnation EXCEPT ![r.dest] = incarnation[r.dest] + 1]
                      /\ SendAck(r, [incarnation |-> incarnation'[r.dest]], send_gossip)
                   \/ /\ r.payload.incarnation <= incarnation[r.dest]
                      /\ SendAck(r, [incarnation |-> incarnation[r.dest]], send_gossip)
                      /\ UNCHANGED <<incarnation>>
                /\ HandleGossip(r.dest, r.source, r.payload.incarnation, r.gossip, send_gossip) 
    /\ UNCHANGED <<round, responses_seen, pending_req >>

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
    \E r \in DOMAIN requests :
        LET response == requests[r]
        IN
            /\ NotProcessedResponse(response)
            /\ response.type = AckMessage
            /\ round' = [round EXCEPT ![response.dest] = @ + 1]
            /\ HandleGossip(response.dest, 
                            response.source, 
                            response.payload.incarnation, 
                            response.gossip, 
                            <<>>)
            /\ SetAsNotPending(r.source, r.dest)
            /\ ResponseProcessed(response)
            /\ UNCHANGED <<incarnation, requests>>

(************************************************************************) 
(******************** ACTION: ProbeFails ********************************)
(************************************************************************)

(* Notes
Handles a failed probe.
If the probe request matches the local incarnation for the probe destination and the local
state for the destination is Alive or Suspect, update the state to Suspect and decrement the timeout counter.
Increments this member's round amd untracks the original request - required for fair scheduling
*)
ProbeFails ==
    \E r \in DOMAIN requests :
        /\ r.type = ProbeMessage
        /\ NotRepliedTo(r)
        /\ incarnation[r.dest] = Nil
        /\ IF r.payload.incarnation > 0
                /\ r.payload.incarnation = peer_states[r.source][r.dest].incarnation
                /\ peer_states[r.source][r.dest].state \in { Alive, Suspect}
           THEN
                UpdateState(r.source, r.dest, Suspect)
           ELSE UNCHANGED << peer_states >>
        /\ round' = [round EXCEPT ![r.source] = @ + 1]
        /\ TLCDefer(MayBeRecordMemberCounts)
        /\ SetAsNotPending(r.source, r.dest)
        /\ RequestFailed(r)
        /\ UNCHANGED <<incarnation, responses_seen, sim_complete>>

(************************************************************************) 
(******************** ACTION: Expire ********************************)
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
    /\ member # peer
    /\ peer_states[member][peer].state = Suspect
    /\ peer_states[member][peer].timeout <= 0
    /\ UpdateState(member, peer, Dead)
    /\ IF WillBeConverged THEN sim_complete' = 1 ELSE UNCHANGED sim_complete
    /\ UNCHANGED <<incarnation, requests, pending_req, responses_seen, round >>

(*
***************** NOT CURRENTLY USED *****************
Adds a member to the cluster
* 'id' is the identifier of the member to add
If the member is not present in the state history:
* Initialize the member's incarnation to 1
* Initialize the member's states for all known members to incarnation: 0, state: Dead to allow heartbeats
* Enqueue an update to notify peers of the member's existence
Mod 1: No history variable
*)
AddMember(id) ==
    /\ incarnation[id] = Nil
    /\ incarnation' = [incarnation EXCEPT ![id] = 1]
    /\ peer_states' = [peer_states EXCEPT ![id] = [i \in DOMAIN peer_states |-> [incarnation |-> 0, state |-> Dead, timeout |-> SuspectTimeout]]]
    /\ UNCHANGED <<requests, pending_req, responses_seen, round, sim_complete>>

(*
***************** NOT CURRENTLY USED *****************
Removes a member from the cluster
* 'id' is the identifier of the member to remove
Alter the domain of 'incarnation', 'members', and 'updates' to remove the member's
volatile state. We retain only the in-flight messages and history for model checking.
*)
RemoveMember(id) ==
    /\ incarnation[id] # Nil
    /\ incarnation' = [incarnation EXCEPT ![id] = Nil]
    /\ peer_states' = [peer_states EXCEPT ![id] = [j \in Member |-> [incarnation |-> 0, state |-> Nil, timeout |-> SuspectTimeout]]]
    /\ UNCHANGED <<requests, pending_req, responses_seen, round, sim_complete>>

----

\* Initial state
Init ==
    /\ InitMessageVars
    /\ InitMemberVars

(* 
Next state predicate
Due to a convergence check in the Probe operator, it will
eventually deadlock when converged as we want the simulation 
to stop at that point and print out the statistics
*)
Next ==
    \/ \E i, j \in Member : 
        \/ Probe(i, j)
        \/ Expire(i, j)
    \/ ReceiveProbe
    \/ ReceiveAck
    \/ ProbeFails
    
(* Remnants of original Next formula that is not currently required.
   Probablistic dropping of messages may be added at some point. *)
    \* \/ \E i \in Member : RemoveMember(i)
    \* \/ \E i \in Member : AddMember(i)
    \* \/ \E m \in DOMAIN messages : DuplicateMessage(m)
    \* \/ \E m \in DOMAIN messages : DropMessage(m)

\* Prints out the stats on deadlock 
\* The spec is designed to deadlock shortly after convergence is reached
PrintStatesOnConvergence ==
    IF (~ ENABLED Next) THEN
        IF Converged THEN
            /\ LET max_stats_round == MaxRound
                   cfg_str == "," \o ToString(Cardinality(Member)) 
                                \o "," \o ToString(DeadMemberCount)
                                \o "," \o ToString(SuspectTimeout)
                                \o "," \o ToString(DisseminationLimit)
                                \o "," \o ToString(MaxUpdatesPerPiggyBack)
                                \o ","
               IN
                /\ PrintT("rounds" \o cfg_str \o ToString(max_stats_round))
                /\ \A r \in 1..max_stats_round : PrintT("updates_in_round" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(updates_pr_ctr(r))))
                /\ \A r \in 1..max_stats_round : PrintT("eff_updates_in_round" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(eff_updates_pr_ctr(r))))
                /\ \A r \in 1..max_stats_round : 
                    IF TLCGet(suspect_ctr(r)) = -1 
                    THEN PrintT("suspected_members_count" \o cfg_str \o ToString(r) \o "," \o ToString(CurrentMemberCount(Suspect)))
                    ELSE PrintT("suspected_members_count" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(suspect_ctr(r))))
                /\ \A r \in 1..max_stats_round :
                    IF TLCGet(dead_ctr(r)) = -1 
                    THEN PrintT("dead_members_count" \o cfg_str \o ToString(r) \o "," \o ToString(CurrentMemberCount(Dead)))
                    ELSE PrintT("dead_members_count" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(dead_ctr(r))))
                /\ \A r \in 1..max_stats_round : 
                    IF TLCGet(suspect_states_ctr(r)) = -1 
                    THEN PrintT("suspect_states_count" \o cfg_str \o ToString(r) \o "," \o ToString(CurrentStateCount(Suspect)))
                    ELSE PrintT("suspect_states_count" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(suspect_states_ctr(r))))
                /\ \A r \in 1..max_stats_round :
                    IF TLCGet(dead_states_ctr(r)) = -1 
                    THEN PrintT("dead_states_count" \o cfg_str \o ToString(r) \o "," \o ToString(CurrentStateCount(Dead)))
                    ELSE PrintT("dead_states_count" \o cfg_str \o ToString(r) \o "," \o ToString(TLCGet(dead_states_ctr(r))))
            /\ PrintT("converged")
            /\ ResetStats
        ELSE
            /\ Print("could not converge", FALSE)
    ELSE
        \A m \in Member : round[m] \in Nat

(*
OLD - TO BE REVIEWED
*)    
Liveness ==
    /\ \A m1, m2 \in Member :
        /\ WF_vars(Probe(m1, m2))
        /\ WF_vars(Expire(m1, m2))        

    

Spec == Init /\ [][Next]_vars /\ Liveness

=============================================================================
\* Modification History
\* Last modified Tue Aug 25 06:56:14 PDT 2020 by jack
\* Last modified Thu Oct 18 12:45:40 PDT 2018 by jordanhalterman
\* Created Mon Oct 08 00:36:03 PDT 2018 by jordanhalterman