-------------------------------- MODULE swim_stats --------------------------------

(*
Based on the Atomix SWIM TLA+ specification (https://github.com/atomix/atomix-tlaplus/blob/master/SWIM/SWIM.tla) 
but with significant modification aimed at making the spec more useful for simulation. The original spec was
designed entirely on safety properties, allowing each action equal probability, and without any features related
to optimising time to convergence (as those features are not for safety). This spec cares a great deal 
about modelling all the aspects of the SWIM paper related to optimising time to convergence and modelling
some fairness of scheduling of probes.

Summary of modifications:

- Message passing modified to a request/response mechanism without duplication. For simulation
  we want to measure statistical properties under normal network conditions (for now).

- As per the SWIM paper:
    - Gossip messages are piggybacked on probe and ack messages.
    - The number of gossip messages per probe/ack is limited
    - When there are more gossip updates than can fit, those updates with the fewest hops are prioritised.
    - Suspected members are marked as dead after a timeout

- Fair scheduling is modelled to ensure that:
    - the probe rate of each member is balanced
    - each member randomly picks a member to probe, but with guaranteed bounds 
      (i.e. cannot randomly pick the same member over and over again)

- The ensemble of members start all seeing each other as alive, but one being recently dead. 
  The aim is to measure the number of probes in order for the ensemble to converge on this new state.
  Shortly after reaching convergence, the spec will deadlock. This is by design as it helps
  simulation by halting when we reach the objective. On deadlocking, any statistical properties
  being tracked are printed out in a csv format.

Not implemented:

- Probe requests

*)

EXTENDS Naturals, FiniteSets, Sequences, TLC, Integers


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


VARIABLES incarnation,      \* Member incarnation numbers
          members,          \* Member state of the ensemble
          updates,          \* Pending updates to be gossipped
          tick,             \* A per member counter for the number of probes sent. This is used
                            \* to ensure that members send out probes at the same rate. It is not
                            \* part of the actual state of the system, but a meta variable for this spec.
          requests,         \* a function of all requests and their responses
          pending_req,      \* tracking pending requests per member to member       
          responses_seen,   \* the set of all processed responses
          sim_complete      \* used to signal the end of the simulation    

vars == <<incarnation, members, updates, requests, pending_req, responses_seen, tick, sim_complete>>

----

InitMemberVars ==
    \E dead_members \in SUBSET Member : 
        /\ Cardinality(dead_members) = DeadMemberCount
        /\ incarnation = [m \in Member |-> IF m \in dead_members THEN Nil ELSE 1]
        /\ members = [m \in Member |-> IF m \in dead_members 
                                       THEN [m1 \in Member |-> [incarnation |-> 0, state |-> Nil, suspect_timeout |-> SuspectTimeout]]
                                       ELSE [m1 \in Member |-> [incarnation |-> 1, state |-> Alive, suspect_timeout |-> SuspectTimeout]]]
        /\ updates = [m \in Member |-> <<>>]
        /\ tick = [m \in Member |-> 0]
        /\ sim_complete = 0

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

\* Sets whether 'source' has a pending response from 'dest' to TRUE or FALSE
TrackPending(source, dest) ==
    pending_req' = [pending_req EXCEPT ![source][dest] = 
                            [pending |-> TRUE, count |-> @.count + 1]]

UntrackPending(source, dest) ==
    pending_req' = [pending_req EXCEPT ![source][dest] = 
                            [pending |-> FALSE, count |-> @.count]]

(* HELPER Operators to determine if the ensemble has converged 
   on the real state of the system *)

\* The set of all members that are alive
LiveMembers ==
    { m \in Member : incarnation[m] # Nil }

\* The real state being either dead or alive. The real state of a member 
\* cannot be "suspected".
RealStateOfMember(m) ==
    IF incarnation[m] = Nil THEN Dead ELSE Alive

\* TRUE when all live members see the true state of the universe
Converged ==
    LET live_members == LiveMembers
        dead_members == Member \ LiveMembers
    IN
        \A m1 \in live_members :
            \A m2 \in Member :
                \/ m1 = m2
                \/ /\ m1 # m2
                   /\ members[m1][m2].state = RealStateOfMember(m2)

\* TRUE when all live members see the true state of the universe in the next state
WillBeConverged ==
    LET live_members == LiveMembers
        dead_members == Member \ LiveMembers
    IN
        \A m1 \in live_members :
            \A m2 \in Member :
                \/ m1 = m2
                \/ /\ m1 # m2
                   /\ members'[m1][m2].state = RealStateOfMember(m2)
                   

(************************************************************************) 
(******************** OUTGOING GOSSIP ***********************************)
(************************************************************************)

(* NOTES
Gossip is selected for piggybacking on probes and acks based on:
1. The maximum number of times an item can be gossiped (lambda log n in the paper
   but in this spec the constant DisseminationLimit.
2. The maximum number of items that can be piggybacked on any given probe or ack.
   In this spec the constant MaxUpdatesPerPiggyBack.
3. In the case that all valid gossip does not fit, prioritise items that have been 
   disseminated fewer times. All gossip is stored in a function gossip |-> dissemination counter
*)

GossipUnderLimit(m) ==
    { update \in DOMAIN updates[m] : updates[m][update] < DisseminationLimit }
    
GossipOverLimit(m) ==
    { update \in DOMAIN updates[m] : updates[m][update] >= DisseminationLimit } 

\* Choose the gossip based on the MaxUpdatesPerGossip and when there is more
\* gossip than can be accomodated in a single message, choose the gossip items
\* in order of fewest disseminations first

Prioritise(m, candidate_gossip, limit) ==
    CHOOSE update_subset \in SUBSET candidate_gossip :
        /\ Cardinality(update_subset) = limit
        /\ \A u1 \in update_subset :
            \A u2 \in candidate_gossip :
                updates[m][u1] <= updates[m][u2] 

SelectOutgoingGossip(m, new_gossip) ==
    LET candidate_gossip == GossipUnderLimit(m)
        limit == IF new_gossip = {} THEN MaxUpdatesPerPiggyBack ELSE MaxUpdatesPerPiggyBack - 1 
    IN
        IF Cardinality(candidate_gossip) <= limit 
        THEN candidate_gossip \union new_gossip
        ELSE 
            LET prioritised_gossip == Prioritise(m, candidate_gossip, limit)
            IN prioritised_gossip \union new_gossip
            
\* The gossip that is a candidate for being piggybacked on the ack
\* This is the existing pending gossip + a new gossip
\* The gossip received in the probe is not included
RefuteSuspicionGossip(member, probe_state) ==
    IF probe_state = Suspect
    THEN { [id          |-> member, 
            incarnation |-> incarnation'[member], 
            state       |-> Alive] }
    ELSE {}

\* This gossip can also include a refutation of being Suspect. Not currently
\* needed in this spec, but will be required if testing false positives later on.
SelectOutgoingAckGossip(member, probe_state) ==
    SelectOutgoingGossip(member, RefuteSuspicionGossip(member, probe_state))

\* Increment the dissemination counter of each gossip item
IncrementPiggybackCount(member, gossip_to_send) ==
    updates' = [updates EXCEPT ![member] = [u \in DOMAIN updates[member] |->
                                                IF u \in gossip_to_send 
                                                THEN updates[member][u] +1
                                                ELSE updates[member][u]]]

(************************************************************************) 
(******************** INCOMING GOSSIP ***********************************)
(************************************************************************)

(* NOTES

Gossip can come in on probes and acks. Any incoming gossip is merged with existing gossip
and any stale gossip is filtered out (compaction). 

Stale gossip is that which has a lower incarnation number than the member has recorded for
that target member or which has the same incarnation number, but a lower precedence state. The 
precedence order is (highest to lowest) Dead, Suspect, Alive.

The merged and compacted gossip is then applied to known information that the member has on
all other members (the members variable).
*)

\* Returns TRUE or FALSE as to whether an individual gossip item is new for this member
\* It is new only if:
\* - its incarnation number is > than the known incarnation number of the target member
\* - its incarnation number equals the known incarnation number of the target member but its state has higher precedence
IsNewInformation(member, gossip) ==
    \/ gossip.incarnation > members[member][gossip.id].incarnation
    \/ /\ gossip.incarnation = members[member][gossip.id].incarnation
       /\ gossip.state < members[member][gossip.id].state
       
\* Returns TRUE if the gossip matches currently known information or is new       
IsCurrentOrNewInformation(member, gossip) ==
    \/ gossip.incarnation >= members[member][gossip.id].incarnation
    \/ /\ gossip.incarnation = members[member][gossip.id].incarnation
       /\ gossip.state <= members[member][gossip.id].state       

\* Merges incoming gossip with existing gossip and compacts it, removing any stale items
\* 1. Merge the gossip with any existing gossip that the member has. The merged gossip may have
\*    multiple items pertaining to a given member id.
\* 2. Compact the merged gossip to remove stale items and so that even in the case 
\*    that there are multiple items of a given id only the highest precedence one remains.
MergeAndCompactGossip(member, gossip_items) ==
    LET merged_gossip == DOMAIN updates[member] \union gossip_items
    IN  { 
            g1 \in merged_gossip :
                /\ IsCurrentOrNewInformation(member, g1)
                /\ ~\E g2 \in merged_gossip :
                    /\ g1 # g2
                    /\ g1.id = g2.id
                    /\ \/ g2.incarnation > g1.incarnation
                       \/ /\ g2.incarnation = g1.incarnation
                          /\ g2.state < g1.state  
         }

\* Returns TRUE or FALSE as to whether the member has a gossip 
MemberHasGossipItem(member, gossip_items) ==
    \E g \in gossip_items : g.id = member

\* Returns the gossip that concerns this member    
GossipItemOfMember(member, gossip_items) ==
    CHOOSE g \in gossip_items : g.id = member

\* Saves the compacted gossip and increments the dissemination counter of any gossip that
\* was sent out
SaveGossip(member, compacted_updates, sent_updates) ==
    updates' = [updates EXCEPT ![member] = 
                    [u \in compacted_updates |->
                        LET sent == u \in sent_updates
                            new == u \notin DOMAIN updates[member]
                        IN 
                            IF sent /\ new THEN 1
                            ELSE IF sent /\ ~new THEN updates[member][u] + 1
                            ELSE IF ~sent /\ ~new THEN updates[member][u]
                            ELSE 0]]

\* Updates the state based on the compacted gossip (which contains only existing or new information)
\* If its new information, update the state
\* If the information already exists, then no change
\* If there is no gossip about a member, then no change 
UpdateMemberState(member, compacted_gossip) ==
    members' = [members EXCEPT ![member] = 
                    [m \in Member |-> 
                          IF MemberHasGossipItem(m, compacted_gossip) 
                          THEN LET gossip_item == GossipItemOfMember(m, compacted_gossip)
                               IN IF IsNewInformation(member, gossip_item)
                                  THEN [incarnation     |-> gossip_item.incarnation, 
                                        state           |-> gossip_item.state,
                                        suspect_timeout |-> SuspectTimeout] 
                                  ELSE @[m]
                          ELSE @[m]]]

\* Merges and compacts gossip, then:
\* - Updates the known information of other members based on the new gossip
\* - Save the gossip (includes incrementing dissemination counters)
HandleGossip(member, incoming_gossip, sent_gossip) ==
    LET compacted_gossip == MergeAndCompactGossip(member, incoming_gossip)
    IN
        /\ UpdateMemberState(member, compacted_gossip)
        /\ SaveGossip(member, compacted_gossip, sent_gossip)
        /\ IF WillBeConverged THEN sim_complete' = 1 ELSE UNCHANGED sim_complete

\* Updates the state of a peer on the given 'source' node
\* When the state of the 'dest' is updated, an update message is added to existing gossip
UpdateState(source, dest, inc, state) ==
    /\ members' = [members EXCEPT ![source][dest] = [incarnation     |-> inc, 
                                                     state           |-> state,
                                                     suspect_timeout |-> @.suspect_timeout]]
    /\ SaveGossip(source, {[id          |-> dest, 
                            incarnation |-> inc, 
                            state       |-> state]}, {})

\* Updates the state of a peer on the given 'source' node and decrements its suspect timeout counter.
\* When the state of the 'dest' is updated, an update message is added to existing gossip    
UpdateAsSuspect(source, dest, inc) ==
    /\ members' = [members EXCEPT ![source][dest] = [incarnation |-> inc, 
                                                     state       |-> Suspect,
                                                     suspect_timeout |-> @.suspect_timeout - 1]]
    /\ SaveGossip(source, {[id          |-> dest, 
                           incarnation |-> inc, 
                           state       |-> Suspect]}, {})


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

HasNoMembersToExpire(source) ==
    ~\E m \in Member :
        /\ members[source][m].state = Suspect
        /\ members[source][m].suspect_timeout <= 0

IsValidProbeTarget(source, dest) ==
    /\ source # dest
    /\ members[source][dest].state # Dead               \* The source believes the dest to be alive or suspect
    /\ \/ members[source][dest].state # Suspect         \* If suspect, we haven't reached the suspect timeout
       \/ /\ members[source][dest].state = Suspect
          /\ members[source][dest].suspect_timeout > 0

\* 'tick' balances the probes across the ensemble more or less
\* 'pending_req' ensures we don;t have more than one pedning request for this source-dest
\* and also 
IsFairlyScheduled(source, dest) ==
    /\ pending_req[source][dest].pending = FALSE
    /\ \A m \in Member : 
         IF IsValidProbeTarget(source, m) 
         THEN pending_req[source][dest].count <= pending_req[source][m].count
         ELSE TRUE
    /\ \A m1 \in LiveMembers : tick[source] <= tick[m1]

Probe(source, dest) ==
    /\ sim_complete = 0
    /\ incarnation[source] # Nil        \* The source is alive
    /\ pending_req[source][dest].pending = FALSE
    /\ HasNoMembersToExpire(source)     \* Only send a probe if we have no pending expiries
    /\ IsValidProbeTarget(source, dest) \* The dest is valid (not dead for example)
    /\ IsFairlyScheduled(source, dest)  \* We aim to make the rate probe sending more or less balanced
    /\ LET gossip_to_send == SelectOutgoingGossip(source, {})
       IN
        /\ SendRequest([type    |-> ProbeMessage,
                        source  |-> source,
                        dest    |-> dest,
                        tick    |-> tick[source],
                        payload |-> members[source][dest],
                        gossip  |-> gossip_to_send])
        /\ IncrementPiggybackCount(source, gossip_to_send)
        /\ TrackPending(source, dest)
        /\ UNCHANGED <<incarnation, members, tick, responses_seen, sim_complete >>


        
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
    SendReply(request, [type      |-> AckMessage,
                        source    |-> request.dest,
                        dest      |-> request.source,
                        dest_tick |-> request.tick,
                        payload   |-> payload,
                        gossip    |-> piggyback_gossip])
 
ReceiveProbe ==
    \E r \in DOMAIN requests :
        /\ NotRepliedTo(r)
        /\ incarnation[r.dest] # Nil
        /\ LET send_gossip == SelectOutgoingAckGossip(r.dest, r.payload.state)
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
                /\ HandleGossip(r.dest, r.gossip, send_gossip) 
    /\ UNCHANGED <<tick, responses_seen, pending_req >>

(************************************************************************) 
(******************** ACTION: ReceiveAck ********************************)
(************************************************************************)

(* Notes

Handles an ack message from a peer
- If the acknowledged message is greater than the incarnation for the member on the destination
node, update the member's state and add an update for gossip.
- Also adds any piggybacked gossip on ack to pending updates.
- Increments this member's tick amd untracks the original request - required for fair scheduling
*)
ReceiveAck ==
    \E r \in DOMAIN requests :
        LET response == requests[r]
        IN
            /\ NotProcessedResponse(response)
            /\ response.type = AckMessage
            /\ LET new_gossip == IF response.payload.incarnation > members[response.dest][response.source].incarnation 
                                 THEN response.gossip 
                                         \union { [id          |-> response.source, 
                                                   incarnation |-> response.payload.incarnation, 
                                                   state       |-> Alive] }
                                 ELSE response.gossip
               IN 
                /\ tick' = [tick EXCEPT ![response.dest] = @ + 1]
                /\ HandleGossip(response.dest, new_gossip, {})
                /\ UntrackPending(r.source, r.dest)
                /\ ResponseProcessed(response)
                /\ UNCHANGED <<incarnation, requests>>

(************************************************************************) 
(******************** ACTION: ProbeFails ********************************)
(************************************************************************)

(* Notes

Handles a failed probe.

If the probe request matches the local incarnation for the probe destination and the local
state for the destination is Alive or Suspect, update the state to Suspect and decrement the timeout counter.

Increments this member's tick amd untracks the original request - required for fair scheduling
*)
ProbeFails ==
    \E r \in DOMAIN requests :
        /\ r.type = ProbeMessage
        /\ NotRepliedTo(r)
        /\ incarnation[r.dest] = Nil
        /\ IF r.payload.incarnation > 0
                /\ r.payload.incarnation = members[r.source][r.dest].incarnation
                /\ members[r.source][r.dest].state \in { Alive, Suspect}
           THEN
                UpdateAsSuspect(r.source, r.dest, r.payload.incarnation)
           ELSE UNCHANGED << members, updates >>
        /\ tick' = [tick EXCEPT ![r.source] = @ + 1]
        /\ UntrackPending(r.source, r.dest)
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
Expire(source, dest) ==
    /\ source # dest
    /\ members[source][dest].state = Suspect
    /\ members[source][dest].suspect_timeout <= 0
    /\ UpdateState(source, dest, members[source][dest].incarnation, Dead)
    /\ IF WillBeConverged THEN sim_complete' = 1 ELSE UNCHANGED sim_complete
    /\ UNCHANGED <<incarnation, requests, pending_req, responses_seen, tick >>

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
    /\ members' = [members EXCEPT ![id] = [i \in DOMAIN members |-> [incarnation |-> 0, state |-> Dead, suspect_timeout |-> SuspectTimeout]]]
    /\ UNCHANGED <<updates, requests, pending_req, responses_seen, tick, sim_complete>>

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
    /\ members' = [members EXCEPT ![id] = [j \in Member |-> [incarnation |-> 0, state |-> Nil, suspect_timeout |-> SuspectTimeout]]]
    /\ updates' = [updates EXCEPT ![id] = {}]
    /\ UNCHANGED <<requests, pending_req, responses_seen, tick, sim_complete>>

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
            /\ \A m \in LiveMembers : PrintT("ticks" \o "," \o ToString(m) \o "," \o ToString(tick[m]))
            /\ PrintT("converged")
        ELSE
            /\ Print("could not converge", FALSE)
    ELSE
        \A m \in Member : tick[m] \in Nat

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
\* Last modified Fri Aug 21 07:47:21 PDT 2020 by jack
\* Last modified Thu Oct 18 12:45:40 PDT 2018 by jordanhalterman
\* Created Mon Oct 08 00:36:03 PDT 2018 by jordanhalterman
