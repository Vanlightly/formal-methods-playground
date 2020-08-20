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
          MaxUpdatesPerPiggyBack \* The maximum  number of state updates to be included in
                                 \* any given piggybacked gossip message

\* The values of member states must be sequential
ASSUME Alive > Suspect /\ Suspect > Dead
ASSUME DeadMemberCount \in (Nat \ {0})


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
        /\ pending_req = [m \in Member |-> [m1 \in Member |-> [pending |-> FALSE, count |-> 0]]]
        /\ updates = [m \in Member |-> {}]
        /\ tick = [m \in Member |-> 0]
        /\ sim_complete = 0

InitMessageVars ==
    /\ requests = [req \in {} |-> 0]
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

(* HELPER Operators for updating member state *)

\* Records an 'update' to be gossipped by the given 'member'
RecordUpdate(member, new_update) ==
    updates' = [updates EXCEPT ![member] = @ \union {new_update}]    
    
\* Replaces all updates of a member   
SetUpdates(member, new_updates) == 
    updates' = [updates EXCEPT ![member] = new_updates]

\* Updates the state of a peer on the given 'source' node
\* When the state of the 'dest' is updated, an update message is enqueued for gossip
\* and the state change is recorded in the 'source' node's history for model checking.
UpdateState(source, dest, inc, state, hops) ==
    /\ members' = [members EXCEPT ![source][dest] = [incarnation     |-> inc, 
                                                     state           |-> state,
                                                     suspect_timeout |-> @.suspect_timeout]]
    /\ RecordUpdate(source, [id          |-> dest, 
                             incarnation |-> inc, 
                             state       |-> state, 
                             hops        |-> hops])
    
UpdateAsSuspect(source, dest, inc) ==
    /\ members' = [members EXCEPT ![source][dest] = [incarnation |-> inc, 
                                                     state       |-> Suspect,
                                                     suspect_timeout |-> @.suspect_timeout - 1]]
    /\ RecordUpdate(source, [id |-> dest, incarnation |-> inc, state |-> Suspect, hops |-> 0])

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
                   

(* HELPER Operators for choosing which gossip to include with a probe or ack *)

\* Choose the gossip based on the MaxUpdatesPerGossip and when there is more
\* gossip than can be accomodated in a single message, choose the gossip items
\* in order of fewest hops first
ChooseGossipToSend(m, candidate_gossip) ==
    IF Cardinality(candidate_gossip) <= MaxUpdatesPerPiggyBack THEN
        candidate_gossip
    ELSE
        CHOOSE update_subset \in SUBSET candidate_gossip :
            /\ Cardinality(update_subset) = MaxUpdatesPerPiggyBack
            /\ \A update \in update_subset :
                \A u1 \in candidate_gossip : update.hops <= u1.hops 

\* Increment the hop field on each gossip item
IncrementHop(gossip_to_send) ==
    { [id          |-> u.id,
       incarnation |-> u.incarnation,
       state       |-> u.state,
       hops        |-> u.hops + 1] : u \in gossip_to_send }

(* 
--------------------------------------------------
OPERATOR - Probe
--------------------------------------------------

Triggers a probe request to a peer
* 'source' is the source of the probe
* 'dest' is the destination to which to send the probe

- Uses fair scheduling to ensure that each member more or less is sending out a similar number of probes
  and that each member is choosing other members to probe in a balanced but random fashion

- Piggybacks any gossip that will fit, incrementing its hop counters

- Not enabled if convergence has been reached, ensuring deadlock will occur
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
    /\ LET gossip_to_send == IF updates[source] = {}
                             THEN {}
                             ELSE ChooseGossipToSend(source, updates[source])
       IN
        /\ SendRequest([type    |-> ProbeMessage,
                        source  |-> source,
                        dest    |-> dest,
                        tick    |-> tick[source],
                        payload |-> members[source][dest],
                        gossip  |-> IF gossip_to_send = {} THEN {} 
                                    ELSE IncrementHop(gossip_to_send)])
        /\ updates' = [updates EXCEPT ![source] = @ \ gossip_to_send]
        /\ TrackPending(source, dest)
        /\ UNCHANGED <<incarnation, members, tick, responses_seen, sim_complete >>

(*
GOSSIP HANDLING - USED WHEN RECEIVING A PROBE OR AN ACK
Handles a gossip update
* 'member' is the member that has received the gossip
* 'incoming_gossip' is the destination handling the update
* 'gossip' is the update message in the format with the updated member ID, incarnation, and state

If the member is not present in the destination's members, add it to the members set.
If the incarnation is greater than the destination's incarnation for the gossipped member,
update the member's incarnation and state on the destination node and enqueue the change for
gossip. If the incarnation is equal to the destination's incarnation for the member and the
state is less than the destination's state for the member, update the member's state on the
destination node and enqueue the change for gossip.
MOD 1: This is now a sub-formula of ReceiveProbe and ReceiveAck
MOD 2: No history variable
MOD 3: Handles multiple gossip items in a single step
*)

\* Returns TRUE or FALSE as to whether an individual gossip item is valid
\* It is valid only if:
\* - its incarnation number is higher than the known incarnation number of the target member
\* - its incarnation number equals the known incarnation number of the target member but its state has higher precedence
HigherPredenceThanLocal(member, gossip) ==
    \/ gossip.incarnation > members[member][gossip.id].incarnation
    \/ /\ gossip.incarnation = members[member][gossip.id].incarnation
       /\ gossip.state < members[member][gossip.id].state

\* Filter the gossip items to the ones that are:
\* 1. A valid state change for this member
\* 2. In the case there are multiple states of a given id, take the highest precedence one
FilterIncomingGossip(member, incoming_gossip) ==
    LET valid_gossip == { g \in incoming_gossip : HigherPredenceThanLocal(member, g) }
    IN
        { 
            g1 \in valid_gossip :
                LET gossip_of_member == {g2 \in valid_gossip : g2.id = g1.id}
                IN
                    \/ Cardinality(gossip_of_member) = 1
                    \/ \A g2 \in gossip_of_member :
                        \/ g1.incarnation_number > g2.incarnation_number
                        \/ /\ g1.incarnation_number = g2.incarnation_number
                           /\ g1.state < g2.state 
        }

\* Returns TRUE or FALSE as to whether the member has a gossip 
MemberHasGossipItem(member, gossip_items) ==
    \E g \in gossip_items : g.id = member

\* Returns the gossip that concerns this member    
GossipItemOfMember(member, gossip_items) ==
    CHOOSE g \in gossip_items : g.id = member

\* Filters the gossip down to only the valid gossip and only the highest precedence
\* per member. Then:
\* - Updates the known state of other members based on the new gossip
\* - Adds this gossip to the pending items to be gossipped to other members
HandleGossip(member, incoming_gossip) ==
    LET filtered_gossip == FilterIncomingGossip(member, incoming_gossip)
    IN
        /\ members' = [members EXCEPT ![member] = 
                        [m \in Member |-> IF MemberHasGossipItem(m, filtered_gossip) 
                                          THEN LET new_state == GossipItemOfMember(m, filtered_gossip)
                                               IN [incarnation     |-> new_state.incarnation, 
                                                   state           |-> new_state.state,
                                                   suspect_timeout |-> SuspectTimeout] \* TODO is this correct?
                                          ELSE @[m]]]
        /\ SetUpdates(member, filtered_gossip)
        /\ IF WillBeConverged THEN sim_complete' = 1 ELSE UNCHANGED sim_complete
        
(*
--------------------------------------------------
ACTION - ReceiveProbe
--------------------------------------------------

Handles a probe message from a peer.

If the received incarnation is greater than the destination's incarnation number, update the
destination's incarnation number to 1 plus the received number. This can happen after a node
leaves and rejoins the cluster. If the destination is suspected by the source, increment the
destination's incarnation, enqueue an update to be gossipped, and respond with the updated
incarnation. If the destination's incarnation is greater than the source's incarnation, just
send an ack.
- Adds pending gossip (that will fit) to the ack (piggybacking)
- Adds any incoming gossip that is valid, to the local updates to be gossiped later
*)

\* Send an ack and piggyback gossip if any to send
SendAck(request, payload, piggyback_gossip) ==
    SendReply(request, [type      |-> AckMessage,
                        source    |-> request.dest,
                        dest      |-> request.source,
                        dest_tick |-> request.tick,
                        payload   |-> payload,
                        gossip    |-> IF updates[request.source] = {} 
                                      THEN {} 
                                      ELSE IncrementHop(piggyback_gossip)])
        
\* TODO: we have "received" gossip which we need to store
\*       we have "pending" and "generated" gossip that can be added to the ack
\*       any left over that cannot fit in the ack must also be stored
\* strategy = set to store, set to send

\* The gossip that is a candidate for being piggybacked on the ack
\* This is the existing pending gossip + a new gossip
\* The gossip received in the probe is not included
CandidateAckGossip(member, probe_state) ==
    IF probe_state = Suspect
    THEN updates[member] \union { [id          |-> member, 
                                   incarnation |-> incarnation'[member], 
                                   state       |-> Alive, 
                                   hops        |-> 0] }
    ELSE updates[member]
 
ReceiveProbe ==
    \E r \in DOMAIN requests :
        /\ NotRepliedTo(r)
        /\ incarnation[r.dest] # Nil
        /\ 
           LET candidate_ack_gossip == CandidateAckGossip(r.dest, r.payload.state)
           IN
               LET gossip_to_send_in_ack == ChooseGossipToSend(r.dest, candidate_ack_gossip)
                   gossip_to_store == r.gossip \union (candidate_ack_gossip \ gossip_to_send_in_ack)
               IN 
                    /\ \/ /\ r.payload.incarnation > incarnation[r.dest]
                          /\ incarnation' = [incarnation EXCEPT ![r.dest] = r.payload.incarnation + 1]
                          /\ SendAck(r, [incarnation |-> incarnation'[r.dest]], gossip_to_send_in_ack)
                       \/ /\ r.payload.state = Suspect
                          /\ incarnation' = [incarnation EXCEPT ![r.dest] = incarnation[r.dest] + 1]
                          /\ SendAck(r, [incarnation |-> incarnation'[r.dest]], gossip_to_send_in_ack)
                       \/ /\ r.payload.incarnation <= incarnation[r.dest]
                          /\ SendAck(r, [incarnation |-> incarnation[r.dest]], gossip_to_send_in_ack)
                          /\ UNCHANGED <<incarnation>>
                    /\ HandleGossip(r.dest, gossip_to_store) 
    /\ UNCHANGED <<tick, responses_seen, pending_req >>

(*
--------------------------------------------------
ACTION ReceiveAck
--------------------------------------------------
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
                                 THEN updates[response.dest] 
                                         \union response.gossip 
                                         \union { [id          |-> response.source, 
                                                   incarnation |-> response.payload.incarnation, 
                                                   state       |-> Alive, 
                                                   hops        |-> 0] }
                                 ELSE updates[response.dest] \union response.gossip
               IN 
                /\ tick' = [tick EXCEPT ![response.dest] = @ + 1]
                /\ HandleGossip(response.dest, new_gossip)
                /\ UntrackPending(r.source, r.dest)
                /\ ResponseProcessed(response)
                /\ UNCHANGED <<incarnation, requests>>

(*
--------------------------------------------------
ACTION ProbeFails
--------------------------------------------------
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

(*
--------------------------------------------------
ACTION Expire
--------------------------------------------------
Expires a suspected peer once it has reached the timeout
* 'source' is the node on which to expire the peer
* 'dest' is the peer to expire

If the destination's state is Suspect, change its state to Dead and enqueue a gossip
update to notify peers of the state change.

Set the sim_complete variable to 1 if this action will cause convergence (so we deadlock soon after)
*)
Expire(source, dest) ==
    /\ source # dest
    /\ members[source][dest].state = Suspect
    /\ members[source][dest].suspect_timeout <= 0
    /\ UpdateState(source, dest, members[source][dest].incarnation, Dead, 0)
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
    /\ updates' = [updates EXCEPT ![id] = <<>>]
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
\* CURRENTLY SET UP FOR MODEL CHECKING (NO PRINTING)
PrintStatesOnConvergence ==
    IF (~ ENABLED Next) THEN
        IF Converged THEN
            \*/\ \A m \in LiveMembers : PrintT("ticks" \o "," \o ToString(m) \o "," \o ToString(tick[m]))
            \*/\ PrintT("converged")
            TRUE
        ELSE
            FALSE
            \*/\ Print("could not converge", FALSE)
        
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
\* Last modified Thu Aug 20 04:27:30 PDT 2020 by jack
\* Last modified Thu Oct 18 12:45:40 PDT 2018 by jordanhalterman
\* Created Mon Oct 08 00:36:03 PDT 2018 by jordanhalterman
