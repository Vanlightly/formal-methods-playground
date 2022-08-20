--------------------- MODULE KafkaRebalancingProtocol3 ---------------------
EXTENDS Integers, Naturals, Functions, FiniteSets, FiniteSetsExt, SequencesExt, Sequences, TLC, TLCExt, CSV, IOUtils

(*
Interesting cases:
- when a client restarts, its former self no longer sends
  heartbeats, so the broker cannot try and revoke the resources
  until it times out.
*)
CONSTANTS InitNumCoordMembers,
          InitNumCoordResources,
          InitNumClients,
          InitNumResources,
          AssignmentStrategy,
          StickyFairLimit
         
\* State space constraints 
CONSTANTS MaxAddClients,
          MaxRemoveClients,
          MaxAddResources,
          MaxRemoveResources,
          MaxHbCountDiff
          
CONSTANTS HeartbeatRequest,
          HeartbeatResponse   
          
CONSTANTS Nil

CONSTANTS Free,
          Assigning,
          Assigned,
          Revoking,
          IllegalState
          
CONSTANTS CSVFile          
          
VARIABLES messages,
          clients,
          resources,
          client_assignment,
          client_member_epoch,
          client_member_id,
          client_pending_hb,
          coord_member_epoch,
          coord_member_client,
          coord_member_pending_hb_res,
          coord_target_assignment,
          coord_resource_state,
          coord_epochs,
          aux_client_id,
          aux_member_id,
          aux_add_client_ctr,
          aux_remove_client_ctr,
          aux_add_resource_ctr,
          aux_remove_resource_ctr,
          aux_hb_ctr,
          config

clientVars == << client_assignment, client_member_epoch, client_member_id,
                 client_pending_hb >>
coordVars == << coord_member_epoch, coord_member_client,
                coord_member_pending_hb_res,
                coord_target_assignment, coord_epochs, coord_resource_state >>
auxIds == << aux_client_id, aux_member_id >>
auxCtrs == <<aux_add_client_ctr,
              aux_remove_client_ctr, aux_add_resource_ctr, 
              aux_remove_resource_ctr>>
auxHb == << aux_hb_ctr >>
auxVars == << auxIds, auxCtrs, auxHb >>
vars == << clients, resources, clientVars, coordVars, messages, auxVars, config >>
safetyView == << clients, resources, clientVars, coordVars, messages, config >>
livenessView == << clients, resources, clientVars, coordVars, messages, config, auxHb >>

StdOut(text) ==
   TRUE \*PrintT(text)

SetupComplete ==
    client_assignment # <<>>

TargetAssignmentReached ==
    /\ coord_epochs.resources = resources
    /\ coord_epochs.members = DOMAIN coord_member_epoch
    /\ coord_epochs.members = DOMAIN client_member_epoch
    /\ coord_epochs.group = coord_epochs.assignment
    /\ \A mid \in DOMAIN coord_member_epoch :
        coord_member_epoch[mid] = coord_epochs.group
    /\ \A r \in resources :
        /\ coord_resource_state[r].state = Assigned
        /\ coord_resource_state[r].epoch = coord_epochs.group

\* -------------------------------------------------
\* Assignment strategies
\* -------------------------------------------------

\* This spec has the following assignment strategies:
\* - Range assignment
\* - Round robin assignment
\* - Stick assignment (which has two sub-strategies):
\*    - Simple fair
\*    - Distance fair

\* Range assignment
RECURSIVE RangeAssign(_,_,_,_,_)
RangeAssign(free_res, mbs, alloc1, max, at_max) ==
     IF Cardinality(free_res) = 0 \/ Cardinality(mbs) = 0
     THEN alloc1
     ELSE
         LET r == CHOOSE r \in free_res : 
                    \A r1 \in free_res : r <= r1
             r_left == free_res \ {r}
             m == CHOOSE m \in mbs : 
                    \A m1 \in mbs : m <= m1
             alloc2 == IF m \in DOMAIN alloc1
                       THEN [alloc1 EXCEPT ![m] = @ \union {r}]
                       ELSE alloc1 @@ (m :> {r})
         IN
            IF Cardinality(alloc2[m]) = max
            THEN CASE at_max = 0 ->
                        RangeAssign(r_left, mbs \ {m}, alloc2, max, 0)
                   [] at_max = 1 ->
                        RangeAssign(r_left, mbs \ {m}, alloc2, max-1, 0)
                   [] OTHER -> 
                        RangeAssign(r_left, mbs \ {m}, alloc2, max, at_max-1)
            ELSE RangeAssign(r_left, mbs, alloc2, max, at_max)

CalculateRangeAssignments(mbs, res, target_alloc) ==
    LET resource_count == Cardinality(res)
        member_count   == Cardinality(mbs)
        min_alloc      == resource_count \div member_count
        remainder      == resource_count % member_count
        max_alloc      == IF remainder = 0 THEN min_alloc ELSE min_alloc + 1
        ideal_at_max   == IF remainder = 0 THEN member_count ELSE remainder
    IN RangeAssign(res, mbs, <<>>, max_alloc, ideal_at_max)

\* Round robin assignment
RECURSIVE RoundRobinAssign(_,_,_,_)
RoundRobinAssign(free_res, mbs_left, mbs_right, alloc1) ==
     IF Cardinality(free_res) = 0
     THEN alloc1
     ELSE
         LET r == CHOOSE r \in free_res : 
                    \A r1 \in free_res : r <= r1
             r_left == free_res \ {r}
             m == CHOOSE m \in mbs_left : 
                    \A m1 \in mbs_left : m <= m1
             mbs_left1 == mbs_left \ {m}
             mbs_right1 == mbs_right \union {m}
             alloc2 == IF m \in DOMAIN alloc1
                       THEN [alloc1 EXCEPT ![m] = @ \union {r}]
                       ELSE alloc1 @@ (m :> {r})
         IN IF mbs_left1 = {}
            THEN RoundRobinAssign(r_left, mbs_right1, mbs_left1, alloc2)
            ELSE RoundRobinAssign(r_left, mbs_left1, mbs_right1, alloc2)

CalculateRoundRobinAssignments(mbs, res, target_alloc) ==
    RoundRobinAssign(res, mbs, {}, <<>>)

\* Sticky assignment
FairSimple(mbs, alloc1, tolerance) ==
    ~\E m1, m2 \in mbs : 
        Cardinality(alloc1[m1]) - Cardinality(alloc1[m2]) > tolerance

FairDistance(res, mbs, alloc1, max_distance) ==
    /\ LET resource_count == Cardinality(res)
           member_count == Cardinality(mbs)
           min_alloc == resource_count \div member_count
           remainder ==  resource_count % member_count
           max_alloc == IF remainder = 0 THEN min_alloc ELSE min_alloc + 1
           ideal_at_max == IF remainder = 0 THEN member_count
                           ELSE remainder
           actual_at_max == Quantify(DOMAIN alloc1, LAMBDA m : 
                                Cardinality(alloc1[m]) >= max_alloc)                     
       IN /\ \A m \in mbs : 
            \/ Cardinality(alloc1[m]) < max_alloc
            \/ /\ Cardinality(alloc1[m]) = max_alloc
               /\ actual_at_max - ideal_at_max < max_distance

Fair(res, mbs, alloc1, limit, strat) ==
    CASE strat = "stickyfairsimple" ->
            FairSimple(mbs, alloc1, limit)
      [] OTHER ->
            FairDistance(res, mbs, alloc1, limit)

RECURSIVE StickyAssign(_,_,_,_,_,_,_)
StickyAssign(all_res, free_res, mbs, alloc1, limit, strat, revoked) ==
    IF Cardinality(free_res) = 0 
    THEN 
         \* there are no free resources so check if there
         \* is a resource that should be freed from an
         \* existing allocation, else allocation complete
         IF ~Fair(all_res, mbs, alloc1, limit, strat)
         THEN LET m == CHOOSE m1 \in mbs :
                            \A m2 \in mbs : 
                                Cardinality(alloc1[m1]) >= Cardinality(alloc1[m2])
                  freed == { CHOOSE r \in alloc1[m] : TRUE }
                  remaining == alloc1[m] \ freed
                  new_alloc == [alloc1 EXCEPT ![m] = remaining]
              IN StickyAssign(all_res, freed, mbs, new_alloc, limit, strat, revoked + 1)
         ELSE [assignment |-> alloc1, revoked |-> revoked]
    ELSE \* there are free resources, so choose the member with the
         \* least assigned resources and assign the resource to that member
         LET m == CHOOSE m \in mbs :
                    IF m \notin DOMAIN alloc1
                    THEN TRUE
                    ELSE \A m1 \in mbs :
                        \/ m1 = m
                        \/ IF m1 \notin DOMAIN alloc1
                           THEN FALSE
                           ELSE Cardinality(alloc1[m]) <= Cardinality(alloc1[m1])
             r == CHOOSE r \in free_res : TRUE
             rest ==  free_res \ {r}
             alloc2 == IF m \in DOMAIN alloc1
                       THEN [alloc1 EXCEPT ![m] = @ \union {r}]
                       ELSE alloc1 @@ (m :> {r})
         IN StickyAssign(all_res, rest, mbs, alloc2, limit, strat, revoked)

CalculateStickyAssignments(mbs, res, target_alloc, limit, strat) ==
    LET prep_alloc == [mid \in mbs |-> IF mid \in DOMAIN target_alloc
                                       THEN target_alloc[mid] \intersect res
                                       ELSE {}]
        free_res  == res \ UNION Range(prep_alloc)
        new_alloc == StickyAssign(res, free_res, mbs, prep_alloc, limit, strat, 0)
    IN new_alloc.assignment

CalculateDistance(mbs, res, target_alloc) ==
    LET prep_alloc == [mid \in mbs |-> IF mid \in DOMAIN target_alloc
                                       THEN target_alloc[mid] \intersect res
                                       ELSE {}]
        free_res  == res \ UNION Range(prep_alloc)
        new_alloc == StickyAssign(res, free_res, mbs, prep_alloc, 1, "stickyfairsimple", 0)
    IN new_alloc.revoked    

CalculateAssignments(member_ids, res, curr_assignment, strat, strat_param) ==
    IF member_ids = {}
    THEN <<>>
    ELSE CASE strat = "range" ->
            CalculateRangeAssignments(
                member_ids,
                res,
                curr_assignment)
        [] strat = "roundrobin" ->
            CalculateRoundRobinAssignments(
                member_ids,
                res,
                curr_assignment)
        [] OTHER ->
            IF \/ strat = "stickyfairsimple"
               \/ strat = "stickyfairdistance"
            THEN CalculateStickyAssignments(
                        member_ids,
                        res,
                        curr_assignment,
                        strat_param, 
                        strat)
            ELSE Nil \* Bad input, so crash


\* -------------------------------------------------
\* STATS
\* -------------------------------------------------

\* Create the CSV file
ASSUME 
    IOExec(
        <<"bash", "-c", "echo \"TS,Traces,Level,Revocations,Heartbeats,GroupEpoch,Distance,InitNumCts,InitNumCoordMbrs,InitNumRes,InitNumCoordRes,Strategy,StrategyParam,AddRes,RemRes\" > " \o CSVFile>>
        ).exitValue = 0 \* Fail fast if CSVFile was not created.

\* Various keys for TLCGet/Set        
RevocationsCtr == 1
HeartbeatsCtr == 2
DistanceCtr == 3
RunCtr == 4
LastPrinted == 5

\* The counters must be reset at the start of every behaviour
ResetCounters ==
    /\ TLCSet(RevocationsCtr, 0)
    /\ TLCSet(HeartbeatsCtr, 0)
    /\ TLCSet(DistanceCtr, 0)

\* Record a statistic value
RecordStat(key, count) ==
    TLCSet(key, TLCGet(key) + count)

\* Write the statistics to the CSV
PrintStats ==
    /\ PrintT(<<"stats", TLCGet("stats").traces, TLCGet(RunCtr)>>)
    /\ CSVWrite("%1$s,%2$s,%3$s,%4$s,%5$s,%6$s,%7$s,%8$s,%9$s,%10$s,%11$s,%12$s,%13$s,%14$s,%15$s",
                <<TLCGet("revision").timestamp,
                TLCGet("stats").traces, 
                TLCGet("level"), 
                TLCGet(RevocationsCtr),
                TLCGet(HeartbeatsCtr),
                coord_epochs.group,
                TLCGet(DistanceCtr),
                config.initClients,
                config.initAssignedClients,
                config.initResources,
                config.initAssignedResources,
                config.strategy,
                config.strategyParam,
                aux_add_client_ctr,
                aux_remove_client_ctr>>, CSVFile)
    /\ TLCSet(LastPrinted, TLCGet(RunCtr))

TerminationDetected ==
    /\ SetupComplete
    /\ TargetAssignmentReached
    /\ TLCGet(RunCtr) > TLCGet(LastPrinted)
    /\ aux_add_client_ctr >= MaxAddClients
    /\ aux_remove_client_ctr >= MaxRemoveClients
    /\ aux_add_resource_ctr >= MaxAddResources
    /\ aux_remove_resource_ctr >= MaxRemoveResources

\* Set this as an invariant. Once the behaviour
\* effective termination is detected, write out the stats to CSV.
AtTermination ==
    TerminationDetected => PrintStats    

\* Set as an invariant to debug or view state as it changes in a behaviour.
PrintLevel ==
    PrintT(<<TLCGet("level"), TargetAssignmentReached,
                aux_hb_ctr,
                client_pending_hb,
                client_member_epoch,
                coord_epochs,
                coord_member_epoch,
                coord_member_client,
                coord_target_assignment,
                client_assignment,
                coord_resource_state >>)

\* ----------------------------------------------
\* HELPERS
\* ----------------------------------------------
    
MaxInteger(i1, i2) ==
    IF i1 >= i2 THEN i1 ELSE i2

SendMultiple(msgs) ==
    /\ \A m \in msgs : m \notin DOMAIN messages
    /\ messages' = messages @@ [msg \in msgs |-> 1] 

Send(m) ==
    \/ /\ m \notin DOMAIN messages
       /\ messages' = messages @@ (m :> 1)
    \/ /\ m \in DOMAIN messages
       /\ messages' = [messages EXCEPT ![m] = @ + 1]
          
Reply(response, request) ==
    /\ messages[request] > 0 \* request must exist
    /\ \/ /\ response \notin DOMAIN messages \* response does not exist, so add it
          /\ messages' = [messages EXCEPT ![request] = @ - 1] @@ (response :> 1)
       \/ /\ response \in DOMAIN messages
          /\ messages' = [messages EXCEPT ![request] = @ - 1,
                                          ![response] = @ + 1]

Discard(m) ==
    /\ m \in DOMAIN messages
    /\ messages[m] > 0 \* message must exist
    /\ messages' = [messages EXCEPT ![m] = @ - 1]

SendHeartbeat(c, hb) ==
    /\ Send(hb)
    /\ aux_hb_ctr' = [aux_hb_ctr EXCEPT ![c] = @ + 1]
    /\ IF c \in DOMAIN client_pending_hb
       THEN client_pending_hb' = [client_pending_hb EXCEPT ![c] = FALSE]
       ELSE client_pending_hb' = client_pending_hb @@ (c :> FALSE)
    /\ RecordStat(HeartbeatsCtr, 1)

SendFirstHeartbeats(c_all, hbs) ==
    /\ SendMultiple(hbs)
    /\ aux_hb_ctr' = [c \in c_all |-> IF c \in DOMAIN aux_hb_ctr
                                      THEN aux_hb_ctr[c]
                                      ELSE Min(Range(aux_hb_ctr))]
    /\ client_pending_hb' = [c \in c_all |-> IF c \in DOMAIN client_pending_hb
                                      THEN client_pending_hb[c]
                                      ELSE FALSE]
    /\ RecordStat(HeartbeatsCtr, Cardinality(hbs))
    
ReplyWithHeartbeat(c, hb, m) ==
    /\ Reply(hb, m)
    /\ UNCHANGED aux_hb_ctr
    /\ client_pending_hb' = [client_pending_hb EXCEPT ![c] = FALSE]
    /\ RecordStat(HeartbeatsCtr, 1)    

NoReplyHeartbeat(c, m) ==
    /\ Discard(m)
    /\ client_pending_hb' = [client_pending_hb EXCEPT ![m.dest] = TRUE]
    /\ UNCHANGED aux_hb_ctr
    

\*------------------------------------------------------
\* ACTIONS  
\*------------------------------------------------------

\*------------------------------------------------------
\* Action: RestartClients
\* Restarts a number of clients. A restart is basically killing
\* one client and starting a new one. Equivalent of a StopClient
\* and StartClient in one action.
FirstHeartbeatRequest(c) ==
    [type       |-> HeartbeatRequest,
     epoch      |-> 0,
     assignment |-> {},
     member_id  |-> -1,
     source     |-> c]

RestartClients(num) ==
    /\ SetupComplete
    /\ TargetAssignmentReached
    /\ aux_add_client_ctr < MaxAddClients
    /\ aux_remove_client_ctr < MaxRemoveClients
    /\ \E c_old \in kSubset(num, clients) : 
        /\ LET  c_new == { aux_client_id + n :
                               n \in 1..num }
                new_clients == (clients \ c_old) \union c_new
           IN /\ clients' = new_clients
              /\ client_assignment' = [c \in new_clients |-> IF c \in DOMAIN client_assignment
                                                             THEN client_assignment[c] ELSE {}]
              /\ client_member_epoch' = [c \in new_clients |-> IF c \in DOMAIN client_member_epoch
                                                               THEN client_member_epoch[c] ELSE 0]
              /\ client_member_id' = [c \in new_clients |-> IF c \in DOMAIN client_member_id
                                                            THEN client_member_id[c] ELSE -1]
              /\ SendFirstHeartbeats(new_clients, 
                        {FirstHeartbeatRequest(c) : c \in c_new})
              /\ aux_client_id' = aux_client_id + num
              /\ aux_add_client_ctr' = aux_add_client_ctr + num
              /\ aux_remove_client_ctr' = aux_remove_client_ctr + num
    /\ UNCHANGED << resources, coordVars, aux_member_id, aux_add_resource_ctr, 
                    aux_remove_resource_ctr, config>>
    /\ StdOut("RestartClients")

\*------------------------------------------------------
\* Action: StartClient
\* Starts a new client which sends its first heartbeat
StartClient ==
    /\ SetupComplete
    /\ aux_add_client_ctr < MaxRemoveClients
    /\ LET c == aux_client_id + 1
       IN /\ clients' = clients \union {c}
          /\ client_assignment' = client_assignment @@ (c :> {})
          /\ client_member_epoch' = client_member_epoch @@ (c :> 0)
          /\ client_member_id' = client_member_id @@ (c :> -1)
          /\ SendHeartbeat(c, FirstHeartbeatRequest(c))
          /\ aux_client_id' = aux_client_id + 1
          /\ aux_add_client_ctr' = aux_add_client_ctr + 1
    /\ UNCHANGED << coordVars, config >>

\*------------------------------------------------------
\* Action: StopClient
\* Stops one random client by removing all its state.
StopClient ==
    /\ SetupComplete
    /\ \E c \in clients :
        /\ aux_remove_client_ctr < MaxRemoveClients
        /\ LET remaining == clients \ {c}
           IN /\ clients' = remaining
              /\ client_assignment' = [c1 \in remaining |-> client_assignment[c1]]
              /\ client_member_epoch' = [c1 \in remaining |-> client_member_epoch[c1]]
              /\ client_member_id' = [c1 \in remaining |-> client_member_id[c1]]
              /\ aux_remove_client_ctr' = aux_remove_client_ctr + 1
        /\ UNCHANGED <<>>

\*------------------------------------------------------
\* Action: AddResource
\* Adds a resource which the coordinator will become aware of.
AddResource ==
    /\ SetupComplete
    /\ aux_add_resource_ctr < MaxAddResources
    /\ LET r == Max(resources)
       IN resources' = resources \union {r}
    /\ aux_add_resource_ctr' = aux_add_resource_ctr + 1
    /\ UNCHANGED <<>>

\*------------------------------------------------------
\* Action: AddResource    
\* Removes the highest numbered resource (simulating partitions)    
\* TODO: allow for removing any arbitrary resources.
RemoveResource ==
    /\ SetupComplete
    /\ aux_remove_resource_ctr < MaxRemoveResources
    /\ Cardinality(resources) > 0
    /\ LET r == Max(resources)
       IN resources' = resources \ {r}
    /\ aux_remove_resource_ctr' = aux_remove_resource_ctr + 1
    /\ UNCHANGED <<>>    

\*------------------------------------------------------
\* Action: TimeoutLiveMember and TimeoutDeadMember
\* The coordinator timesout a member by removing all
\* its state and freeing any resources assigned to it.
TimeoutMember(mid) ==
     LET members == DOMAIN coord_member_epoch \ {mid}
     IN
         /\ coord_member_epoch' = [mid1 \in members |-> coord_member_epoch[mid1]]
         /\ coord_member_client' = [mid1 \in members |-> coord_member_client[mid1]]
         /\ coord_member_pending_hb_res' = [mid1 \in members |-> coord_member_pending_hb_res[mid1]]
         /\ coord_resource_state' = [r \in DOMAIN coord_resource_state |->
                                        LET rstate == coord_resource_state[r]
                                        IN
                                            IF rstate.member = mid
                                            THEN [rstate EXCEPT !.state = Free,
                                                                !.member = -1]
                                            ELSE rstate]
         /\ UNCHANGED << clients, resources, coord_target_assignment, coord_epochs, 
                         messages, clientVars, auxVars, config >>

TimeoutLiveMember ==
    /\ SetupComplete
    /\ \E mid \in DOMAIN coord_member_epoch :
        /\ \E c \in DOMAIN client_member_id : client_member_id[c] = mid 
        /\ TimeoutMember(mid)
        
TimeoutDeadMember ==
    /\ SetupComplete
    \* there is a member that the coordinator knows
    /\ \E mid \in DOMAIN coord_member_epoch :
        \* that no longer exists
        /\ ~\E c \in DOMAIN client_member_id : 
            c = coord_member_client[mid]
        \* FOR SIMULATION
        \* The coordinator timesout this member once
        \* all possible assignments are completed. This
        \* allows simulation to see the effect of a restarting
        \* client, where the new client joins causing reassignments
        \* followed by the timeout of the dead member causing
        \* another round of reassignments
        /\ LET expected == DOMAIN client_member_id
           IN 
                \* coordinator knows of all live clients
                /\ \A c \in expected : 
                    \E mid1 \in DOMAIN coord_member_client :
                        coord_member_client[mid1] = c
                \* current assignment includes all live clients
                /\ coord_epochs.members = DOMAIN coord_member_client
                /\ coord_epochs.group = coord_epochs.assignment
                \* all resources either still with dead member
                \* or now assigned to live member in group epoch
                \* i.e. further reassignments blocked until timeout.
                /\ \A r \in resources :
                    \/ coord_resource_state[r].member = mid
                    \/ r \in coord_target_assignment[mid]
                    \/ /\ coord_resource_state[r].member # mid
                       /\ coord_resource_state[r].state = Assigned
                       /\ coord_resource_state[r].epoch = coord_epochs.group   
        /\ TimeoutMember(mid)    
        /\ StdOut("TimeoutDeadMember")   

\*------------------------------------------------------
\* Action: SendNewMemberHeartbeatRequest
\* A client sends its first heartbeat. This actions can
\* occur when the initial state includes clients
\* that have not been preassigned according to a scenario.
SendNewMemberHeartbeatRequest ==
    /\ SetupComplete
    /\ \E c \in clients : 
        /\ client_member_epoch[c] = -1
        /\ client_member_epoch' = [client_member_epoch EXCEPT ![c] = 0]
        /\ SendHeartbeat(c, FirstHeartbeatRequest(c))
        /\ UNCHANGED << clients, resources, client_assignment, client_member_id,
                        coordVars, auxIds, auxCtrs, config >>
        /\ StdOut("SendNewMemberHeartbeatRequest")

\*------------------------------------------------------
\* Action: SendExistingMemberHeartbeatRequest
\* An existing member with a member id > 0 sends a heartbeat.
\* A member only sends when a heartbeat when:
\* - It is not waiting for a heartbeat response
\* - It does not violate "balanced progress".
\*
\* The idea of balanced progress is to prevent infinite 
\* cycles of a subset of clients sending heartbeats leaving 
\* another subset without any heartbeats at all, or the 
\* coordinator not doing things like installing new assignments. 
\* We have balanced progress if:
\* 1. The max difference in number of heartbeats sent 
\*    does not exceed MaxHbCountDiff.
\* 2. The coordinator does not need to:
\*     a) install a new target assignment.
\*     b) timeout a dead member
\* 3. The target assignment has not been reached. If it
\*    has then send no more heartbeats and let it terminate.

BalancedProgress(c) ==
    \* the client is due a heartbeat
    /\ client_pending_hb[c] = TRUE
    \* and it has sent a similar number of heartbeats to its peers
    /\ ~\E c1 \in clients :
        aux_hb_ctr[c] - aux_hb_ctr[c1] >= MaxHbCountDiff
    \* thet target assignment has not been achieved yet
    /\ ~TargetAssignmentReached
    \* no new target assignment is needed, else we could send heartbeats
    \* forever and never actually create the new target assignment
    /\ coord_epochs.resources = resources
    /\ coord_epochs.members = DOMAIN coord_member_epoch
    /\ coord_epochs.group = coord_epochs.assignment
    \* there is no dead member that needs timing out first
    /\ ~(ENABLED TimeoutDeadMember)

SendExistingMemberHeartbeatRequest ==
    /\ SetupComplete
    /\ \E c \in clients : 
        /\ client_member_id[c] # -1
        /\ BalancedProgress(c)
        /\ SendHeartbeat(c,
                [type       |-> HeartbeatRequest,
                 epoch      |-> client_member_epoch[c],
                 assignment |-> client_assignment[c],
                 member_id  |-> client_member_id[c],
                 source     |-> c])
        /\ UNCHANGED << clients, resources, client_assignment, client_member_id,
                        client_member_epoch, coordVars, auxIds, auxCtrs, config >>
        /\ StdOut(<<"SendExistingMemberHeartbeatRequest", c, client_assignment[c]>>)

\*------------------------------------------------------
\* Action: HandleNewMemberHeartbeatRequest
\* The coordinator receives a heartbeat from a new member. It
\* adds it to its state and assigns it a member id.
HandleNewMemberHeartbeatRequest ==
    /\ SetupComplete
    /\ \E m \in DOMAIN messages :
        /\ m.type = HeartbeatRequest
        /\ messages[m] > 0
        /\ m.member_id = -1
        /\ LET member_id == aux_member_id + 1
           IN /\ coord_member_epoch' = coord_member_epoch @@ (member_id :> 0)
              /\ coord_member_client' = coord_member_client @@ (member_id :> m.source)
              /\ coord_member_pending_hb_res' = coord_member_pending_hb_res @@ (member_id :> TRUE)
              /\ aux_member_id' = member_id
              /\ Discard(m)
        /\ UNCHANGED << clients, resources, clientVars, coord_target_assignment, 
                        coord_epochs, coord_resource_state, aux_client_id, 
                        auxCtrs, auxHb, config >>
        /\ StdOut("HandleNewMemberHeartbeatRequest")

\*------------------------------------------------------
\* Action: HandleExistingMemberHeartbeatRequest
\* The coordinator receives a heartbeat from an existing member.
\* It updates the resource state for any resources currently
\* assigned to the member.
HandleExistingMemberHeartbeatRequest ==
    /\ SetupComplete
    /\ \E m \in DOMAIN messages :
        /\ m.type = HeartbeatRequest
        /\ messages[m] > 0
        /\ m.member_id \in DOMAIN coord_member_epoch
        /\ coord_member_epoch' = [coord_member_epoch EXCEPT ![m.member_id] = m.epoch]
        /\ coord_resource_state' = [r \in resources |->
                                        LET rstate == coord_resource_state[r]
                                        IN
                                            IF rstate.member = m.member_id
                                            THEN 
                                                   CASE /\ rstate.state = Revoking 
                                                        /\ r \notin m.assignment
                                                        \* /\ rstate.epoch <= m.epoch 
                                                        ->
                                                            [rstate EXCEPT !.state = Free,
                                                                           !.member = -1]
                                                     [] /\ rstate.state = Assigning 
                                                        /\ r \in m.assignment
                                                        \* /\ rstate.epoch = m.epoch 
                                                            ->
                                                            [rstate EXCEPT !.state = Assigned]
                                                     [] /\ rstate.state = Assigned
                                                        /\ r \in m.assignment
                                                        \* /\ rstate.epoch = m.epoch 
                                                            ->
                                                            rstate
                                                     [] OTHER -> [rstate EXCEPT !.state = IllegalState]
                                             ELSE rstate]
        /\ coord_member_pending_hb_res' = [coord_member_pending_hb_res EXCEPT ![m.member_id] = TRUE]
        /\ Discard(m)
        /\ UNCHANGED << clients, resources, clientVars, coord_member_client, 
                        coord_target_assignment, coord_epochs, auxVars, config >>        
        /\ StdOut(<<"HandleExistingMemberHeartbeatRequest", m.source, m.assignment>>)

\*------------------------------------------------------
\* Action: IncrementGroupEpoch
\* The current resources and/or the current members have changed.
\* The coordinator increments the group epoch and records the members
\* resources at this new epoch.
IncrementGroupEpoch ==
    /\ SetupComplete
    /\ \E mid \in DOMAIN coord_member_epoch : TRUE \* coordinator knows of at least one member
    /\ \/ coord_epochs.resources # resources
       \/ coord_epochs.members # DOMAIN coord_member_epoch
    /\ coord_epochs' = [group      |-> coord_epochs.group + 1,
                        assignment |-> coord_epochs.assignment,
                        resources  |-> resources,
                        members    |-> DOMAIN coord_member_epoch]
    /\ UNCHANGED << clients, resources, coord_member_epoch, coord_member_client,
                    coord_member_pending_hb_res, 
                    coord_target_assignment, coord_resource_state,
                    clientVars, auxVars, messages, config >> 
    /\ StdOut("IncrementGroupEpoch")

\*------------------------------------------------------
\* Action: InstallNewTargetAssignment
\* The group epoch is greater than the assignment epoch and
\* so the coordinator installs a new target assignment.

InstallNewTargetAssignment ==
    /\ SetupComplete
    /\ coord_epochs.group > coord_epochs.assignment
    /\ LET member_ids     == DOMAIN coord_member_epoch
           new_assignment == CalculateAssignments(
                                member_ids,
                                resources,
                                coord_target_assignment,
                                config.strategy,
                                config.strategyParam)
          distance == CalculateDistance(
                                member_ids,
                                resources,
                                new_assignment)
       IN
          /\ coord_epochs' = [coord_epochs EXCEPT !.assignment = coord_epochs.group]                                                   
          /\ coord_target_assignment' = new_assignment
          /\ RecordStat(DistanceCtr, distance)
          /\ UNCHANGED << clients, resources, coord_member_epoch, coord_member_client,
                          coord_resource_state, coord_member_pending_hb_res, clientVars, 
                          auxVars, messages, config >>
          /\ StdOut("InstallNewTargetAssignment")

\*------------------------------------------------------
\* Action: SendHeartbeatResponseToRevoke
\* The coordinator sends a heartbeat response to a member that
\* should revoke a subset of its resources.
\* It updates the resource state accordingly.
Revoke(r, mid) == 
    /\ coord_resource_state[r].member = mid
    /\ r \notin coord_target_assignment[mid]

Keep(r, mid) == 
    /\ coord_resource_state[r].member = mid
    /\ r \in coord_target_assignment[mid]

IsFree(r) ==
    coord_resource_state[r].state = Free

SendHeartbeatResponseToRevoke ==
    /\ SetupComplete
    /\ \E mid \in DOMAIN coord_target_assignment :
        /\ mid \in DOMAIN coord_member_epoch \* could have timed out
        /\ coord_member_pending_hb_res[mid] = TRUE
        /\ \E r \in resources : 
            /\ coord_resource_state[r].member = mid
            /\ r \notin coord_target_assignment[mid]
        /\ RecordStat(RevocationsCtr, Quantify(resources, LAMBDA r : Revoke(r, mid)))
        /\ coord_member_pending_hb_res' = [coord_member_pending_hb_res EXCEPT ![mid] = FALSE]
        /\ LET \* when revoking resources, include only the resources of its existing assignment
               \* that are also in the target assignment
               assignment == {r \in resources : Keep(r, mid)}
               \* is this assignment its target?
               is_target  == assignment = coord_target_assignment[mid]
               \* if with this revocation the member reaches its target
               \* assignment then it can immediately switch to the new epoch
               \* else it remains on its current epoch as it will need another
               \* assignment once the revocation is complete.
               new_member_epoch == IF is_target
                                   THEN coord_epochs.assignment
                                   ELSE coord_member_epoch[mid]
           IN
                /\ coord_resource_state' = [r \in resources |->
                                                LET rstate == coord_resource_state[r]
                                                IN 
                                                    CASE Revoke(r, mid) ->
                                                             [rstate EXCEPT !.state = Revoking]
                                                      [] Keep(r, mid) ->
                                                             [rstate EXCEPT !.epoch = coord_epochs.assignment]
                                                      [] OTHER -> coord_resource_state[r]]
                /\ Send([type       |-> HeartbeatResponse,
                         epoch      |-> new_member_epoch,
                         assignment |-> assignment,
                         member_id  |-> mid,
                         dest       |-> coord_member_client[mid]])
                /\ UNCHANGED << clients, resources, coord_member_epoch, coord_member_client,
                                coord_target_assignment, coord_epochs, clientVars, auxVars, config >>
                /\ StdOut(<<"SendHeartbeatResponseToRevoke", coord_member_client[mid], assignment,
                            new_member_epoch, client_member_epoch[coord_member_client[mid]]>>)

\*------------------------------------------------------
\* Action: SendHeartbeatResponseAssignmentOnly
\* The coordinator sends a heartbeat response to a member
\* that does not need to revoke any resources.
ResourceAssigned(rstate, mid, epoch) ==
    /\ rstate.member = mid
    /\ rstate.epoch = epoch
    /\ rstate.state = Assigned

SendHeartbeatResponseAssignmentOnly ==
    /\ SetupComplete
    /\ \E mid \in DOMAIN coord_target_assignment :
        /\ mid \in DOMAIN coord_member_epoch \* could have timed out
        \* pending send of heartbeat response
        /\ coord_member_pending_hb_res[mid] = TRUE
        \* no resources need to be revoked
        /\ ~\E r \in resources : 
            /\ coord_resource_state[r].member = mid
            /\ r \notin coord_target_assignment[mid]
        /\ LET \* The assignable resources in this moment. Some of its target
               \* resources may still be assigned to another member still.
               assignable == { r \in coord_target_assignment[mid] :
                                \/ Keep(r, mid)
                                \/ IsFree(r) }
               \* The member epoch can advance to the assignment epoch if the 
               \* assignable resources match its target assignment, else it
               \* remains on its current epoch for now.
               new_member_epoch == IF Cardinality(assignable) = Cardinality(coord_target_assignment[mid])
                                    THEN coord_epochs.assignment
                                    ELSE coord_member_epoch[mid]
           IN        
                /\ coord_resource_state' = [r \in resources |-> 
                                                LET rstate == coord_resource_state[r]
                                                IN
                                                    IF /\ r \in assignable
                                                       /\ ~ResourceAssigned(rstate, mid, coord_epochs.assignment)  
                                                    THEN [rstate EXCEPT !.state  = Assigning,
                                                                        !.epoch  = coord_epochs.assignment,
                                                                        !.member = mid]
                                                    ELSE coord_resource_state[r]]
                /\ coord_member_pending_hb_res' = [coord_member_pending_hb_res EXCEPT ![mid] = FALSE]
                /\ Send([type       |-> HeartbeatResponse,
                         epoch      |-> new_member_epoch,
                         assignment |-> assignable,
                         member_id  |-> mid,
                         dest       |-> coord_member_client[mid]])
                /\ UNCHANGED << clients, resources, coord_member_epoch, coord_member_client,
                                coord_target_assignment, coord_epochs, clientVars, auxVars, config >>
                /\ StdOut(<<"SendHeartbeatResponseAssignmentOnly", coord_member_client[mid], assignable>>)

\*------------------------------------------------------
\* Action: HandleHeartbeatResponse
\* A client receives a heartbeat response. If the response
\* has a different assignment or epoch then the client
\* sends a new heartbeat immediately.
RequiresImmediateReply(m) ==
    \/ client_member_epoch[m.dest] # m.epoch
    \/ client_assignment[m.dest] # m.assignment

HandleHeartbeatResponse ==
    /\ SetupComplete
    /\ \E m \in DOMAIN messages :
        /\ m.type = HeartbeatResponse
        /\ messages[m] > 0
        /\ m.dest \in DOMAIN client_member_epoch
        /\ m.epoch >= client_member_epoch[m.dest]
        /\ client_assignment' = [client_assignment EXCEPT ![m.dest] = m.assignment]
        /\ client_member_epoch' = [client_member_epoch EXCEPT ![m.dest] = m.epoch]
        /\ IF client_member_id[m.dest] = -1
           THEN client_member_id' = [client_member_id EXCEPT ![m.dest] = m.member_id]
           ELSE UNCHANGED client_member_id
        /\ IF RequiresImmediateReply(m)
           THEN ReplyWithHeartbeat(m.dest,
                     [type       |-> HeartbeatRequest,
                      source     |-> m.dest,
                      assignment |-> m.assignment,
                      member_id  |-> m.member_id,
                      epoch      |-> m.epoch], m)
           ELSE NoReplyHeartbeat(m.dest, m)
        /\ UNCHANGED << clients, resources, coordVars, auxIds, auxCtrs, config >>
        /\ StdOut(<<"HandleHeartbeatResponse", m.dest, m.assignment, 
                     m.epoch, RequiresImmediateReply(m)>>)

\*------------------------------------------------------
\* Action: Setup
\* Due to a strange bug in TLC, we cannot use the recursive
\* assignment action to see the client_assignment and
\* coord_resource_state variables. So the Init formula is
\* split into Init and Setup.
\* TODO: Figure out what is going on with this bug.
NoAssignments(cts) ==
    [c \in cts |-> {}]    

Setup ==
    /\ ~SetupComplete
    /\ client_assignment' = [c \in clients |->
                                IF c \in DOMAIN coord_target_assignment
                                THEN coord_target_assignment[c]
                                ELSE {}]
    /\ coord_resource_state' = [r \in resources |->
                                IF r \in DOMAIN coord_resource_state
                                THEN [state |-> Assigned,
                                        epoch |-> 1,
                                        member |-> CHOOSE mid \in DOMAIN coord_target_assignment :
                                                        r \in coord_target_assignment[mid]]
                                ELSE [state  |-> Free,
                                        epoch  |-> 0,
                                        member |-> -1]]
    /\ RecordStat(RunCtr, 1)
    /\ ResetCounters
    /\ UNCHANGED << resources, clients, messages, auxVars,
                    client_member_epoch, client_member_id, client_pending_hb,
                    coord_member_epoch, coord_member_client,
                    coord_member_pending_hb_res,
                    coord_target_assignment, coord_epochs, config >>
    /\ StdOut("Setup")

\* Terminate ==
\*     /\ 
\*     /\ LET member_ids == DOMAIN coord_member_epoch
\*            distance   == CalculateDistance(
\*                                 member_ids,
\*                                 resources,
\*                                 coord_target_assignment)
       

\*------------------------------------------------------
\* Action: Init and Next
\*------------------------------------------------------

InitVars(initClients, initClientsAssigned, initResources, initResourcesAssigned,
         assignmentStrategy, strategyParam, initAssignments) ==
    /\ clients = initClients
    /\ client_assignment = <<>>
    /\ client_member_epoch = [c \in initClients |-> 
                                IF c \in initClientsAssigned
                                THEN 1
                                ELSE -1]
    /\ client_member_id = [c \in initClients |-> 
                                IF c \in initClientsAssigned
                                THEN c
                                ELSE -1]
    /\ client_pending_hb = [c \in initClients |-> TRUE]
    /\ resources = initResources
    /\ coord_member_epoch = [mid \in initClientsAssigned |-> 1]
    /\ coord_member_client = [mid \in initClientsAssigned |-> mid]
    /\ coord_member_pending_hb_res = [mid \in initClientsAssigned |-> FALSE]
    /\ coord_target_assignment = [mid \in initClientsAssigned |->
                                        initAssignments[mid]]
    /\ coord_resource_state = [r \in initResources |->
                                    [state  |-> Free,
                                        epoch  |-> 0,
                                        member |-> -1]]
    /\ coord_epochs = [group      |-> 1,
                       assignment |-> 1,
                       resources  |-> initResources,
                       members    |-> initClientsAssigned]
    /\ aux_client_id = Max(initClients)
    /\ aux_member_id = Max(initClientsAssigned)
    /\ aux_add_client_ctr = 0
    /\ aux_remove_client_ctr = 0
    /\ aux_add_resource_ctr = 0
    /\ aux_remove_resource_ctr = 0
    /\ aux_hb_ctr = [c \in initClients |-> 0] 
    /\ messages = <<>>  
    /\ config = [initClients           |-> Cardinality(initClients),
                 initAssignedClients   |-> Cardinality(initClientsAssigned),
                 initResources         |-> Cardinality(initResources),
                 initAssignedResources |-> Cardinality(initResourcesAssigned),
                 strategy              |-> assignmentStrategy,
                 strategyParam         |-> strategyParam]
    /\ ResetCounters
    /\ TLCSet(RunCtr, 0)  
    /\ TLCSet(LastPrinted, 0) 

InitOneConfig ==
    LET initClients   == 1..InitNumClients
        initResources == 1..InitNumResources
        initClientsAssigned == 1..InitNumCoordMembers
        initResourcesAssigned == 1..InitNumCoordResources
        initAssignments   == CalculateAssignments(initClientsAssigned, 
                                                  initResourcesAssigned,
                                                  NoAssignments(initClientsAssigned),
                                                  AssignmentStrategy,
                                                  StickyFairLimit)
    IN  InitVars(initClients, initClientsAssigned,
                 initResources, initResourcesAssigned,
                 AssignmentStrategy, StickyFairLimit, initAssignments)

StickyParams(strat, numResources) ==
    CASE strat = "stickyfairsimple" -> 1..MaxInteger(1, Min({5, numResources \div 10}))
      [] strat = "stickyfairdistance" -> 1..MaxInteger(1, Min({10, numResources \div 5}))
      [] OTHER -> {0} 

InitStableManyConfigs ==
    \E numResources \in 5..InitNumResources :
        \E numClients \in 2..numResources :
            \E strat \in {"range", "roundrobin", "stickyfairsimple", "stickyfairdistance"} :
                \E stickyPm \in StickyParams(strat, numResources) :
                    LET initClients   == 1..numClients
                        initResources == 1..numResources
                        initClientsAssigned == 1..numClients
                        initResourcesAssigned == 1..numResources
                        initAssignments   == CalculateAssignments(initClientsAssigned, 
                                                                  initResourcesAssigned,
                                                                  NoAssignments(initClientsAssigned),
                                                                  strat,
                                                                  stickyPm)
                    IN  InitVars(initClients, initClientsAssigned,
                                 initResources, initResourcesAssigned,
                                 strat, stickyPm, initAssignments)

Next ==
    \/ Setup
    \* changes to clients and resource counts
    \/ RestartClients(1)
    \* protocol
    \/ SendNewMemberHeartbeatRequest
    \/ SendExistingMemberHeartbeatRequest
    \/ HandleNewMemberHeartbeatRequest
    \/ HandleExistingMemberHeartbeatRequest
    \/ IncrementGroupEpoch
    \/ InstallNewTargetAssignment
    \/ SendHeartbeatResponseToRevoke
    \/ SendHeartbeatResponseAssignmentOnly
    \/ HandleHeartbeatResponse
    \/ TimeoutDeadMember
    
NoStuttering ==
    WF_vars(Next)

Spec == InitOneConfig /\ [][Next]_vars
LivenessSpec == InitOneConfig /\ [][Next]_vars /\ NoStuttering
SimRestartsSpec == InitStableManyConfigs /\ [][Next]_vars /\ NoStuttering

\* ------------------------------------------------
\* LIVENESS
\* ------------------------------------------------

\* Liveness: RebalanceCompletes
AllEpochsMatch ==
    IF DOMAIN coord_member_epoch = {}
    THEN TRUE
    ELSE
            /\ coord_epochs.group = coord_epochs.assignment
            /\ \A mid \in DOMAIN coord_member_epoch :
                coord_member_epoch[mid] = coord_epochs.group

RebalanceCompletes ==
    []<>AllEpochsMatch

\* ------------------------------------------------
\* INVARIANTS    
\* ------------------------------------------------

\* INV: TypeOK
AllClients ==
    1..aux_client_id
    
AllMemberIds ==
    1..aux_member_id    
    
AllResources ==
    LET maxResource == MaxInteger(InitNumResources, InitNumCoordResources)
                       + MaxAddResources
    IN 1..maxResource
    
TypeOK ==
    /\ client_assignment \in [DOMAIN client_assignment -> SUBSET AllResources]
    /\ client_member_epoch \in [DOMAIN client_member_epoch -> {-1} \union Nat]
    /\ client_member_id \in [DOMAIN client_member_id -> {-1} \union Nat]
    /\ coord_member_epoch \in [DOMAIN coord_member_epoch -> Nat]
    /\ coord_member_client \in [DOMAIN coord_member_client -> AllClients]
    /\ coord_target_assignment \in [DOMAIN coord_target_assignment -> SUBSET AllResources]
    /\ coord_member_pending_hb_res \in [DOMAIN coord_member_pending_hb_res -> BOOLEAN]
    /\ coord_epochs \in [group: Nat,
                         assignment: Nat, 
                         resources: SUBSET AllResources,
                         members: SUBSET AllMemberIds]
    /\ coord_resource_state \in [resources -> [state: {Free, Revoking, Assigning, Assigned, IllegalState},
                                               epoch: Nat,
                                               member: {-1} \union Nat]]
    /\ aux_member_id \in Nat

\* INV: NoDoubleAssignedResource
\* Note that this can happen when using the TimeoutLiveMember action.
NoDoubleAssignedResource ==
    IF SetupComplete
    THEN  ~\E r \in resources :
            \E c1, c2 \in clients :
                /\ c1 # c2
                /\ r \in client_assignment[c1]
                /\ r \in client_assignment[c2]
                /\ client_member_id[c1] \in DOMAIN coord_member_epoch
                /\ client_member_id[c2] \in DOMAIN coord_member_epoch
    ELSE TRUE

\* INV: ConsistentView
\* If the epoch of a member matches the assignment epoch then then
\* the clients resources should match its target assignment
ConsistentView ==
    IF SetupComplete
    THEN \A c \in DOMAIN client_assignment :
            IF /\ client_member_id[c] # -1
               /\ client_member_epoch[c] = coord_epochs.assignment
            THEN client_assignment[c] = coord_target_assignment[client_member_id[c]]
            ELSE TRUE
    ELSE TRUE

\* INV: NoIllegalState
\* No resource should enter an illegal state. This can happen
\* if a heartbeat request is received that it inconsistent with
\* the current state of the resource on the coordinator.
NoIllegalState ==
    \A r \in resources :
        coord_resource_state[r].state # IllegalState    
    
TestInv ==
    TLCGet("level") < 10000
    
=============================================================================
\* Modification History
\* Last modified Tue Aug 09 10:16:41 CEST 2022 by GUNMETAL
\* Created Fri Jul 29 15:08:32 CEST 2022 by GUNMETAL
