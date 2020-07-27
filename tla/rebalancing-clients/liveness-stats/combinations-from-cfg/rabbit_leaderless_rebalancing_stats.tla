------------------- MODULE rabbit_leaderless_rebalancing_stats -------------------
EXTENDS TLC, Sequences, Integers, FiniteSets, Naturals

CONSTANTS Q,                  \* set of all sets of queues
          A,                  \* set of all sets of apps
          RESTART_LIMIT

VARIABLES app,                \* the set of all applications of any given behaviour
          queue,              \* the set of all queues of any given behaviour
          subscriber_queue,   \* the First Subscribe, First Active ordering of each queue
          active,             \* the active consumer of each queue
          app_id,             \* the id of each app, required for determinism in releases
          id,                 \* for assigning each id
          \* statistics data
          per_queue_releases, \* number of releases per queue counter
          total_releases      \* total number of releases

vars == << queue, app, subscriber_queue, active, app_id, id, per_queue_releases, total_releases >>

(***************************************************************************)
(* Initial states                                                          *) 
(***************************************************************************)

Init ==
    /\ app \in A
    /\ queue \in Q
    /\ subscriber_queue = [q \in queue |-> <<>>]
    /\ active = [q \in queue |-> 0]
    /\ app_id = [a \in app |-> 0]
    /\ id = 1
    /\ per_queue_releases = [q \in queue |-> 0]
    /\ total_releases = 0

(***************************************************************************)
(* Actions and state formulae                                              *) 
(***************************************************************************)
    
StartedApps ==
    { a \in app : app_id[a] # 0 }

\* A stopped app_id starts and is assigned an id
Start(a) ==
    \* enabling conditions 
    /\ app_id[a] = 0
    \* actions
    /\ app_id' = [app_id EXCEPT ![a] = id]
    /\ id' = id + 1
    /\ UNCHANGED << app, queue, subscriber_queue, active, per_queue_releases, total_releases >>

Stop(a) ==
    \* enabling conditions
    /\ app_id[a] # 0
    /\ id < Cardinality(app) + RESTART_LIMIT
    \* actions
    /\ subscriber_queue' = [q \in queue |-> SelectSeq(subscriber_queue[q], LAMBDA a1: a1 # a)]
    /\ active' = [q \in queue |-> IF active[q] = a THEN 0 ELSE active[q]] 
    /\ app_id' = [app_id EXCEPT ![a] = 0]
    /\ UNCHANGED << app, queue, id, per_queue_releases, total_releases >>

AppInSubscribeQueue(a, q) ==
    \E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a

\* If an app is not subscribed to a queue, then subscribe
\* This action is used when we want to verify with random subscribe ordering
SubscribeToOneQueue(a, q) ==
    \* enabling conditions 
    /\ ~\E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a
    /\ active[q] # a
    \* actions
    /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = Append(@, a)]
    /\ UNCHANGED << app, queue, active, app_id, id, per_queue_releases, total_releases >>

\* An app that is not subscribed on one or more queues, subscribes to all those queues it is missing
\* This action is used when we want to verify with sequential subscribe ordering    
SubscribeToAllQueues(a) ==
    \* enabling conditions
    /\ \E q \in queue :
        /\ ~AppInSubscribeQueue(a, q)
        /\ active[q] # a
    \* actions
    /\ subscriber_queue' = [q \in queue |->
            IF ~AppInSubscribeQueue(a, q) THEN
                Append(subscriber_queue[q], a)
            ELSE
                subscriber_queue[q]]
    /\ UNCHANGED << app, queue, active, app_id, id, per_queue_releases, total_releases >>

\* The number of active consumers the application (a) has
AppActiveCount(a) ==
    Cardinality({ q \in queue : active[q] = a})


\* The position in the list of apps with active consumers, in reverse order, then by id
\* Required in order for each app to deterministically make the same decision about when to release a queue
Position(a) ==
    IF AppActiveCount(a) = 0 THEN -1
    ELSE
        Cardinality({ 
            a1 \in StartedApps :
                LET a_active == AppActiveCount(a)
                    a1_active == AppActiveCount(a1)
                IN
                    /\ a # a1
                    /\ a1_active > 0
                    /\ \/ a1_active >= a_active
                       \/ /\ a1_active = a_active
                          /\ app_id[a] < app_id[a1]
                
        })

SubscribedApplications ==
    { a \in app : 
        \E q \in queue : 
            \/ active[q] = a 
            \/ \E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a
    }

\* Calculates the ideal number of active consumers this application should have
IdealNumber(a) ==
    LET queue_count == Cardinality(queue)
        app_count == Cardinality(SubscribedApplications)
    IN
        IF app_count = 0 THEN 0
        ELSE
            LET ideal == queue_count \div app_count
                remainder ==  queue_count % app_count
                position == Position(a)
            IN
                IF remainder = 0 THEN ideal
                ELSE
                    IF remainder >= position + 1 THEN
                        ideal + 1
                    ELSE
                        ideal 

\* Releases one queue if it has too many active consumers
Release(a, q) ==
    \* enabling conditions 
    /\ active[q] = a
    /\ AppActiveCount(a) > IdealNumber(a) 
    \* actions
    /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = SelectSeq(@, LAMBDA a1: a1 # a)]
    /\ per_queue_releases' = [per_queue_releases EXCEPT ![q] = @ + 1]
    /\ total_releases' = total_releases + 1
    /\ \/ /\ active[q] = a
          /\ active' = [active EXCEPT ![q] = 0]
       \/ /\ active[q] # a
          /\ UNCHANGED active
    /\ UNCHANGED << app, queue, app_id, id >>

\* The SAC queue assigns active status to the next consumer in the subscriber queue
MakeActive(a, q) ==
    \* enabling conditions 
    /\ Cardinality(DOMAIN subscriber_queue[q]) > 0 
    /\ Head(subscriber_queue[q]) = a
    /\ active[q] = 0
    \* actions
    /\ active' = [active EXCEPT ![q] = a]
    /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = SelectSeq(@, LAMBDA a1: a1 # a)]
    /\ UNCHANGED << app, queue, app_id, id, per_queue_releases, total_releases >>

RandomNext ==
    \E a \in app :
        \/ Start(a)
        \/ Stop(a)
        \/ \E q \in queue :
            \/ SubscribeToOneQueue(a, q)
            \/ Release(a, q)
            \/ MakeActive(a, q)

SequentialNext ==
    \E a \in app :
        \/ Start(a)
        \/ Stop(a)
        \/ SubscribeToAllQueues(a)
        \/ \E q \in queue :
            \/ Release(a, q)
            \/ MakeActive(a, q)
        

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

\* True when:
\* - every queue has an active consumer
\* - every application is started
\* - every application has its number of active consumers <= the ideal number
\* (the ideal number can be 1 higher than it actually gets)
IsBalanced ==
    /\ \A q \in queue : active[q] # 0
    /\ \A a1, a2 \in app : 
        /\ app_id[a1] # 0
        /\ app_id[a2] # 0
        /\ AppActiveCount(a1) - AppActiveCount(a2) \in { -1, 0, 1}
         
\* True when every application has a consumer on every queue
\* (either as the active consumer or in the queue's subscriber queue)
AllAppsSubscribedOnAllQueues ==
    \A a \in app : 
        \A q \in queue : 
            \/ active[q] = a 
            \/ \E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a
    
RandomPostCondition == 
    IF (~ ENABLED RandomNext) THEN
        /\ AllAppsSubscribedOnAllQueues
        /\ IsBalanced
        /\ \A q \in queue :
            /\ Print("per_queue_releases," \o ToString(per_queue_releases[q]) \o "," \o ToString(Cardinality(app)) \o "," \o ToString(Cardinality(queue)), TRUE)
        /\ Print("total_releases," \o ToString(total_releases) \o "," \o ToString(Cardinality(app)) \o "," \o ToString(Cardinality(queue)), TRUE)
    ELSE
        id \in Nat

SequentialPostCondition == 
    IF (~ ENABLED SequentialNext) THEN
        /\ AllAppsSubscribedOnAllQueues
        /\ IsBalanced
        /\ \A q \in queue :
            /\ Print("per_queue_releases," \o ToString(per_queue_releases[q]) \o "," \o ToString(Cardinality(app)) \o "," \o ToString(Cardinality(queue)), TRUE)
        /\ Print("total_releases," \o ToString(total_releases) \o "," \o ToString(Cardinality(app)) \o "," \o ToString(Cardinality(queue)), TRUE)
    ELSE
        id \in Nat

AppOrNone ==
    app \union { 0 }

TypeOK ==
    /\ subscriber_queue \in [queue -> Seq(app)]
    /\ active \in [queue -> AppOrNone]
    /\ app_id \in [app -> Nat]
    /\ id \in Nat

(***************************************************************************)
(* Specs                                                                    *)
(***************************************************************************)

RandomSpec == Init /\ [][RandomNext]_vars /\ WF_vars(RandomNext) /\ []RandomPostCondition
SequentialSpec == Init /\ [][SequentialNext]_vars /\ WF_vars(SequentialNext)/\ []SequentialPostCondition

=============================================================================
\* Modification History
\* Last modified Mon Jul 27 11:24:29 CEST 2020 by GUNMETAL
