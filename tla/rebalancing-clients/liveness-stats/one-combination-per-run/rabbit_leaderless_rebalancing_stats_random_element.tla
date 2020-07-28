------------------- MODULE rabbit_leaderless_rebalancing_stats_random_element -------------------
EXTENDS TLC, Sequences, Integers, FiniteSets, Naturals

CONSTANTS Q,                  \* set of all queues
          A,                  \* set of all apps
          RESTART_LIMIT

VARIABLES subscriber_queue,   \* the First Subscribe, First Active ordering of each queue
          active,             \* the active consumer of each queue
          app_id,             \* the id of each app, required for determinism in releases
          id,                 \* for assigning each id
          \* statistics data
          per_queue_releases, \* number of releases per queue counter
          total_releases      \* total number of releases

vars == << subscriber_queue, active, app_id, id, per_queue_releases, total_releases >>

(***************************************************************************)
(* Initial states                                                          *) 
(***************************************************************************)

Init ==
    /\ subscriber_queue = [q \in Q |-> <<>>]
    /\ active = [q \in Q |-> 0]
    /\ app_id = [a \in A |-> 0]
    /\ id = 1
    /\ per_queue_releases = [q \in Q |-> 0]
    /\ total_releases = 0

(***************************************************************************)
(* Actions and state formulae                                              *) 
(***************************************************************************)
    
StartedApps ==
    { a \in A : app_id[a] # 0 }

\* A stopped app_id starts and is assigned an id
Startable(a) == app_id[a] = 0

Start(a) ==
    \* enabling conditions 
    /\ Startable(a)
    \* actions
    /\ app_id' = [app_id EXCEPT ![a] = id]
    /\ id' = id + 1
    /\ UNCHANGED << subscriber_queue, active, per_queue_releases, total_releases >>

Stoppable(a) ==
    /\ app_id[a] # 0
    /\ id < Cardinality(A) + RESTART_LIMIT

Stop(a) ==
    \* enabling conditions
    /\ Stoppable(a)
    \* actions
    /\ subscriber_queue' = [q \in Q |-> SelectSeq(subscriber_queue[q], LAMBDA a1: a1 # a)]
    /\ active' = [q \in Q |-> IF active[q] = a THEN 0 ELSE active[q]] 
    /\ app_id' = [app_id EXCEPT ![a] = 0]
    /\ UNCHANGED << id, per_queue_releases, total_releases >>

AppInSubscribeQueue(a, q) ==
    \E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a

\* If an app is not subscribed to a queue, then subscribe
\* This action is used when we want to verify with random subscribe ordering
Subscribeable(a, q) ==
    /\ \/ subscriber_queue[q] = <<>>
       \/ ~\E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a
    /\ active[q] # a

SubscribeToOneQueue(a, q) ==
    \* enabling conditions 
    /\ Subscribeable(a, q)
    \* actions
    /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = Append(@, a)]
    /\ UNCHANGED << active, app_id, id, per_queue_releases, total_releases >>

\* An app that is not subscribed on one or more queues, subscribes to all those queues it is missing
\* This action is used when we want to verify with sequential subscribe ordering    
SubscribeToAllQueues(a) ==
    \* enabling conditions
    /\ \E q \in Q :
        Subscribeable(a, q)
    \* actions
    /\ subscriber_queue' = [q \in Q |->
            IF ~AppInSubscribeQueue(a, q) THEN
                Append(subscriber_queue[q], a)
            ELSE
                subscriber_queue[q]]
    /\ UNCHANGED << active, app_id, id, per_queue_releases, total_releases >>

\* The number of active consumers the application (a) has
AppActiveCount(a) ==
    Cardinality({ q \in Q : active[q] = a})


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
    { a \in A : 
        \E q \in Q : 
            \/ active[q] = a 
            \/ \E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a
    }

\* Calculates the ideal number of active consumers this application should have
IdealNumber(a) ==
    LET queue_count == Cardinality(Q)
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
Releasable(a, q) ==
    /\ active[q] = a
    /\ AppActiveCount(a) > IdealNumber(a) 

Release(a, q) ==
    \* enabling conditions 
    /\ Releasable(a, q)
    \* actions
    /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = SelectSeq(@, LAMBDA a1: a1 # a)]
    /\ per_queue_releases' = [per_queue_releases EXCEPT ![q] = @ + 1]
    /\ total_releases' = total_releases + 1
    /\ \/ /\ active[q] = a
          /\ active' = [active EXCEPT ![q] = 0]
       \/ /\ active[q] # a
          /\ UNCHANGED active
    /\ UNCHANGED << app_id, id >>

\* The SAC queue assigns active status to the next consumer in the subscriber queue
Activatable(a, q) ==
    /\ Cardinality(DOMAIN subscriber_queue[q]) > 0 
    /\ Head(subscriber_queue[q]) = a
    /\ active[q] = 0

MakeActive(a, q) ==
    \* enabling conditions 
    /\ Activatable(a, q)
    \* actions
    /\ active' = [active EXCEPT ![q] = a]
    /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = SelectSeq(@, LAMBDA a1: a1 # a)]
    /\ UNCHANGED << app_id, id, per_queue_releases, total_releases >>

StartableApps ==
    { a \in A : Startable(a) } 

StoppableApps ==
    { a \in A : Stoppable(a)  } 

SubscribeableApps ==
    { a \in A : \E q \in Q : Subscribeable(a, q) }

SubscribeableQueues(a) ==
    { q \in Q : Subscribeable(a, q) }

ReleasableApps ==
    { a \in A : \E q \in Q : Releasable(a, q) }

ReleasableQueues(a) ==
    { q \in Q : Releasable(a, q) }

ActivatableApps ==
    { a \in A : \E q \in Q : Activatable(a, q) }

ActivatableQueues(a) ==
    { q \in Q : Activatable(a, q) }

NextEnabled ==
    \/ StartableApps # {}
    \/ StoppableApps # {}
    \/ SubscribeableApps # {}
    \/ ReleasableApps # {}
    \/ ActivatableApps # {}

\* With RandomElement to avoid non-determinism, but distribution favours low state spaces
\* TODO: Investigate why
(*
NonDeterministicStart ==
    LET apps == StartableApps
    IN 
        /\ apps # {}
        /\ Start(RandomElement(apps))

NonDeterministicStop ==
    LET apps == StoppableApps
    IN 
        /\ apps # {}
        /\ Stop(RandomElement(apps))
       
NonDeterministicSubscribe ==
    LET apps == SubscribeableApps
    IN 
        /\ apps # {}
        /\ LET a == RandomElement(apps)
           IN SubscribeToOneQueue(a, RandomElement(SubscribeableQueues(a)))

NonDeterministicRelease ==
    LET apps == ReleasableApps
    IN 
        /\ apps # {}
        /\ LET a == RandomElement(apps)
           IN Release(a, RandomElement(ReleasableQueues(a)))

NonDeterministicMakeActive ==
    LET apps == ActivatableApps
    IN 
        /\ apps # {}
        /\ LET a == RandomElement(apps)
           IN MakeActive(a, RandomElement(ActivatableQueues(a)))
*)

NonDeterministicStart ==
    /\ StartableApps # {}
    /\ Start(RandomElement(StartableApps))

NonDeterministicStop ==
    /\ StoppableApps # {}
    /\ Stop(RandomElement(StoppableApps))
       
NonDeterministicSubscribe ==
    /\ SubscribeableApps # {}
    /\ LET a == RandomElement(SubscribeableApps)
       IN SubscribeToOneQueue(a, RandomElement(SubscribeableQueues(a)))

NonDeterministicRelease ==
    /\ ReleasableApps # {}
    /\ LET a == RandomElement(ReleasableApps)
       IN Release(a, RandomElement(ReleasableQueues(a)))

NonDeterministicMakeActive ==
    /\ ActivatableApps # {}
    /\ LET a == RandomElement(ActivatableApps)
       IN MakeActive(a, RandomElement(ActivatableQueues(a)))

\* True when every application has a consumer on every queue
\* (either as the active consumer or in the queue's subscriber queue)
AllAppsSubscribedOnAllQueues ==
    \A a \in A : 
        \A q \in Q : 
            \/ active[q] = a 
            \/ /\ subscriber_queue[q] # <<>>
               /\ \E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a

RandomNext ==
    \/ NonDeterministicStart
    \/ NonDeterministicStop
    \/ NonDeterministicSubscribe
    \/ /\ AllAppsSubscribedOnAllQueues
       /\ \/ NonDeterministicRelease
          \/ NonDeterministicMakeActive

\* The original - works but is VERY slow for large state spaces due to non-determinism
(*
RandomNext ==
    \E a \in A :
        \/ Start(a)
        \/ Stop(a)
        \/ SubscribeToOneQueue(a, q)
        \/ /\ AllAppsSubscribedOnAllQueues
           /\ \/ Release(a, q)
              \/ MakeActive(a, q)
*)

SequentialNext ==
    \E a \in A :
        \/ Start(a)
        \/ Stop(a)
        \/ SubscribeToAllQueues(a)
        \/ \E q \in Q :
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
    /\ \A q \in Q : active[q] # 0
    /\ \A a1, a2 \in A : 
        /\ app_id[a1] # 0
        /\ app_id[a2] # 0
        /\ AppActiveCount(a1) - AppActiveCount(a2) \in { -1, 0, 1}
         
RandomPostCondition == 
    IF (~ ENABLED NextEnabled) THEN
        IF AllAppsSubscribedOnAllQueues /\ IsBalanced THEN
            /\ \A q \in Q :
                /\ Print("per_queue_releases," \o ToString(per_queue_releases[q]) \o "," \o ToString(Cardinality(A)) \o "," \o ToString(Cardinality(Q)), TRUE)
            /\ Print("total_releases," \o ToString(total_releases) \o "," \o ToString(Cardinality(A)) \o "," \o ToString(Cardinality(Q)), TRUE)
        ELSE
            /\ Print("Terminated without balance" \o "," \o ToString(Cardinality(A)) \o "," \o ToString(Cardinality(Q)), FALSE) \* this should never be printed
    ELSE
        id \in Nat

SequentialPostCondition == 
    IF (~ ENABLED NextEnabled) THEN
        IF AllAppsSubscribedOnAllQueues /\ IsBalanced THEN
            /\ \A q \in Q :
                /\ Print("per_queue_releases," \o ToString(per_queue_releases[q]) \o "," \o ToString(Cardinality(A)) \o "," \o ToString(Cardinality(Q)), TRUE)
            /\ Print("total_releases," \o ToString(total_releases) \o "," \o ToString(Cardinality(A)) \o "," \o ToString(Cardinality(Q)), TRUE)
        ELSE
            /\ Print("Terminated without balance" \o "," \o ToString(Cardinality(A)) \o "," \o ToString(Cardinality(Q)), FALSE) \* this should never be printed
    ELSE
        id \in Nat

AppOrNone ==
    A \union { 0 }

TypeOK ==
    /\ subscriber_queue \in [Q -> Seq(A)]
    /\ active \in [Q -> AppOrNone]
    /\ app_id \in [A -> Nat]
    /\ id \in Nat

(***************************************************************************)
(* Specs                                                                    *)
(***************************************************************************)

RandomSpec == Init /\ [][RandomNext]_vars /\ WF_vars(RandomNext) /\ []RandomPostCondition
SequentialSpec == Init /\ [][SequentialNext]_vars /\ WF_vars(SequentialNext)/\ []SequentialPostCondition

=============================================================================
\* Modification History
\* Last modified Mon Jul 27 11:24:29 CEST 2020 by GUNMETAL
