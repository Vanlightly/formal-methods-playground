------------------- MODULE rebalancing_client_stats_as_vars -------------------
EXTENDS TLC, Sequences, Integers, FiniteSets, Naturals

CONSTANTS Q, \* set of all queues
          A  \* set of all apps

ASSUME A \in SUBSET Nat

VARIABLES subscriber_queue,   \* the First Subscribe, First Active ordering of each queue
          active,             \* the active consumer of each queue
          \* statistics data
          per_queue_releases,  \* number of releases per queue 
          per_app_releases,    \* number of releases per queue 
          total_releases,      \* total number of releases
          per_app_checks \* number of check cycles per queue 

vars == << subscriber_queue, active, per_queue_releases, per_app_releases, total_releases, per_app_checks >>

(***************************************************************************)
(* Initial states                                                          *) 
(***************************************************************************)

Init ==
    /\ subscriber_queue = [q \in Q |-> <<>>]
    /\ active = [q \in Q |-> 0]
    /\ per_queue_releases = [q \in Q |-> 0]
    /\ per_app_releases = [a \in A |-> 0]
    /\ per_app_checks = [a \in A |-> 0]
    /\ total_releases = 0

(***************************************************************************)
(* Actions and state formulae                                              *) 
(***************************************************************************)

AppHasSubscriptions(a) ==
    \E q \in Q : 
        \/ active[q] = a 
        \/ \E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a
    
\* Not currently used
Stop(a) ==
    \* enabling conditions
    /\ AppHasSubscriptions(a)
    \* actions
    /\ subscriber_queue' = [q \in Q |-> SelectSeq(subscriber_queue[q], LAMBDA a1: a1 # a)]
    /\ active' = [q \in Q |-> IF active[q] = a THEN 0 ELSE active[q]] 
    /\ UNCHANGED << per_queue_releases, per_app_releases, total_releases, per_app_checks >>

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
    /\ UNCHANGED << active, per_queue_releases, per_app_releases, total_releases, per_app_checks >>

\* An app that is not subscribed on one or more queues, subscribes to all those queues it is missing
\* This action is used when we want to verify with sequential subscribe ordering    
SubscribeToAllQueues(a) ==
    \* enabling conditions
    /\ \E q \in Q :
        /\ ~AppInSubscribeQueue(a, q)
        /\ active[q] # a
    \* actions
    /\ subscriber_queue' = [q \in Q |->
            IF ~AppInSubscribeQueue(a, q) THEN
                Append(subscriber_queue[q], a)
            ELSE
                subscriber_queue[q]]
    /\ UNCHANGED << active, per_queue_releases, per_app_releases, total_releases, per_app_checks >>

\* The number of active consumers the application (a) has
AppActiveCount(a) ==
    Cardinality({ q \in Q : active[q] = a})


\* The position in the list of apps with active consumers, in reverse order, then by id
\* Required in order for each app to deterministically make the same decision about when to release a queue
Position(a) ==
    IF AppActiveCount(a) = 0 THEN -1
    ELSE
        Cardinality({ 
            a1 \in A :
                LET a_active == AppActiveCount(a)
                    a1_active == AppActiveCount(a1)
                IN
                    /\ a # a1
                    /\ a1_active > 0
                    /\ \/ a1_active >= a_active
                       \/ /\ a1_active = a_active
                          /\ a < a1
                
        })

SubscribedApplications ==
    { a \in A : AppHasSubscriptions(a) }

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
ReleaseQueues(a) ==
    LET release_count == AppActiveCount(a) - IdealNumber(a) 
    IN
        \* enabling conditions 
        /\ release_count > 0
        \* actions 
        /\ LET release_queues == CHOOSE s \in SUBSET { q \in Q : active[q] = a } : Cardinality(s) = release_count
           IN
            /\ subscriber_queue' = [q \in Q |->
                                        IF q \in release_queues 
                                        THEN SelectSeq(subscriber_queue[q], LAMBDA a1: a1 # a)
                                        ELSE subscriber_queue[q]]
            /\ per_queue_releases' = [q \in Q |->
                                              IF q \in release_queues 
                                              THEN per_queue_releases[q] + 1
                                              ELSE per_queue_releases[q]]
            /\ per_app_releases' = [per_app_releases EXCEPT ![a] = @ + release_count]
            /\ per_app_checks' = [per_app_checks EXCEPT ![a] = @ + 1]
            /\ total_releases' = total_releases + 1
            /\ active' = [q \in Q |-> IF q \in release_queues THEN 0 ELSE active[q]]

\* The SAC queue assigns active status to the next consumer in the subscriber queue
MakeActive(a, q) ==
    \* enabling conditions 
    /\ subscriber_queue[q] # <<>> 
    /\ Head(subscriber_queue[q]) = a
    /\ active[q] = 0
    \* actions
    /\ active' = [active EXCEPT ![q] = a]
    /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = SelectSeq(@, LAMBDA a1: a1 # a)]
    /\ UNCHANGED << per_queue_releases, per_app_releases, total_releases, per_app_checks >>

RandomNext ==
    \E a \in A :
        \/ ReleaseQueues(a)
        \/ \E q \in Q :
            \/ SubscribeToOneQueue(a, q)
            \/ MakeActive(a, q)

SequentialNext ==
    \E a \in A :
        \/ SubscribeToAllQueues(a)
        \/ ReleaseQueues(a)
        \/ \E q \in Q :
            \/ MakeActive(a, q)
        
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

\* True when every application has a consumer on every queue
\* (either as the active consumer or in the queue's subscriber queue)
AllAppsSubscribedOnAllQueues ==
    \A a \in A : 
        \A q \in Q : 
            \/ active[q] = a 
            \/ \E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a


\* True when:
\* - every queue has an active consumer
\* - every application is started
\* - every application has its number of active consumers <= the ideal number
\* (the ideal number can be 1 higher than it actually gets)
IsBalanced ==
    /\ \A q \in Q : active[q] # 0
    /\ \A a1, a2 \in A : 
        /\ AppHasSubscriptions(a1)
        /\ AppHasSubscriptions(a2)
        /\ AppActiveCount(a1) - AppActiveCount(a2) \in { -1, 0, 1}

PrintStats ==
    /\ \A q \in Q :
        /\ Print("per_queue_releases," \o ToString(q) \o "," \o ToString(per_queue_releases[q]) \o "," \o ToString(Cardinality(A)) \o "," \o ToString(Cardinality(Q)), TRUE)
    /\ \A a \in A :
        /\ Print("per_app_releases," \o ToString(a) \o ","\o ToString(per_app_releases[a]) \o "," \o ToString(Cardinality(A)) \o "," \o ToString(Cardinality(Q)), TRUE)
        /\ Print("per_app_checks," \o ToString(a) \o ","\o ToString(per_app_checks[a]) \o "," \o ToString(Cardinality(A)) \o "," \o ToString(Cardinality(Q)), TRUE)
    /\ Print("total_releases," \o ToString(total_releases) \o "," \o ToString(Cardinality(A)) \o "," \o ToString(Cardinality(Q)), TRUE)

RandomPostCondition == 
    IF (~ ENABLED RandomNext) THEN
        IF AllAppsSubscribedOnAllQueues /\ IsBalanced THEN
            PrintStats
        ELSE
            /\ Print("Terminated without balance" \o "," \o ToString(Cardinality(A)) \o "," \o ToString(Cardinality(Q)), FALSE) \* this should never be printed
    ELSE
        total_releases \in Nat

SequentialPostCondition == 
    IF (~ ENABLED SequentialNext) THEN
        IF AllAppsSubscribedOnAllQueues /\ IsBalanced THEN
            PrintStats
        ELSE
            /\ Print("Terminated without balance" \o "," \o ToString(Cardinality(A)) \o "," \o ToString(Cardinality(Q)), FALSE) \* this should never be printed
    ELSE
        total_releases \in Nat

AppOrNone ==
    A \union { 0 }

TypeOK ==
    /\ subscriber_queue \in [Q -> Seq(A)]
    /\ active \in [Q -> AppOrNone]

(***************************************************************************)
(* Specs                                                                    *)
(***************************************************************************)

RandomSpec == Init /\ [][RandomNext]_vars /\ WF_vars(RandomNext) 
SequentialSpec == Init /\ [][SequentialNext]_vars /\ WF_vars(SequentialNext)

=============================================================================
\* Modification History
\* Last modified Wed Aug 05 09:40:01 PDT 2020 by jack
\* Last modified Mon Jul 27 11:24:29 CEST 2020 by jack
