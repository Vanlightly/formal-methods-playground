------------------- MODULE target_spec -------------------
EXTENDS TLC, Sequences, Integers, FiniteSets, Naturals

CONSTANTS Q, \* set of queues, e.g. { q1, q2, q3, q4, q5 }
          A,  \* set of apps, e.g. { a1, a2, a3 }
          RESTART_LIMIT

(*

Models an algorithm that balances the consumption of group of Q queues over a group of
A applications, using the Single Active Consumer (SAC) feature of RabbitMQ.

RabbitMQ itself does not possess a Kafka-like consumer group functionality, it only has SAC,
but a group of consuming applications can take individual actions in order to achieve balanced
consumption.

The individual actions of consuming applications is to detect how many active consumers each has
and when calculate the ideal number of active consumers they should have. On having too many active consumers,
an application will "release" N queues which, in the real-wolrd, means it will cancel and then resubscribe
to N queues.

The SAC queue will then select the next consumer in its "subscriber queue". This means that rebalancing
can take sometime as there can be cascades of releases until balance is achieved.

Safety is assured because all consumers in the group always subscribe to all queues. The main issue
with this algorithm is its liveness properties and it is those properties that we are most concerned with
and likely the reason to not choose this algorithm at all.

Example:

Initial state:
- q1
- q2

State 1 (a1 subscribes to q1 and is made active):
- q1 -> a1

State 2 (a1 subscribes to q2 and is made active):
- q1 -> a1
- q2 -> a1

State 3 (a2 subscribes to q1, added to subscriber queue):
- q1 -> a1 [a2]
- q2 -> a1

State 4 (a2 subscribes to q2, added to subscriber queue):
- q1 -> a1 [a2]
- q2 -> a1 [a2]

State 5 (a1 releases q2):
- q1 -> a1 [a2]
- q2 -> - [a2]

State 6 (a2 made active on q2):
- q1 -> a1 [a2]
- q2 -> a2

Balance achieved

State 6 (a1 subscribes to q2, added to subscriber queue):
- q1 -> a1 [a2]
- q2 -> a2 [a1]

Deadlock (no more to do - steady state)
 
*)

VARIABLES subscriber_queue,   \* the First Subscribe, First Active ordering of each queue
          active,             \* the active consumer of each queue
          app,                \* a list of ids, required for determinism in releases
          id,                 \* for assigning each id
          \* statistics data
          per_queue_releases, \* number of releases per queue counter
          total_releases      \* total number of releases

vars == << subscriber_queue, active, app, id, per_queue_releases, total_releases >>

release_counter == 0

(***************************************************************************)
(* Initial states                                                          *) 
(***************************************************************************)

Init ==
    /\ subscriber_queue = [q \in Q |-> <<>>]
    /\ active = [q \in Q |-> 0]
    /\ app = [a \in A |-> 0]
    /\ id = 1
    /\ per_queue_releases = [q \in Q |-> 0]
    /\ total_releases = 0
\*    /\ TLCSet(release_counter, 0)

(***************************************************************************)
(* Actions and state formulae                                              *) 
(***************************************************************************)
    
StoppedApps ==
    { a \in A : app[a] = 0 }

StartedApps ==
    { a \in A : app[a] # 0 }

\* A stopped app starts and is assigned an id
Start ==
    \E a \in StoppedApps :
        \* enabling conditions 
        /\ app[a] = 0
        \* actions
        /\ app' = [app EXCEPT ![a] = id]
        /\ id' = id + 1
        /\ UNCHANGED << subscriber_queue, active, per_queue_releases, total_releases >>

AppInSubscribeQueue(a, q) ==
    \E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a

\* If an app is not subscribed to a queue, then subscribe
SubscribeToOneQueue ==
    \E a \in StartedApps : 
        \E q \in Q :
            \* enabling conditions 
            /\ ~\E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a
            /\ active[q] # a
            \* actions
            /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = Append(@, a)]
            /\ UNCHANGED << active, app, id, per_queue_releases, total_releases >>

\* An app that is not subscribed on one or more queues, subscribes to all those queues it is missing    
SubscribeToAllQueues ==
    \E a \in StartedApps : 
        \* enabling conditions
        /\ \E q \in Q :
            /\ ~AppInSubscribeQueue(a, q)
            /\ active[q] # a
        \* actions
        \* subscribe to all queues
        /\ subscriber_queue' = [q \in Q |->
                IF ~AppInSubscribeQueue(a, q) THEN
                    Append(subscriber_queue[q], a)
                ELSE
                    subscriber_queue[q]]
        /\ UNCHANGED << active, app, id, per_queue_releases, total_releases >>

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
                          /\ app[a] < app[a1]
                
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
Release ==
    \E a \in StartedApps : 
        \E q \in Q :
            \* enabling conditions 
            /\ active[q] = a
            /\ AppActiveCount(a) > IdealNumber(a) 
            \* actions
            /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = SelectSeq(@, LAMBDA a1: a1 # a)]
            /\ per_queue_releases' = [per_queue_releases EXCEPT ![q] = @ + 1]
            /\ total_releases' = total_releases + 1
\*            /\ TLCSet(release_counter,TLCGet(release_counter) + 1)
            /\ \/ /\ active[q] = a
                  /\ active' = [active EXCEPT ![q] = 0]
               \/ /\ active[q] # a
                  /\ UNCHANGED active
            /\ UNCHANGED << app, id >>

\* The SAC queue assigns active status to the next consumer in the subscriber queue
MakeActive ==
    \E a \in StartedApps : 
        \E q \in Q :
        \* enabling conditions 
        /\ Cardinality(DOMAIN subscriber_queue[q]) > 0 
        /\ Head(subscriber_queue[q]) = a
        /\ active[q] = 0
        \* actions
        /\ active' = [active EXCEPT ![q] = a]
        /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = SelectSeq(@, LAMBDA a1: a1 # a)]
        /\ UNCHANGED << app, id, per_queue_releases, total_releases >>

Stop ==
    /\ id < Cardinality(A) + RESTART_LIMIT
    /\ \E a \in StartedApps :
        /\ subscriber_queue' = [q \in Q |-> SelectSeq(subscriber_queue[q], LAMBDA a1: a1 # a)]
        /\ active' = [q \in Q |-> IF active[q] = a THEN 0 ELSE active[q]] 
        /\ app' = [app EXCEPT ![a] = 0]
        /\ UNCHANGED << id, per_queue_releases, total_releases >>

NextSequential ==
    \/ Start
    \/ SubscribeToOneQueue
    \/ Release
    \/ MakeActive
    \/ Stop

NextRandom ==
    \/ Start
    \/ SubscribeToAllQueues
    \/ Release
    \/ MakeActive
    \/ Stop    

(***************************************************************************)
(* Temporal formulas                                                       *)
(***************************************************************************)

\* True when:
\* - every queue has an active consumer
\* - every application is started
\* - every application has its number of active consumers <= the ideal number
\* (the ideal number can be 1 higher than it actually gets)
IsBalanced ==
    /\ \A q \in Q : active[q] # 0
    /\ \A a \in A : 
        /\ app[a] # 0
        /\ AppActiveCount(a) <= IdealNumber(a) 
         
\* True when every application has a consumer on every queue
\* (either as the active consumer or in the queue's subscriber queue)
AllAppsSubscribedOnAllQueues ==
    \A a \in A : 
        \A q \in Q : 
            \/ active[q] = a 
            \/ \E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a
    
\* Temporal (liveness) formula that states that:
\* Given all apps are subscribed to all queues then eventually balance is achieved
EventuallyBalanced ==
    AllAppsSubscribedOnAllQueues~>IsBalanced

EventuallAllSubscribed ==
    <>AllAppsSubscribedOnAllQueues
    
Liveness ==
    /\ EventuallAllSubscribed
    /\ EventuallyBalanced
        
PostCondition == 
    /\ AllAppsSubscribedOnAllQueues
    /\ IsBalanced

SequentialSafety == []((~ ENABLED NextSequential) => PostCondition)
RandomSafety == []((~ ENABLED NextRandom) => PostCondition)

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

AppOrNone ==
    A \union { 0 }

TypeOK ==
    /\ subscriber_queue \in [Q -> Seq(A)]
    /\ active \in [Q -> AppOrNone]
    /\ app \in [A -> Nat]
    /\ id \in Nat
    /\ per_queue_releases \in [Q -> Nat]
    /\ total_releases \in Nat

\* A trick to print out the statistics when perfect balance has been achieved
PrintStatsAtEndSeq ==
    IF ~ ENABLED NextSequential THEN
        /\ \A q \in Q :
            Print("per_queue_releases," \o ToString(per_queue_releases[q]), TRUE)
        /\ Print("total_releases," \o ToString(total_releases), TRUE)
        
    ELSE id \in Nat

PrintStatsAtEndRandom ==
    IF ~ ENABLED NextRandom THEN
        /\ \A q \in Q :
            Print("per_queue_releases," \o ToString(per_queue_releases[q]), TRUE)
        /\ Print("total_releases," \o ToString(total_releases), TRUE)
        
    ELSE id \in Nat

(***************************************************************************)
(* Specs                                                                    *)
(***************************************************************************)

SequentialSpec == Init /\ [][NextSequential]_vars /\ WF_vars(NextSequential)
RandomSpec == Init /\ [][NextRandom]_vars /\ WF_vars(NextRandom)


\*Inv == IF TLCGet("duration") > 60 THEN Print(TLCGet(release_counter), FALSE) 
\*       ELSE id \in Nat \* Some invariant of the system that we know holds to
\*                       \* lift Inv from constant to state level. TLC evaluates
\*                       \* constant expressions eagerly at startup. Alternatively,
\*                       \* run TLC with -Dtlc2.tool.impl.SpecProcessor.vetoed=Inv
\*                       \* TODO: Load TLC module override with level=1 (state).

=============================================================================
\* Modification History
\* Last modified Fri Jul 24 04:44:28 PDT 2020 by jack
\* Last modified Fri Jul 24 03:34:52 PDT 2020 by jack
\* Last modified Fri Jul 24 10:23:06 CEST 2020 by GUNMETAL
\* Created Tue Jul 21 17:02:05 CEST 2020 by GUNMETAL
