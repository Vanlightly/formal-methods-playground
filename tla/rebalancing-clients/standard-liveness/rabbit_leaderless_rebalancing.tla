------------------- MODULE rabbit_leaderless_rebalancing -------------------
EXTENDS TLC, Sequences, Integers, FiniteSets, Naturals

CONSTANTS Q,                \* set of queues, e.g. { q1, q2, q3, q4, q5 }
          A,                \* set of apps, e.g. { a1, a2, a3 }
          RESTART_LIMIT     \* plays two roles:
                            \* 1. Limits state space
                            \* 2. Makes defining temporal properties that
                            \* a perfect balance will eventually be achieved
                            \* trivial because we prevent infinite application restarts.
                            \* We are not concerned with infinite restarts that prevent
                            \* perfect balance from being achieved. 

(*

ALGORITHM DESCRIPTION

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

NOTES ON SAFETY AND LIVENESS

Safety for this algorithm focuses on whether queues have consumers or not and whether there is
a balance of active consumers across applications. But these properties cannot be guaranteed in
every state. 
 - Applications can stop and start, meaning that queues may not have consumers in some states
 - Each individual client has no control over active status assignment and so each queue can
   assign active status in an imbalanced way.

Ths algorithm is fundamentally unsafe in this regard. But given the chance, eventually each application
will create consumers on all queues and balance will be achieved. So we are only concerned with the 
liveness property that perfect balance is achievable in all behaviours. Every behaviour should 
eventually achieve balance. 

Therefore we have no invariants beyond the usual "type safety".

EXAMPLE BEHAVIOUR

Uses the notation: queue -> active consumer app [subscriber queue]

Initial state:
- a1 -> not started, a2 -> not started
- q1 -> 0 [], q2 -> 0 []

State 1 (a1 starts)
- a1 -> started, a2 -> not started
- q1 -> 0 [], q2 -> 0 []

State 2 (a2 starts)
- a1 -> started, a2 -> started
- q1 -> 0 [], q2 -> 0 []

State 3 (a1 subscribes to q1):
- q1 -> 0 [a1], q2 -> 0 []

State 4 (a1 subscribes to q2):
- q1 -> 0 [a1], q2 -> 0 [a1]

State 5 (a1 made active on q1):
- q1 -> a1 [], q2 -> 0 []

State 6 (a1 made active on q2):
- q1 -> a1 [], q2 -> a1 []

State 7 (a2 subscribes to q1, added to subscriber queue):
- q1 -> a1 [a2], q2 -> a1 []

State 8 (a2 subscribes to q2, added to subscriber queue):
- q1 -> a1 [a2], q2 -> a1 [a2]

State 9 (a1 releases q2):
- q1 -> a1 [a2], q2 -> 0 [a2]

State 10 (a2 made active on q2):
- q1 -> a1 [a2], q2 -> a2 []

Balance of active consumers achieved

State 11 (a1 subscribes to q2, added to subscriber queue):
- q1 -> a1 [a2], q2 -> a2 [a1]

All applications subscribed to all queues

Deadlock (no more to do - steady state aka terminates)
 
*)

VARIABLES subscriber_queue,   \* the First Subscribe, First Active ordering of each queue
          active,             \* the active consumer of each queue
          app_id,             \* the id of each app, required for determinism in releases
          id                  \* for assigning each id

vars == << subscriber_queue, active, app_id, id >>

(***************************************************************************)
(* Initial states                                                          *) 
(***************************************************************************)

Init ==
    /\ subscriber_queue = [q \in Q |-> <<>>]
    /\ active = [q \in Q |-> 0]
    /\ app_id = [a \in A |-> 0]
    /\ id = 1

(***************************************************************************)
(* Actions and state formulae                                              *) 
(***************************************************************************)
    
StartedApps ==
    { a \in A : app_id[a] # 0 }

\* If app a is not started, then it starts and gets assigned an id
Start(a) ==
    \* enabling conditions 
    /\ app_id[a] = 0
    \* actions
    /\ app_id' = [app_id EXCEPT ![a] = id]
    /\ id' = id + 1
    /\ UNCHANGED << subscriber_queue, active >>

\* If app a is started, then it stops (but not infinitely)
Stop(a) ==
    \* enabling conditions
    /\ app_id[a] # 0
    /\ id < Cardinality(A) + RESTART_LIMIT
    \* actions
    /\ subscriber_queue' = [q \in Q |-> SelectSeq(subscriber_queue[q], LAMBDA a1: a1 # a)]
    /\ active' = [q \in Q |-> IF active[q] = a THEN 0 ELSE active[q]] 
    /\ app_id' = [app_id EXCEPT ![a] = 0]
    /\ UNCHANGED << id >>

AppInSubscribeQueue(a, q) ==
    \E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a

\* If app a is not subscribed to a queue q, then it subscribes
Subscribe(a, q) ==
    \* enabling conditions 
    /\ ~\E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a
    /\ active[q] # a
    \* actions
    /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = Append(@, a)]
    /\ UNCHANGED << active, app_id, id >>

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

\* If app a is active on queue q and it has too many active consumers
\* then it releases this queue
Release(a, q) ==
    \* enabling conditions 
    /\ active[q] = a
    /\ AppActiveCount(a) > IdealNumber(a) 
    \* actions
    /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = SelectSeq(@, LAMBDA a1: a1 # a)]
    /\ \/ /\ active[q] = a
          /\ active' = [active EXCEPT ![q] = 0]
       \/ /\ active[q] # a
          /\ UNCHANGED active
    /\ UNCHANGED << app_id, id >>

\* If app a has a consumer that is at the head of the subscriber queue of queue q
\* then the queue makes that consumer active
MakeActive(a, q) ==
    \* enabling conditions 
    /\ Cardinality(DOMAIN subscriber_queue[q]) > 0 
    /\ Head(subscriber_queue[q]) = a
    /\ active[q] = 0
    \* actions
    /\ active' = [active EXCEPT ![q] = a]
    /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = SelectSeq(@, LAMBDA a1: a1 # a)]
    /\ UNCHANGED << app_id, id >>

Next ==
    \E a \in A :
        \/ Start(a)
        \/ Stop(a)
        \/ \E q \in Q :
            \/ Subscribe(a, q)
            \/ Release(a, q)
            \/ MakeActive(a, q)
        

(***************************************************************************)
(* Temporal formulas                                                       *)
(***************************************************************************)

\* True when:
\* - every queue has an active consumer
\* - every application is started
\* - no application has more than 2 extra active consumers compared to another
BalancedActiveConsumers ==
    /\ \A q \in Q : active[q] # 0
    /\ \A a1, a2 \in A : 
        /\ app_id[a1] # 0
        /\ app_id[a2] # 0
        /\ AppActiveCount(a1) - AppActiveCount(a2) \in { -1, 0, 1}
         
\* True when every application has a consumer on every queue
\* (either as the active consumer or in the queue's subscriber queue)
AllAppsSubscribedOnAllQueues ==
    \A a \in A : 
        \A q \in Q : 
            \/ active[q] = a 
            \/ \E a1 \in DOMAIN subscriber_queue[q] : subscriber_queue[q][a1] = a
    
\* Perfect balance of active consumers across the applications is achieved,
\* with back-up consumers waiting to take over in the event that an active consumer stops   
PerfectBalance == 
   /\ AllAppsSubscribedOnAllQueues
   /\ BalancedActiveConsumers
   
\* Always we eventually achieve a perfect balance, given that application restarts
\* are finite.
Liveness ==
    []<>PerfectBalance

\*Safety == []((~ ENABLED Next) => PerfectBalance)

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

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

Fairness ==
    /\ WF_vars(Next)
    \* the subscription by every app to every queue is weakly fair
    \* this ensures we make progress towards all applications subscribing to
    \* all queues which is necessary to achieve balance
    /\ \A a \in A :
        \A q \in Q :
            WF_vars(Subscribe(a, q))

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
\* Modification History