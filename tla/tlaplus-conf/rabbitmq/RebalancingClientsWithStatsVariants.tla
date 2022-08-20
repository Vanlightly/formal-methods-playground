------------------- MODULE RebalancingClientsWithStatsVariants -------------------
EXTENDS Sequences, Integers, Functions, FiniteSets, FiniteSetsExt, Naturals, TLC, TLCExt, CSV, IOUtils

\* Q=40,A=2..60
\* Q=2.60, A=40
CONSTANTS FixedCount,
          CSVFile1,
          CSVFile2,
          CSVFile3,
          CSVFile4

ASSUME FixedCount \in Nat

ASSUME 
    IOExec(
        <<"bash", "-c", "echo \"Traces,Length,Queue,PerQueueReleases,Algorithm,QueueCount,AppCount\" > " \o CSVFile1>>
        ).exitValue = 0 \* Fail fast if CSVFile1 was not created.

ASSUME 
    IOExec(
        <<"bash", "-c", "echo \"Traces,Length,App,PerAppReleases,Algorithm,QueueCount,AppCount\" > " \o CSVFile2>>
        ).exitValue = 0 \* Fail fast if CSVFile2 was not created.

ASSUME 
    IOExec(
        <<"bash", "-c", "echo \"Traces,Length,App,PerAppRounds,Algorithm,QueueCount,AppCount\" > " \o CSVFile3>>
        ).exitValue = 0 \* Fail fast if CSVFile3 was not created.

ASSUME 
    IOExec(
        <<"bash", "-c", "echo \"Traces,Length,TotalReleases,Algorithm,QueueCount,AppCount\" > " \o CSVFile4>>
        ).exitValue = 0 \* Fail fast if CSVFile4 was not created.

VARIABLES algorithm,
          app,                \* the set of all applications of any given behaviour
          queue,              \* the set of all queues of any given behaviour
          subscriber_queue,   \* the First Subscribe, First Active ordering of each queue
          active,             \* the active consumer of each queue
          app_queues,         \* the set of queues each app has a consumer for
          per_app_checks      \* number of rounds

vars == << algorithm, app, queue, subscriber_queue, active, app_queues, per_app_checks >>

\* the counter ids
per_queue_releases_ctr(q) == 1000 + q
per_app_releases_ctr(a) == 100000 + a
total_releases_ctr == 0

(***************************************************************************)
(* Initial states                                                          *) 
(***************************************************************************)

StdOut(text) ==
   TRUE \*PrintT(text)

PrintQueueState ==
    TRUE
    \* IF \A a1, a2 \in app : per_app_checks[a1] = per_app_checks[a2]
    \* THEN  
    \*       /\ PrintT(<<"Round", Min(Range(per_app_checks))>>)
    \*       /\ \A q \in queue :
    \*             PrintT([queue |-> q, 
    \*                     active |-> active'[q],
    \*                     sub_queue |-> subscriber_queue'[q]])
    \* ELSE TRUE   

ResetCounters ==
    /\ \A a \in app : TLCSet(per_app_releases_ctr(a), 0)
    /\ \A q \in queue : TLCSet(per_queue_releases_ctr(q), 0)
    /\ TLCSet(total_releases_ctr, 0)

Position1Algorithm ==
    algorithm \in { "pos1-activerelease", "pos1-nonactiverelease" }

ActiveReleaseAlgorithm ==
    algorithm \in { "pos1-activerelease", "pos2-activerelease" }    

Algorithms ==
    { "pos1-activerelease",
      "pos2-activerelease",
      "pos1-nonactiverelease",
      "pos2-nonactiverelease" }

InitVars(apps, queues, algo) ==
    /\ algorithm = algo
    /\ app = apps
    /\ queue = queues
    /\ subscriber_queue = [q \in queues |-> <<>>]
    /\ active = [q \in queues |-> 0]
    /\ app_queues = [a \in apps |-> {}]
    /\ per_app_checks = [a \in apps |-> 0]

InitFromZero ==
    \E max_count \in 2..(FixedCount + (FixedCount \div 2)) :
        /\ \E algo \in Algorithms :
            LET apps   == 1..max_count
                queues == 1..FixedCount
            IN InitVars(apps, queues, algo)
        /\ ResetCounters

(***************************************************************************)
(* State formulae                                                          *) 
(***************************************************************************)

AppHasSubscriptions(a) ==
    app_queues[a] # {}


\* The number of active consumers the application (a) has
AppActiveCount(a) ==
    Quantify(queue, LAMBDA q : active[q] = a)
    \* Cardinality({q \in queue : active[q] = a})

\* True when:
\* - every queue has an active consumer
\* - every application is started
\* - every application has its number of active consumers <= the ideal number
\* (the ideal number can be 1 higher than it actually gets)
IsBalanced ==
    /\ \A q \in queue : active[q] # 0
    /\ \A a1, a2 \in app : 
        /\ AppHasSubscriptions(a1)
        /\ AppHasSubscriptions(a2)
        /\ AppActiveCount(a1) - AppActiveCount(a2) \in { -1, 0, 1}

(***************************************************************************)
(* Action formulae                                                          *) 
(***************************************************************************)
   
\* Not currently used
Stop(a) ==
    \* enabling conditions
    /\ AppHasSubscriptions(a)
    \* actions
    /\ subscriber_queue' = [q \in queue |-> SelectSeq(subscriber_queue[q], LAMBDA a1: a1 # a)]
    /\ active' = [q \in queue |-> IF active[q] = a THEN 0 ELSE active[q]] 
    /\ app_queues' = [app_queues EXCEPT ![a] = {}]
    /\ UNCHANGED << algorithm, app, queue, per_app_checks >>

\* If an app is not subscribed to a queue, then subscribe
\* This action is used when we want to verify with random subscribe ordering
SubscribeToOneQueue(a, q) ==
    \* enabling conditions 
    /\ q \notin app_queues[a]
    \* actions
    /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = Append(@, a)]
    /\ app_queues' = [app_queues EXCEPT ![a] = @ \union {q}]
    /\ UNCHANGED << algorithm, app, queue, active, per_app_checks >>
    /\ StdOut(<<"SubscribeToOneQueue", a, q>>)

\* An app that is not subscribed on one or more queues, subscribes to all those queues it is missing
\* This action is used when we want to verify with sequential subscribe ordering    
SubscribeToAllQueues(a) ==
    \* enabling conditions
    /\ app_queues[a] # queue
    \* actions
    /\ subscriber_queue' = [q \in queue |->
                                IF q \notin app_queues[a] THEN
                                    Append(subscriber_queue[q], a)
                                ELSE
                                    subscriber_queue[q]]
    /\ app_queues' = [app_queues EXCEPT ![a] = queue]
    /\ UNCHANGED << algorithm, app, queue, active, per_app_checks >>
    /\ StdOut(<<"SubscribeToAllQueues", a>>)

\* The position in the list of apps with active consumers, in reverse order, then by id
\* Required in order for each app to deterministically make the same decision about when to release a queue
Position1(a) ==
    IF AppActiveCount(a) = 0 THEN -1
    ELSE
        Cardinality({ 
            a1 \in app :
                LET a_active == AppActiveCount(a)
                    a1_active == AppActiveCount(a1)
                IN
                    /\ a # a1
                    /\ a1_active > 0
                    /\ \/ a1_active > a_active
                       \/ /\ a1_active = a_active
                          /\ a < a1
                
        })

Position2(a) ==
    Quantify(app, LAMBDA a1 : 
        /\ AppHasSubscriptions(a1)
        /\ LET a_active == AppActiveCount(a)
              a1_active == AppActiveCount(a1)
           IN
               /\ a # a1
               /\ \/ a1_active > a_active
                  \/ /\ a1_active = a_active
                     /\ a1 < a)

SubscribedAppCount ==
    Quantify(app, LAMBDA a1 : AppHasSubscriptions(a1))

\* Calculates the ideal number of active consumers this application should have
IdealNumber(a) ==
    LET queue_count == Cardinality(queue)
        app_count == SubscribedAppCount
    IN
        IF app_count = 0 THEN 0
        ELSE
            LET ideal == queue_count \div app_count
                remainder ==  queue_count % app_count
                position == IF Position1Algorithm
                            THEN Position1(a)
                            ELSE Position2(a)
            IN
                IF remainder = 0 THEN ideal
                ELSE
                    IF remainder >= position + 1 THEN
                        ideal + 1
                    ELSE
                        ideal 

IncrementMetrics(a, queues, release_count) ==
    /\ \A q \in queues : TLCSet(per_queue_releases_ctr(q), TLCGet(per_queue_releases_ctr(q)) + 1)
    /\ TLCSet(per_app_releases_ctr(a), TLCGet(per_app_releases_ctr(a)) + release_count)
    /\ TLCSet(total_releases_ctr, TLCGet(total_releases_ctr) + release_count)

\* Releases one queue if it has too many active consumers
ReleaseQueues(a, release_count) ==
    \E release_queues \in SUBSET { q \in queue : active[q] = a } : 
        /\ Cardinality(release_queues) = release_count
        /\ subscriber_queue' = [q \in queue |->
                                    IF q \in release_queues 
                                    THEN SelectSeq(subscriber_queue[q], LAMBDA a1: a1 # a)
                                    ELSE subscriber_queue[q]]
        /\ active' = [q \in queue |-> IF q \in release_queues THEN 0 ELSE active[q]]
        /\ app_queues' = [app_queues EXCEPT ![a] = @ \ release_queues]
        /\ IncrementMetrics(a, release_queues, release_count)
        /\ StdOut(<<"Release", a, release_queues>>)

ReleaseNonActiveQueues(a) ==
    LET non_active_queues == {q \in queue : active[q] # a }
    IN /\ subscriber_queue' = [q \in queue |->
                                IF q \in non_active_queues 
                                THEN SelectSeq(subscriber_queue[q], LAMBDA a1: a1 # a)
                                ELSE subscriber_queue[q]]
       /\ app_queues' = [app_queues EXCEPT ![a] = @ \ non_active_queues]
       /\ UNCHANGED << active >>

ExistsOtherUnderActiveApp ==
    \E a \in app :
        AppActiveCount(a) < IdealNumber(a)

\* Perform a check as long as:
\* the balancing has not terminated
\* this app is equal to or behind the other apps in terms of number of checks
\* all apps are subscribed to all queues (this ignores that there can be a
\* very short period between release and subscribe operations where this
\* might not be the case).
CanPerformCheck(a) ==
    /\ ~IsBalanced
    /\ \A a1 \in app : 
        /\ per_app_checks[a] <= per_app_checks[a1]
        /\ app_queues[a1] = queue
    /\ \A q \in queue : active[q] # 0
        
PerformActiveReleaseCheck(a) ==
    \* enabling conditions
    /\ CanPerformCheck(a)
    \* actions
    /\ per_app_checks' = [per_app_checks EXCEPT ![a] = @ + 1]
    /\ LET release_count == AppActiveCount(a) - IdealNumber(a) 
       IN
            /\ IF release_count > 0 THEN 
                   /\ ReleaseQueues(a, release_count)
               ELSE 
                   /\ IncrementMetrics(a, {}, 0)
                   /\ UNCHANGED << app_queues, subscriber_queue, active >>
            /\ StdOut(<<"PerformActiveReleaseCheck", a, release_count>>)
            /\ PrintQueueState
            \* /\ \A a1 \in app : 
            \*     PrintT(<<a, "Ideal", a1, IdealNumberVals(a1), AppActiveCount(a1)>>)
    /\ UNCHANGED <<algorithm, app, queue>>

PerformNonActiveReleaseCheck(a) ==
    \* enabling conditions
    /\ CanPerformCheck(a)
    \* actions
    /\ per_app_checks' = [per_app_checks EXCEPT ![a] = @ + 1]
    /\ LET release_count == AppActiveCount(a) - IdealNumber(a) 
       IN
            /\ IF release_count > 0 THEN 
                   /\ ReleaseQueues(a, release_count)
                   /\ StdOut(<<"PerformNonActiveReleaseCheck", a, release_count, "release active">>)
               ELSE IF release_count = 0 /\ ExistsOtherUnderActiveApp THEN
                   /\ ReleaseNonActiveQueues(a)
                   /\ StdOut(<<"PerformNonActiveReleaseCheck", a, release_count, "release non-active">>)
               ELSE
                   /\ IncrementMetrics(a, {}, 0)
                   /\ StdOut(<<"PerformNonActiveReleaseCheck", a, "No releases">>)
                   /\ UNCHANGED << app_queues, subscriber_queue, active >>
            /\ UNCHANGED << algorithm, app, queue >>

PerformCheck(a) ==
    IF ActiveReleaseAlgorithm
    THEN PerformActiveReleaseCheck(a)
    ELSE PerformNonActiveReleaseCheck(a)

\* The SAC queue assigns active status to the next consumer in the subscriber queue
MakeActive(a, q) ==
    \* enabling conditions 
    /\ subscriber_queue[q] # <<>> 
    /\ Head(subscriber_queue[q]) = a
    /\ active[q] = 0
    \* actions
    /\ active' = [active EXCEPT ![q] = a]
    /\ subscriber_queue' = [subscriber_queue EXCEPT ![q] = SelectSeq(@, LAMBDA a1: a1 # a)]
    /\ UNCHANGED << algorithm, app, queue, app_queues, per_app_checks >>
    /\ StdOut(<<"MakeActive", a, q>>)

RandomNext ==
    \E a \in app : 
        \/ PerformCheck(a)
        \/ \E q \in queue :
            \/ SubscribeToOneQueue(a, q)
            \/ MakeActive(a, q)

SequentialNext ==
    \E a \in app :
        \/ PerformCheck(a)
        \/ SubscribeToAllQueues(a)
        \/ \E q \in queue :
           \/ MakeActive(a, q)
       
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

\* True when every application has a consumer on every queue
\* (either as the active consumer or in the queue's subscriber queue)
AllAppsSubscribedOnAllQueues ==
    \A a \in app : app_queues[a] = queue

AppOrNone ==
    app \union { 0 }

TypeOK ==
    /\ subscriber_queue \in [queue -> Seq(app)]
    /\ active \in [queue -> AppOrNone]
    /\ app_queues \in [app -> SUBSET queue]

StatsInv ==
    (AllAppsSubscribedOnAllQueues /\ IsBalanced) =>
            /\ PrintT(<<"Stats", "Traces", TLCGet("stats").traces, TLCGet("level"),
                        algorithm, Cardinality(app), Cardinality(queue)>>)
            /\ \A q \in queue :
                CSVWrite("%1$s,%2$s,%3$s,%4$s,%5$s,%6$s,%7$s",
                <<TLCGet("stats").traces, TLCGet("level"), q, 
                  TLCGet(per_queue_releases_ctr(q)), algorithm,
                  Cardinality(queue), Cardinality(app)>>, CSVFile1)
            /\ \A a \in app :
                /\ CSVWrite("%1$s,%2$s,%3$s,%4$s,%5$s,%6$s,%7$s",
                    <<TLCGet("stats").traces, TLCGet("level"), a, 
                      TLCGet(per_app_releases_ctr(a)), algorithm,
                      Cardinality(queue), Cardinality(app)>>, CSVFile2)
                /\ CSVWrite("%1$s,%2$s,%3$s,%4$s,%5$s,%6$s,%7$s",
                    <<TLCGet("stats").traces, TLCGet("level"), a,
                      per_app_checks[a], algorithm, Cardinality(queue),
                      Cardinality(app)>>, CSVFile3)
            /\ CSVWrite("%1$s,%2$s,%3$s,%4$s,%5$s,%6$s",
                <<TLCGet("stats").traces, TLCGet("level"),
                  TLCGet(total_releases_ctr), algorithm, Cardinality(queue),
                  Cardinality(app)>>, CSVFile4)
            /\ ResetCounters

TestInv ==
    TRUE
    \* IF (~ ENABLED RandomStandardNext)
    \* THEN AllAppsSubscribedOnAllQueues /\ IsBalanced
    \* ELSE TRUE

    \* IF TLCGet("level") > 1
    \* THEN
    \*     /\ \A a \in app : 
    \*             PrintT(<<"Ideal", a, IdealNumberVals(a), AppActiveCount(a)>>)
    \* ELSE TRUE

(***************************************************************************)
(* Specs                                                                    *)
(***************************************************************************)

RandomSpecFromZero == InitFromZero /\ [][RandomNext]_vars /\ WF_vars(RandomNext) 
SequentialSpecFromZero == InitFromZero /\ [][SequentialNext]_vars /\ WF_vars(SequentialNext)

=============================================================================
\* Modification History
\* Last modified Thu Aug 13 09:39:19 PDT 2020 by jack
\* Last modified Mon Jul 27 11:24:29 CEST 2020 by jack
