-------------------------- MODULE sharding_plugin_pluspy --------------------------
EXTENDS TLC, Sequences, FiniteSets, Integers, Naturals 

(*
This is a version of the sharding_plugin spec built to function with PlusPy.
It is a work in progress.

The variable queue_clients in the original spec has been replaced by the NLBSEQ operator,
because the original spec relied on a recursive operator that PlusPy has been unable to parse.
*)

(*
CONSTANTS N,        \* set of all nodes
          C,        \* set of all clients
          NLBSEQ,   \* round-robin NLB sequence
          QC        \* the number of clients that are a consumer of our sharded queue
*)

N == {1,2,3}

C == {1,2,3,4,5,6,7,8,9,10}

QueueClients == {1,2,3}

NLBSEQ == <<1,2,3>>

QC == 3

VARIABLES connection,       \* the connections of each node
          queue_clients,    \* the clients that are our queue consumers
          nlb_curr_node     \* the current position of the NLB in the round-robin ordering

vars == << connection, queue_clients, nlb_curr_node >>


RandomSubset(k, S) ==
    CHOOSE s \in SUBSET S : Cardinality(s) = k

\* Choose a subset of the clients to be our queue consumers
Init ==
    /\ connection = [n \in N |-> {}]
    /\ nlb_curr_node = 1
    /\ queue_clients = RandomSubset(QC, C)

\* A client that is not connected connects to a node according to the
\* round-robin ordering of the NLB    
Connect ==
    \E c \in C :
        /\ \A n \in N : c \notin connection[n] 
        /\ LET next_node == NLBSEQ[nlb_curr_node]
           IN
            /\ connection' = [connection EXCEPT ![next_node] = @ \union { c }] 
            /\ nlb_curr_node' = IF nlb_curr_node = Cardinality(N) THEN 1 ELSE nlb_curr_node + 1
            /\ UNCHANGED << queue_clients >>
        
Next ==
    Connect

TypeOK ==
    /\ connection \in [N -> SUBSET C]
    /\ nlb_curr_node \in Nat

ConnectedToAllNodes ==
    ~\E n \in N : (queue_clients \intersect connection[n]) = {}

\* Used in simulation mode to print out if we had the situation
\* where no node ends up with no queue consumers connected
WellBalancedInvStats ==
    IF (~ ENABLED Next) THEN
        IF ConnectedToAllNodes THEN
            Print("RESULT,GOOD", TRUE)
        ELSE
            Print("RESULT,BAD", TRUE)
    ELSE
        nlb_curr_node \in Nat  

Spec == Init /\ [][Next]_vars /\ []WellBalancedInvStats

=============================================================================
\* Modification History
\* Last modified Tue Aug 04 14:05:49 CEST 2020 by Jack
\* Created Tue Aug 04 13:20:11 CEST 2020 by Jack