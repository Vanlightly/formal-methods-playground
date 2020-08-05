-------------------------- MODULE sharding_plugin --------------------------
EXTENDS TLC, Sequences, Integers, FiniteSets, Naturals, Randomization 
(*
This spec is used for gathering statistics on the probability that a cohort of consumers,
out of a larger pool of clients, all connect to a cluster such that no node in that cluster
goes without a connection from that cohort.

This is relevant to the RabbitMQ Sharding Plugin that offers a logical queue that is
physically, one standard queue per broker. Consumers are assigned a queue shard that
is hosted on the broker they connect to, meaning that if a cohort fail to connect to a broker
then the queue on that broker remains unconsumed.
*)

CONSTANTS N, \* set of all nodes
          C, \* set of all clients
          QC \* the number of clients that are a consumer of our sharded queue
          
VARIABLES connection,       \* the connections of each node
          queue_clients,    \* the clients that are our queue consumers
          nlb_sequence,     \* the round-robin ordering of the NLB
          nlb_curr_node     \* the current position of the NLB in the round-robin ordering

vars == << connection, queue_clients, nlb_sequence, nlb_curr_node >>

RECURSIVE SeqFromSet(_)
SeqFromSet(S) ==
  IF S = {} THEN << >>
  ELSE
        LET x == CHOOSE x \in S : TRUE
        IN  << x >> \o SeqFromSet(S \ {x})

PrintConfig ==
    Print("CONFIG," \o ToString(Cardinality(N)) \o "," \o ToString(Cardinality(C)) \o "," \o ToString(QC), TRUE)

\* Choose a random round-robin sequence that will be used throughout a given behaviour
\* Choose a subset of the clients to be our queue consumers
Init ==
    /\ connection = [n \in N |-> {}]
    /\ nlb_curr_node = 1
    /\ nlb_sequence = SeqFromSet(N)
    /\ queue_clients = RandomSubset(QC, C)
    /\ PrintConfig

\* A client that is not connected connects to a node according to the
\* round-robin ordering of the NLB    
Connect ==
    \E c \in C :
        /\ ~\E n \in N : c \in connection[n] 
        /\ LET next_node == nlb_sequence[nlb_curr_node]
           IN
            /\ connection' = [connection EXCEPT ![next_node] = @ \union { c }] 
            /\ nlb_curr_node' = IF nlb_curr_node = Cardinality(N) THEN 1 ELSE nlb_curr_node + 1
            /\ UNCHANGED << queue_clients, nlb_sequence >>
        
Next ==
    Connect

TypeOK ==
    /\ connection \in [N -> SUBSET C]
    /\ nlb_sequence \in Seq(N)
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

OnlyQueueConsumers ==
    [ n \in N |-> queue_clients \intersect connection[n]]

\* Used to print out the distribution of the queue clients
WellBalancedInvStatsBad ==
    IF (~ ENABLED Next) THEN
        Print(ToString(OnlyQueueConsumers), TRUE)
    ELSE
        nlb_curr_node \in Nat  

\* Used in model checking mode (more to ensure the spec works)
WellBalancedInv ==
    IF (~ ENABLED Next) THEN
        ConnectedToAllNodes
    ELSE
        nlb_curr_node \in Nat

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================
\* Modification History
\* Last modified Tue Aug 04 14:05:49 CEST 2020 by Jack
\* Created Tue Aug 04 13:20:11 CEST 2020 by Jack


 \* \o ToString(queue_clients) \o "|" \o ToString(connection)