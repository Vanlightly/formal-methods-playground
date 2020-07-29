------------------- MODULE test_dependent_vars_non_det -------------------
EXTENDS TLC

CONSTANTS A, B
VARIABLES app_id, b_to_a 

vars == << app_id, b_to_a >>

Init ==
    /\ app_id = [a \in A |-> 0]
    /\ b_to_a = [b \in B |-> 0]

Startable(a) == app_id[a] = 0

Start(a) ==
    \* enabling conditions 
    /\ Startable(a)
    \* actions
    /\ app_id' = [app_id EXCEPT ![a] = 1]
    /\ UNCHANGED << b_to_a >>

AssignAtoB(a, b) ==
    /\ app_id[a] # 0
    /\ b_to_a[b] = 0
    /\ b_to_a' = [b_to_a EXCEPT ![b] = a]
    /\ UNCHANGED << app_id >>

Next ==
    \E a \in A : 
        \/ Start(a)
        \/ \E b \in B :
            AssignAtoB(a, b)

AllAssigned ==
    /\ \A a \in A : app_id[a] # 0
    /\ \A b \in B : b_to_a[b] # 0

PostCondition == 
    IF (~ ENABLED Next) THEN
        IF AllAssigned THEN
            Print("All started", TRUE)
        ELSE
            Print("Some stopped", TRUE)
    ELSE
        TRUE

TypeOK ==
    /\ app_id \in [A -> {0,1}]
    /\ b_to_a \in [B -> A \union {0}]

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================
\* Modification History
\* Last modified Mon Jul 27 11:24:29 CEST 2020 by GUNMETAL
