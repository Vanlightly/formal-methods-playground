------------------- MODULE test_non_det -------------------
EXTENDS TLC

CONSTANTS A
VARIABLES app_id 

vars == << app_id >>

Init ==
    app_id = [a \in A |-> 0]

Startable(a) == app_id[a] = 0

Start(a) ==
    \* enabling conditions 
    /\ Startable(a)
    \* actions
    /\ app_id' = [app_id EXCEPT ![a] = 1]

Next ==
    \E a \in A : Start(a)

PostCondition == 
    IF (~ ENABLED Next) THEN
        IF \A a \in A : app_id[a] # 0 THEN
            Print("All started", TRUE)
        ELSE
            Print("Some stopped", TRUE)
    ELSE
        TRUE

TypeOK ==
    /\ app_id \in [A -> {0,1}]

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================
\* Modification History
\* Last modified Mon Jul 27 11:24:29 CEST 2020 by GUNMETAL
