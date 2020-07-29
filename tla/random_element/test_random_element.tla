------------------- MODULE test_random_element -------------------
EXTENDS TLC

CONSTANTS A
VARIABLES app_id 

vars == << app_id >>

Init ==
    app_id = [a \in A |-> 0]

(***************************************************************************)
(* Actions and state formulae                                              *) 
(***************************************************************************)
    
Startable(a) == app_id[a] = 0

Start(a) ==
    \* enabling conditions 
    /\ Startable(a)
    \* actions
    /\ app_id' = [app_id EXCEPT ![a] = 1]

StartableApps ==
    { a \in A : Startable(a) } 

NextEnabled ==
    StartableApps # {}

StartRandomApp ==
    LET apps == StartableApps
    IN
        /\ apps # {}
        /\ Start(RandomElement(apps))

Next ==
    StartRandomApp

PostCondition == 
    IF (~ ENABLED NextEnabled) THEN
        IF \A a \in A : app_id[a] # 0 THEN
            Print("All started", TRUE)
        ELSE
            Print("Some stopped", TRUE)
    ELSE
        TRUE

TypeOK ==
    app_id \in [A -> {0,1}]


Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================
\* Modification History
\* Last modified Mon Jul 27 11:24:29 CEST 2020 by GUNMETAL
