------------------- MODULE test_dependent_vars_random_element -------------------
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

Assignable(a, b) ==
    /\ app_id[a] # 0
    /\ b_to_a[b] = 0

AssignAtoB(a, b) ==
    /\ Assignable(a, b)
    /\ b_to_a' = [b_to_a EXCEPT ![b] = a]
    /\ UNCHANGED << app_id >>

StartedApps == 
    { a \in A : app_id[a] # 0}

StartableApps ==
    { a \in A : Startable(a) } 

AssignableApps ==
    { a \in A : \E b \in B : Assignable(a,b) }     

AssignableB(a) ==
    { b \in B : Assignable(a,b) }

NextEnabled ==
    \/ StartableApps # {}
    \/ AssignableApps # {}

StartRandomApp ==
    LET apps == StartableApps
    IN
        /\ apps # {}
        /\ Start(RandomElement(apps))

AssignRandomAToRandomB ==
    LET apps == AssignableApps
    IN
        /\ apps # {}
        /\ LET a == RandomElement(apps)
           IN AssignAtoB(a, RandomElement(AssignableB(a)))        

Next ==
    \/ StartRandomApp
    \/ AssignRandomAToRandomB

AllAssigned ==
    /\ \A a \in A : app_id[a] # 0
    /\ \A b \in B : b_to_a[b] # 0

PostCondition == 
    IF (~ ENABLED NextEnabled) THEN
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
