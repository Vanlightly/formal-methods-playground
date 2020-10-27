------------------------------ MODULE ksubsets_ex_quant ------------------------------
EXTENDS Naturals, Randomization, FiniteSets, TLC

CONSTANT Elements,
         Limit


VARIABLES counts,
          total

vars == <<counts, total >>

AddSubset ==
    /\ total < Limit 
    /\ \E ss \in SUBSET Elements : 
        /\ Cardinality(ss) = 3 
        /\ IF ss \in DOMAIN counts
            THEN counts' = [counts EXCEPT ![ss] = @ + 1]
            ELSE counts' = counts @@ (ss :> 1)
        /\ total' = total + 1

PrintDist ==
    /\ total = Limit
    /\ total' = Limit + 1
    /\ UNCHANGED <<counts>>
    /\ \A ss \in DOMAIN counts : PrintT(<<total, ss, counts[ss]>>)
    /\ PrintT(<<"RESULT", Cardinality(DOMAIN counts)>>)

Init == 
    /\ counts = [ss \in {} |-> 0]
    /\ total = 0

Next ==
    \/ AddSubset
    \/ PrintDist

Spec == Init /\ [][Next]_vars  


=============================================================================
\* Modification History
\* Last modified Tue Oct 27 17:24:00 CET 2020 by jvanlightly
\* Created Tue Oct 27 09:55:35 CET 2020 by jvanlightly
