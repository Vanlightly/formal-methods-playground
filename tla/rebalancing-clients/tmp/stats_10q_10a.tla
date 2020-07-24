---- MODULE stats_10q_10a ----
EXTENDS target_spec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1,a2,a3,a4,a5,a6,a7,a8,a9,a10
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
q1,q2,q3,q4,q5,q6,q7,q8,q9,q10
----

\* MV CONSTANT definitions A
const_15955808771415000 == 
{a1,a2,a3,a4,a5,a6,a7,a8,a9,a10}
----

\* MV CONSTANT definitions Q
const_15955808771416000 == 
{q1,q2,q3,q4,q5,q6,q7,q8,q9,q10}
----

\* CONSTANT definitions @modelParameterConstants:2RESTART_LIMIT
const_15955808771417000 == 
0
----

=============================================================================
\* Modification History
\* Created Fri Jul 24 01:54:37 PDT 2020 by jack
