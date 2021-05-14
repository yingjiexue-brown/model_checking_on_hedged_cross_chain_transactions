---- MODULE MC ----
EXTENDS three_party_two_cycles, TLC

\* PROPERTY definition @modelCorrectnessProperties:0
prop_16209574976375000 ==
(step_considered[0]/\~conforming["ALICE"])=>(ended=>~conforming["BOB"])
----
=============================================================================
\* Modification History
\* Created Thu May 13 21:58:17 EDT 2021 by yingjie
