---- MODULE MC ----
EXTENDS three_party_two_cycles, TLC

\* PROPERTY definition @modelCorrectnessProperties:0
prop_16209578083097000 ==
(step_considered[0]/\~conforming["ALICE"])~>(~conforming["BOB"])
----
=============================================================================
\* Modification History
\* Created Thu May 13 22:03:28 EDT 2021 by yingjie
