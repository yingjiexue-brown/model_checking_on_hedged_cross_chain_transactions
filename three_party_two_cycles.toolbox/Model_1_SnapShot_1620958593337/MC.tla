---- MODULE MC ----
EXTENDS three_party_two_cycles, TLC

\* PROPERTY definition @modelCorrectnessProperties:0
prop_16209581944519000 ==
(step_considered[1]/\~conforming["ALICE"])~>(~conforming["BOB"])
----
=============================================================================
\* Modification History
\* Created Thu May 13 22:09:54 EDT 2021 by yingjie
