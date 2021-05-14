---- MODULE MC ----
EXTENDS three_party_two_cycles, TLC

\* PROPERTY definition @modelCorrectnessProperties:0
prop_162095862748111000 ==
(step_considered[3]/\~conforming["ALICE"])~>(~conforming["BOB"])
----
=============================================================================
\* Modification History
\* Created Thu May 13 22:17:07 EDT 2021 by yingjie
