---- MODULE MC ----
EXTENDS three_party_two_cycles, TLC

\* PROPERTY definition @modelCorrectnessProperties:0
prop_162095896222813000 ==
(~conforming["ALICE"])~>(~conforming["BOB"])
----
=============================================================================
\* Modification History
\* Created Thu May 13 22:22:42 EDT 2021 by yingjie
