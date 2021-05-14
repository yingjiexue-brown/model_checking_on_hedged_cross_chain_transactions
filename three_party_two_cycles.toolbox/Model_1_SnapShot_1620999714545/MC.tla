---- MODULE MC ----
EXTENDS three_party_two_cycles, TLC

\* PROPERTY definition @modelCorrectnessProperties:0
prop_162099939346927000 ==
(~conforming["ALICE"])~>(~conforming["BOB"])
----
=============================================================================
\* Modification History
\* Created Fri May 14 09:36:33 EDT 2021 by yingjie
