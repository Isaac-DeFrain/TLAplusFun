---- MODULE MC ----
EXTENDS ABSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f
----

\* MV CONSTANT definitions Data
const_1573782582607128000 == 
{a, b, c, d, e, f}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1573782582607129000 ==
FairSpec /\ (\E v \in Data: (AVar = v) ~> (BVar = v))
----
=============================================================================
\* Modification History
\* Created Thu Nov 14 20:49:42 EST 2019 by isaac
