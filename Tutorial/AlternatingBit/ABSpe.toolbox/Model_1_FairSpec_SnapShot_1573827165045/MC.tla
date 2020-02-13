---- MODULE MC ----
EXTENDS AB, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e
----

\* MV CONSTANT definitions Data
const_157382716303121000 == 
{a, b, c, d, e}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_157382716303122000 ==
/\ Len(AtoB) <= 3
/\ Len(BtoA) <= 3
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_157382716303124000 ==
ABS!FairSpec
----
=============================================================================
\* Modification History
\* Created Fri Nov 15 09:12:43 EST 2019 by isaac
