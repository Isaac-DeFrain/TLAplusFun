---- MODULE MC ----
EXTENDS AB, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e
----

\* MV CONSTANT definitions Data
const_157382780800625000 == 
{a, b, c, d, e}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_157382780800626000 ==
/\ Len(AtoB) <= 3
/\ Len(BtoA) <= 3
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_157382780800728000 ==
ABS!FairSpec
----
=============================================================================
\* Modification History
\* Created Fri Nov 15 09:23:28 EST 2019 by isaac
