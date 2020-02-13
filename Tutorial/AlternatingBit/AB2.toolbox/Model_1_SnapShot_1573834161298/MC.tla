---- MODULE MC ----
EXTENDS AB2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d
----

\* MV CONSTANT definitions Data
const_157383415628144000 == 
{a, b, c, d}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_157383415628145000 ==
/\ Len(AtoB2) < 4
/\ Len(BtoA2) < 4
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_157383415628147000 ==
ABS!Spec
----
=============================================================================
\* Modification History
\* Created Fri Nov 15 11:09:16 EST 2019 by isaac
