---- MODULE MC ----
EXTENDS AB2H, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d
----

\* MV CONSTANT definitions Data
const_157383572527560000 == 
{a, b, c, d}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_157383572527561000 ==
/\ Len(BtoA) < 4
/\ Len(AtoB) < 4
/\ Len(BtoA2) < 4
/\ Len(AtoB2) < 4
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_157383572527563000 ==
AB!Spec
----
=============================================================================
\* Modification History
\* Created Fri Nov 15 11:35:25 EST 2019 by isaac
