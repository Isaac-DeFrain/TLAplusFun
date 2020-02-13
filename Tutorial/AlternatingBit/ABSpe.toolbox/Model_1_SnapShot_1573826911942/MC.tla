---- MODULE MC ----
EXTENDS AB, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e
----

\* MV CONSTANT definitions Data
const_15738269096525000 == 
{a, b, c, d, e}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_15738269096526000 ==
/\ Len(AtoB) <= 3
/\ Len(BtoA) <= 3
----
=============================================================================
\* Modification History
\* Created Fri Nov 15 09:08:29 EST 2019 by isaac
