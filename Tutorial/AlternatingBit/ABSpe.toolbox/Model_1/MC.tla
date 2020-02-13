---- MODULE MC ----
EXTENDS AB, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e
----

\* MV CONSTANT definitions Data
const_15738270294668000 == 
{a, b, c, d, e}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_15738270294669000 ==
/\ Len(AtoB) <= 3
/\ Len(BtoA) <= 3
----
=============================================================================
\* Modification History
\* Created Fri Nov 15 09:10:29 EST 2019 by isaac
