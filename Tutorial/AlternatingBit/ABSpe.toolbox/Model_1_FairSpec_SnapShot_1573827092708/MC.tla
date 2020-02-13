---- MODULE MC ----
EXTENDS AB, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e
----

\* MV CONSTANT definitions Data
const_157382709069114000 == 
{a, b, c, d, e}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_157382709069115000 ==
/\ Len(AtoB) <= 3
/\ Len(BtoA) <= 3
----
=============================================================================
\* Modification History
\* Created Fri Nov 15 09:11:30 EST 2019 by isaac
