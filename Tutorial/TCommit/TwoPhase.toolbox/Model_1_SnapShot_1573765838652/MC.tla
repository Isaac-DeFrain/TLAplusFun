---- MODULE MC ----
EXTENDS TwoPhase, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
const_157376583652633000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_157376583652634000 == 
Permutations(const_157376583652633000)
----

=============================================================================
\* Modification History
\* Created Thu Nov 14 16:10:36 EST 2019 by isaac
