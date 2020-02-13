---- MODULE MC ----
EXTENDS TwoPhase, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
const_157376598334240000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_157376598334241000 == 
Permutations(const_157376598334240000)
----

=============================================================================
\* Modification History
\* Created Thu Nov 14 16:13:03 EST 2019 by isaac
