---- MODULE MC ----
EXTENDS PaxosCommit, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT definitions Acceptor
const_157376804987791000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions RM
const_157376804987792000 == 
{r1, r2}
----

\* SYMMETRY definition
symm_157376804987793000 == 
Permutations(const_157376804987791000) \union Permutations(const_157376804987792000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballot
const_157376804987794000 == 
{0, 1}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
const_157376804987795000 == 
{{a1, a2}, {a1, a3}, {a2, a3}}
----

=============================================================================
\* Modification History
\* Created Thu Nov 14 16:47:29 EST 2019 by isaac
