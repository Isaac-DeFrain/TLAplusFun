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
const_157376757550663000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions RM
const_157376757550664000 == 
{r1, r2}
----

\* SYMMETRY definition
symm_157376757550665000 == 
Permutations(const_157376757550663000) \union Permutations(const_157376757550664000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballot
const_157376757550666000 == 
{0, 1}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
const_157376757550667000 == 
{{a1, a2}, {a1, a3}, {a2, a3}}
----

=============================================================================
\* Modification History
\* Created Thu Nov 14 16:39:35 EST 2019 by isaac
