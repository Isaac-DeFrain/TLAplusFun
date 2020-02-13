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
const_157376734531050000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions RM
const_157376734531051000 == 
{r1, r2}
----

\* SYMMETRY definition
symm_157376734531052000 == 
Permutations(const_157376734531050000) \union Permutations(const_157376734531051000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballot
const_157376734531053000 == 
{0, 1}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
const_157376734531054000 == 
{{a1, a2}, {a1, a3}, {a2, a3}}
----

=============================================================================
\* Modification History
\* Created Thu Nov 14 16:35:45 EST 2019 by isaac
