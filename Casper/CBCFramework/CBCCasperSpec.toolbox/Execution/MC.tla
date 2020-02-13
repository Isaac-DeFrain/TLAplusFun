---- MODULE MC ----
EXTENDS CBCCasperSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f
----

\* MV CONSTANT definitions values
const_1576712553848127000 == 
{a, b, c, d, e, f}
----

\* CONSTANT definitions @modelParameterConstants:0nodes
const_1576712553848128000 == 
{1,2,3,4,5}
----

\* CONSTANT definitions @modelParameterConstants:1weights
const_1576712553848129000 == 
<<2,3,4,5,6>>
----

\* CONSTANT definitions @modelParameterConstants:3threshold
const_1576712553848130000 == 
4
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1576712553848131000 ==
\A n \in nodes : Len(sent_msgs[n]) < 10
----
=============================================================================
\* Modification History
\* Created Wed Dec 18 18:42:33 EST 2019 by isaac
