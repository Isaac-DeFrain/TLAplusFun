---- MODULE MC ----
EXTENDS CBCCasperSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f
----

\* MV CONSTANT definitions values
const_157670844322339000 == 
{a, b, c, d, e, f}
----

\* CONSTANT definitions @modelParameterConstants:0nodes
const_157670844322340000 == 
{1,2,3,4,5}
----

\* CONSTANT definitions @modelParameterConstants:1weights
const_157670844322341000 == 
{2,3,4,5,6}
----

\* CONSTANT definitions @modelParameterConstants:4threshold
const_157670844322342000 == 
4
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_157670844322343000 ==
\A n \in nodes : Len(sent_msgs[n]) < 10
----
=============================================================================
\* Modification History
\* Created Wed Dec 18 17:34:03 EST 2019 by isaac
