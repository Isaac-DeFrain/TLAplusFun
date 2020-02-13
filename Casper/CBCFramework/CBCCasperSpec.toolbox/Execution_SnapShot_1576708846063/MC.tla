---- MODULE MC ----
EXTENDS CBCCasperSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f
----

\* MV CONSTANT definitions values
const_157670884402460000 == 
{a, b, c, d, e, f}
----

\* CONSTANT definitions @modelParameterConstants:0nodes
const_157670884402461000 == 
{1,2,3,4,5}
----

\* CONSTANT definitions @modelParameterConstants:1weights
const_157670884402462000 == 
<<2,3,4,5,6>>
----

\* CONSTANT definitions @modelParameterConstants:4threshold
const_157670884402463000 == 
4
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_157670884402464000 ==
\A n \in nodes : Len(sent_msgs[n]) < 10
----
=============================================================================
\* Modification History
\* Created Wed Dec 18 17:40:44 EST 2019 by isaac
