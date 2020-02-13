---- MODULE MC ----
EXTENDS CBCCasperSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0nodes
const_1576804359438163000 == 
{1,2,3,4,5}
----

\* CONSTANT definitions @modelParameterConstants:1weights
const_1576804359438164000 == 
{5,6,10,11,15}
----

\* CONSTANT definitions @modelParameterConstants:2values
const_1576804359438165000 == 
{"a","b","c","d","e","f","g","h","i","j","k","l","m"}
----

\* CONSTANT definitions @modelParameterConstants:3threshold
const_1576804359438166000 == 
8
----

\* Constant expression definition @modelExpressionEval
const_expr_1576804359438167000 == 
Cardinality(DepPlus(Msg("a",1,{genesis})))
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1576804359438167000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1576804359438168000 ==
FALSE/\sent_msgs = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1576804359438169000 ==
FALSE/\sent_msgs' = sent_msgs
----
=============================================================================
\* Modification History
\* Created Thu Dec 19 20:12:39 EST 2019 by isaac
