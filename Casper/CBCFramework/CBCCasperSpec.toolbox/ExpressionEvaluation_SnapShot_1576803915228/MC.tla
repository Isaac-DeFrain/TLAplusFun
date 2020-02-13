---- MODULE MC ----
EXTENDS CBCCasperSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0nodes
const_1576803914211100000 == 
{1,2,3,4,5}
----

\* CONSTANT definitions @modelParameterConstants:1weights
const_1576803914211101000 == 
{5,6,10,11,15}
----

\* CONSTANT definitions @modelParameterConstants:2values
const_1576803914211102000 == 
{"a","b","c","d","e","f","g","h","i","j","k","l","m"}
----

\* CONSTANT definitions @modelParameterConstants:3threshold
const_1576803914211103000 == 
8
----

\* Constant expression definition @modelExpressionEval
const_expr_1576803914211104000 == 
Later(genesis,{Msg("a",1,{genesis}),genesis,Msg("b",2,{genesis})})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1576803914211104000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1576803914211105000 ==
FALSE/\sent_msgs = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1576803914211106000 ==
FALSE/\sent_msgs' = sent_msgs
----
=============================================================================
\* Modification History
\* Created Thu Dec 19 20:05:14 EST 2019 by isaac
