---- MODULE MC ----
EXTENDS CBCCasperSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0nodes
const_1576804078323121000 == 
{1,2,3,4,5}
----

\* CONSTANT definitions @modelParameterConstants:1weights
const_1576804078323122000 == 
{5,6,10,11,15}
----

\* CONSTANT definitions @modelParameterConstants:2values
const_1576804078323123000 == 
{"a","b","c","d","e","f","g","h","i","j","k","l","m"}
----

\* CONSTANT definitions @modelParameterConstants:3threshold
const_1576804078323124000 == 
8
----

\* Constant expression definition @modelExpressionEval
const_expr_1576804078323125000 == 
LatestEsts({Msg("a",1,{genesis}),genesis,Msg("b",2,{genesis})})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1576804078323125000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1576804078323126000 ==
FALSE/\sent_msgs = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1576804078323127000 ==
FALSE/\sent_msgs' = sent_msgs
----
=============================================================================
\* Modification History
\* Created Thu Dec 19 20:07:58 EST 2019 by isaac
