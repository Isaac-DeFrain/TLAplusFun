---- MODULE MC ----
EXTENDS CBCCasperSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0nodes
const_1576804579982212000 == 
{1,2,3,4,5}
----

\* CONSTANT definitions @modelParameterConstants:1weights
const_1576804579982213000 == 
{5,6,10,11,15}
----

\* CONSTANT definitions @modelParameterConstants:2values
const_1576804579982214000 == 
{"a","b","c","d","e","f","g","h","i","j","k","l","m"}
----

\* CONSTANT definitions @modelParameterConstants:3threshold
const_1576804579982215000 == 
8
----

\* Constant expression definition @modelExpressionEval
const_expr_1576804579982216000 == 
Equivocation(Msg("a",2,{genesis}),Msg("b",2,{genesis}))
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1576804579982216000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1576804579982217000 ==
FALSE/\sent_msgs = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1576804579982218000 ==
FALSE/\sent_msgs' = sent_msgs
----
=============================================================================
\* Modification History
\* Created Thu Dec 19 20:16:19 EST 2019 by isaac
