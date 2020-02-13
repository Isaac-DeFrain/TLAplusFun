---- MODULE MC ----
EXTENDS CBCCasperSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f
----

\* MV CONSTANT definitions values
const_157634701798813000 == 
{a, b, c, d, e, f}
----

\* CONSTANT definitions @modelParameterConstants:0nodes
const_157634701798814000 == 
{1,2,3,4,5}
----

\* CONSTANT definitions @modelParameterConstants:1weights
const_157634701798815000 == 
{2,3,4,5,6}
----

\* CONSTANT definitions @modelParameterConstants:4threshold
const_157634701798816000 == 
4
----

\* Constant expression definition @modelExpressionEval
const_expr_157634701798817000 == 
UnionEach(<<{1,2},{3,4},{5,6}>>,{"a"})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157634701798817000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_157634701798818000 ==
FALSE/\sent_msgs = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157634701798819000 ==
FALSE/\sent_msgs' = sent_msgs
----
=============================================================================
\* Modification History
\* Created Sat Dec 14 13:10:17 EST 2019 by isaac
