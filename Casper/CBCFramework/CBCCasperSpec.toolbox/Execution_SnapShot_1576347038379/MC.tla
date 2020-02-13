---- MODULE MC ----
EXTENDS CBCCasperSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f
----

\* MV CONSTANT definitions values
const_157634703735827000 == 
{a, b, c, d, e, f}
----

\* CONSTANT definitions @modelParameterConstants:0nodes
const_157634703735828000 == 
{1,2,3,4,5}
----

\* CONSTANT definitions @modelParameterConstants:1weights
const_157634703735829000 == 
{2,3,4,5,6}
----

\* CONSTANT definitions @modelParameterConstants:4threshold
const_157634703735830000 == 
4
----

\* Constant expression definition @modelExpressionEval
const_expr_157634703735831000 == 
UnionEach(<<{1,2},{3,4},{5,6}>>,{7})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157634703735831000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_157634703735832000 ==
FALSE/\sent_msgs = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157634703735833000 ==
FALSE/\sent_msgs' = sent_msgs
----
=============================================================================
\* Modification History
\* Created Sat Dec 14 13:10:37 EST 2019 by isaac
