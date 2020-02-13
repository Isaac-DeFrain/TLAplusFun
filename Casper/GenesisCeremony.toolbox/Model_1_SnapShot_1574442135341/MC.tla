---- MODULE MC ----
EXTENDS GenesisCeremony, TLC

\* Constant expression definition @modelExpressionEval
const_expr_157444213332511000 == 
Op(Mult,2,3)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157444213332511000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_157444213332512000 ==
FALSE/\nInMsg = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157444213332513000 ==
FALSE/\nInMsg' = nInMsg
----
=============================================================================
\* Modification History
\* Created Fri Nov 22 12:02:13 EST 2019 by isaac
