---- MODULE MC ----
EXTENDS GenesisCeremony, TLC

\* Constant expression definition @modelExpressionEval
const_expr_157444224363929000 == 
Op(Mult,2,3)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157444224363929000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_157444224363930000 ==
FALSE/\nInMsg = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157444224363931000 ==
FALSE/\nInMsg' = nInMsg
----
=============================================================================
\* Modification History
\* Created Fri Nov 22 12:04:03 EST 2019 by isaac
