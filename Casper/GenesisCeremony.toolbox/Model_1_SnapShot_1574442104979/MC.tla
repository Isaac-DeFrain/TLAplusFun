---- MODULE MC ----
EXTENDS GenesisCeremony, TLC

\* Constant expression definition @modelExpressionEval
const_expr_15744421036175000 == 
Op(Add,2,3)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_15744421036175000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_15744421036176000 ==
FALSE/\nInMsg = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_15744421036177000 ==
FALSE/\nInMsg' = nInMsg
----
=============================================================================
\* Modification History
\* Created Fri Nov 22 12:01:43 EST 2019 by isaac
