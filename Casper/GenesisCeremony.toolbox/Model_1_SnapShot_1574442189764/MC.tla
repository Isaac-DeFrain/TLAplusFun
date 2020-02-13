---- MODULE MC ----
EXTENDS GenesisCeremony, TLC

\* Constant expression definition @modelExpressionEval
const_expr_157444218822517000 == 
Op(Mult,"2",3)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157444218822517000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_157444218822518000 ==
FALSE/\nInMsg = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157444218822519000 ==
FALSE/\nInMsg' = nInMsg
----
=============================================================================
\* Modification History
\* Created Fri Nov 22 12:03:08 EST 2019 by isaac
