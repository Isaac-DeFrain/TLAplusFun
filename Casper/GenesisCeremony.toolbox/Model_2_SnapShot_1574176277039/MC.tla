---- MODULE MC ----
EXTENDS GenesisCeremony, TLC

\* CONSTANT definitions @modelParameterConstants:0Nodes
const_157417627601928000 == 
{[id |-> 1, bootstrap |-> 2, status |-> "genesis_validator"], [id |-> 2, bootstrap |-> 3, status |-> "genesis_validator"], [id |-> 3, bootstrap |-> 1, status |-> "genesis_validator"]}
----

\* Constant expression definition @modelExpressionEval
const_expr_157417627601929000 == 
Doubled
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157417627601929000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_157417627601930000 ==
FALSE/\nInMsg = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157417627601931000 ==
FALSE/\nInMsg' = nInMsg
----
=============================================================================
\* Modification History
\* Created Tue Nov 19 10:11:16 EST 2019 by isaac
