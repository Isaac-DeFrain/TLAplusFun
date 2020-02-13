---- MODULE MC ----
EXTENDS GenesisCeremony, TLC

\* CONSTANT definitions @modelParameterConstants:0Nodes
const_157417537158014000 == 
{[id |-> 1, bootstrap |-> 2, status |-> "genesis_validator"], [id |-> 2, bootstrap |-> 3, status |-> "genesis_validator"], [id |-> 3, bootstrap |-> 1, status |-> "genesis_validator"]}
----

\* Constant expression definition @modelExpressionEval
const_expr_157417537158015000 == 
Doubled
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157417537158015000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_157417537158016000 ==
FALSE/\nInMsg = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157417537158017000 ==
FALSE/\nInMsg' = nInMsg
----
=============================================================================
\* Modification History
\* Created Tue Nov 19 09:56:11 EST 2019 by isaac
