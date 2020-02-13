---- MODULE MC ----
EXTENDS GenesisCeremony, TLC

\* CONSTANT definitions @modelParameterConstants:0Nodes
const_157417563724821000 == 
{[id |-> 1, bootstrap |-> 2, status |-> "genesis_validator"], [id |-> 2, bootstrap |-> 3, status |-> "genesis_validator"], [id |-> 3, bootstrap |-> 1, status |-> "genesis_validator"]}
----

\* INIT definition @modelBehaviorNoSpec:0
init_157417563724822000 ==
FALSE/\nInMsg = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157417563724823000 ==
FALSE/\nInMsg' = nInMsg
----
=============================================================================
\* Modification History
\* Created Tue Nov 19 10:00:37 EST 2019 by isaac
