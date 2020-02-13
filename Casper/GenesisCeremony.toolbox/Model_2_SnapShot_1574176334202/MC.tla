---- MODULE MC ----
EXTENDS GenesisCeremony, TLC

\* CONSTANT definitions @modelParameterConstants:0Nodes
const_157417633319042000 == 
{[id |-> 1, bootstrap |-> 2, status |-> "genesis_validator"], [id |-> 2, bootstrap |-> 3, status |-> "genesis_validator"], [id |-> 3, bootstrap |-> 1, status |-> "genesis_validator"]}
----

\* INIT definition @modelBehaviorNoSpec:0
init_157417633319043000 ==
FALSE/\nInMsg = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_157417633319044000 ==
FALSE/\nInMsg' = nInMsg
----
=============================================================================
\* Modification History
\* Created Tue Nov 19 10:12:13 EST 2019 by isaac
