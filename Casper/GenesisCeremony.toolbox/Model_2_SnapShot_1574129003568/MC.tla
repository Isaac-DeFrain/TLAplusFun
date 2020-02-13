---- MODULE MC ----
EXTENDS GenesisCeremony, TLC

\* CONSTANT definitions @modelParameterConstants:0Nodes
const_157412897604284000 == 
{[id |-> 1, bootstrap |-> 2, status |-> "ceremony_master"], [id |-> 2, bootstrap |-> 3, status |-> "genesis_validator"], [id |-> 3, bootstrap |-> 1, status |-> "new"]}
----

=============================================================================
\* Modification History
\* Created Mon Nov 18 21:02:56 EST 2019 by isaac
