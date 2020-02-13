---- MODULE MC ----
EXTENDS GenesisCeremony, TLC

\* CONSTANT definitions @modelParameterConstants:0Nodes
const_1574130971144106000 == 
{[id |-> 1, bootstrap |-> 2, status |-> "ceremony_master"], [id |-> 2, bootstrap |-> 3, status |-> "genesis_validator"], [id |-> 3, bootstrap |-> 1, status |-> "genesis_validator"]}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1574130971144107000 ==
\A n \in nodes : Len(nOutStreamMsg[n]) < 3
----
=============================================================================
\* Modification History
\* Created Mon Nov 18 21:36:11 EST 2019 by isaac
