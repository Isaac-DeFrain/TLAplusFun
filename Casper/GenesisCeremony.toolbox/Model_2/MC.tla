---- MODULE MC ----
EXTENDS GenesisCeremony, TLC

\* CONSTANT definitions @modelParameterConstants:0Nodes
const_157417636006445000 == 
{[id |-> 1, bootstrap |-> 2, status |-> "ceremony_master"], [id |-> 2, bootstrap |-> 3, status |-> "genesis_validator"], [id |-> 3, bootstrap |-> 1, status |-> "genesis_validator"]}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_157417636006446000 ==
\A n \in nodes : Len(nOutStreamMsg[n]) < 5
----
=============================================================================
\* Modification History
\* Created Tue Nov 19 10:12:40 EST 2019 by isaac
