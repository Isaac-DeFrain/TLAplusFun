---- MODULE MC ----
EXTENDS GenesisCeremony, TLC

\* CONSTANT definitions @modelParameterConstants:0Nodes
const_15741729617046000 == 
{[id |-> 1, bootstrap |-> 2, status |-> "genesis_validator"], [id |-> 2, bootstrap |-> 3, status |-> "genesis_validator"], [id |-> 3, bootstrap |-> 1, status |-> "genesis_validator"]}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_15741729617047000 ==
\A n \in nodes : Len(nOutStreamMsg[n]) < 5
----
=============================================================================
\* Modification History
\* Created Tue Nov 19 09:16:01 EST 2019 by isaac
