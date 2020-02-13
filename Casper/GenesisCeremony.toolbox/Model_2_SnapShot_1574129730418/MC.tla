---- MODULE MC ----
EXTENDS GenesisCeremony, TLC

\* CONSTANT definitions @modelParameterConstants:0Nodes
const_157412969103598000 == 
{[id |-> 1, bootstrap |-> 2, status |-> "ceremony_master"], [id |-> 2, bootstrap |-> 3, status |-> "genesis_validator"], [id |-> 3, bootstrap |-> 1, status |-> "new"]}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_157412969103599000 ==
\A n \in nodes : Len(nOutStreamMsg[n]) < 3
----
=============================================================================
\* Modification History
\* Created Mon Nov 18 21:14:51 EST 2019 by isaac
