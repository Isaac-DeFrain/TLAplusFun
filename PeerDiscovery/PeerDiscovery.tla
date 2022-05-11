---------- MODULE PeerDiscovery ----------

EXTENDS FiniteSets, Naturals

CONSTANT N

VARIABLES
    dns,                    \* dns map of shared peers
    dns_request_enabled,    \* tuple of each node's DNS flag
    peers                   \* tuple of each node's peer set

vars == <<dns, dns_request_enabled, peers>>
Nodes == 1..N

ASSUME N > 3

(***********)
(* Actions *)
(***********)

\* a node requests peers from the DNS
Request_DNS(n, ns) ==
    LET ps == UNION { dns[m] : m \in Nodes } IN
    /\ dns_request_enabled[n]
    /\ Cardinality(ns) >= 2
    /\ \/ ps = Nodes
       \/ ns \cap ps # {}
       \/ \E m \in Nodes : dns[m] = {}
    /\ dns' = [ dns EXCEPT ![n] = ns ]
    /\ dns_request_enabled' = [ dns_request_enabled EXCEPT ![n] = FALSE ]
    /\ peers' = [ peers EXCEPT ![n] = ns ]

\* node [m] requests peers from a node [n]
\* if [n] doesn't already know about [m], then [m] is added to [n]'s peers
Request_peer(m, n) ==
    /\ n \in peers[m]
    /\ peers' = [ peers EXCEPT ![m] = @ \cup (peers[n] \ {m}),
                               ![n] = @ \cup {m} ]
    /\ UNCHANGED <<dns, dns_request_enabled>>

(*****************)
(* Specification *)
(*****************)

Init ==
    /\ dns = [ n \in Nodes |-> {} ]
    /\ dns_request_enabled = [ n \in Nodes |-> TRUE ]
    /\ peers = [ n \in Nodes |-> {} ]

Next ==
    \/ \E n \in Nodes : \E ns \in SUBSET (Nodes \ {n}) : Request_DNS(n, ns)
    \/ \E m, n \in Nodes : Request_peer(m, n)

Spec == Init /\ [][Next]_vars

Fairness == WF_vars(Next)

FairSpec == Spec /\ Fairness

(***************************)
(* Invariants & Properties *)
(***************************)

TypeOK ==
    /\ \A n \in Nodes : dns_request_enabled[n] \in BOOLEAN
    /\ \A n \in Nodes : peers[n] \subseteq Nodes

Safety == \A n \in Nodes : n \notin peers[n]

Liveness ==
    /\ <>[](\A n \in Nodes : ~dns_request_enabled[n] /\ Cardinality(peers[n]) >= 2)
    /\ <>(\E m, n \in Nodes :
            /\ m /= n
            /\ Cardinality(peers[m]) > 2
            /\ Cardinality(peers[n]) > 2
        )

==========================================
