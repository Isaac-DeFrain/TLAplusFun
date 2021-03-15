---------- MODULE PeerDiscovery ----------

EXTENDS FiniteSets, Naturals

CONSTANT NODES \* set of node IDs

VARIABLES
    dns,  \* tuple of each node's DNS flag
    peers \* tuple of each node's incoming message queue

vars == <<dns, peers>>

ASSUME NODES \subseteq Nat
ASSUME Cardinality(NODES) >= 3

(***********)
(* Actions *)
(***********)

\* node [n] requests peers from DNS
request_dns(n) == \E ns \in SUBSET (NODES \ {n}) :
    /\ Cardinality(ns) >= 2
    /\ dns' = [ dns EXCEPT ![n] = ~@ ]
    /\ peers' = [ peers EXCEPT ![n] = ns ]

\* a node with an empty peer set requests peers from the DNS
Request_DNS == \E n \in NODES :
    /\ dns[n]
    /\ request_dns(n)

request_peer(m, n) ==
    \* node [m] requests peers from node [n]
    /\ peers' = [ peers EXCEPT ![m] = @ \cup (peers[n] \ {m}) ]
    /\ UNCHANGED dns

\* a node requests peers from a peer
Request_peer == \E m \in NODES : \E n \in peers[m] : request_peer(m, n)

(*****************)
(* Specification *)
(*****************)

Init ==
    /\ dns = [ n \in NODES |-> TRUE ]
    /\ peers = [ n \in NODES |-> {} ]

Next == Request_DNS \/ Request_peer

Fairness ==
    /\ WF_peers(Request_DNS)
    /\ WF_peers(Request_peer)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************)
(* Invariants & Properties *)
(***************************)

TypeOK ==
    /\ \A n \in NODES : dns[n] \in BOOLEAN
    /\ \A n \in NODES : peers[n] \subseteq NODES

Safety == \A n \in NODES : n \notin peers[n]

Liveness ==
    /\ <>(\A n \in NODES : ~dns[n] /\ Cardinality(peers[n]) >= 2)
    /\ <>(\E m, n \in NODES : /\ m /= n
                              /\ Cardinality(peers[m]) > 2
                              /\ Cardinality(peers[n]) > 2)

==========================================
