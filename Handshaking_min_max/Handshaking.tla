---------- MODULE Handshaking ----------

EXTENDS FiniteSets, Naturals

CONSTANTS
    NODES, \* set of nodes in the network
    MIN,   \* minimum number of connections
    MAX    \* maximum number of connections

VARIABLES
    connect,     \* tuple of nodes to make a connection with
    connections, \* tuple of each node's connections
    messages,    \* tuple of each node's incoming messages
    waiting      \* tuple of nodes each node is waiting for a response from

vars == <<connect, connections, messages, waiting>>

ASSUME NODES \subseteq Nat
ASSUME MIN \in Nat /\ MIN > 0
ASSUME MAX \in Nat /\ MIN <= MAX /\ MAX < Cardinality(NODES)
\* For combinatorial reasons, we must also have:
ASSUME
    LET N == Cardinality(NODES) IN
    IF N = 3 THEN MAX /= 1 ELSE MAX /= 2 /\ MAX /= N - 2

Messages == [ type : {"conn_req", "ack", "nack"}, from : NODES ]

Requested(m, n) == [type |-> "conn_req", from |-> m] \in messages[n]

(***********)
(* Actions *)
(***********)

try_connect(m, n) ==
    \* node [m] sends a connection request message to node [n]
    /\ messages' = [ messages EXCEPT ![n] = @ \cup {[type |-> "conn_req", from |-> m]} ]
    \* node [m] is now waiting for a response from node [n]
    /\ waiting' = [ waiting EXCEPT ![m] = @ \cup {n} ]
    /\ UNCHANGED <<connect, connections>>

TryConnect == \E m, n \in NODES :
    /\ m /= n
    \* both nodes haven't exceeded the maximum number of connections
    /\ Cardinality(connections[m]) < MAX
    /\ Cardinality(connections[n]) < MAX
    \* node [m] is not connected to or waiting for a response from node [n]
    /\ n \notin connect[m]
    /\ n \notin connections[m]
    /\ n \notin waiting[m]
    \* node [m] requests to connect with node [n]
    /\ try_connect(m, n)

ack(m, n) ==
    \* node [m] can only ack if they and node [n] have not surpassed MAX connections
    /\ Cardinality(connections[m]) < MAX
    /\ Cardinality(connections[n]) < MAX
    /\ messages' = [ messages EXCEPT ![n] = @ \cup {[type |-> "ack", from |-> m]},
                                     ![m] = @ \ {[type |-> "conn_req", from |-> n]} ]
    /\ waiting' = [ waiting EXCEPT ![m] = @ \cup {n} ]
    /\ UNCHANGED <<connect, connections>>

nack(m, n) ==
    \* node [m] can only nack if they and node [n] have both surpassed MIN connections
    /\ Cardinality(connections[m]) >= MIN
    /\ Cardinality(connections[n]) >= MIN
    \* node [m] can only nack a connection request from node [n] if they are already awaiting a response
    /\ ~Requested(m, n)
    /\ messages' = [ messages EXCEPT ![n] = @ \cup {[type |-> "nack", from |-> m]},
                                     ![m] = @ \ {[type |-> "conn_req", from |-> n]} ]
    /\ UNCHANGED <<connect, connections, waiting>>

ack_connect(m, n) ==
    /\ messages' = [ messages EXCEPT ![n] = @ \cup {[type |-> "ack", from |-> m]},
                                     ![m] = @ \ {[type |-> "conn_req", from |-> n]} ]
    /\ waiting' = [ waiting EXCEPT ![m] = @ \ {n} ]
    /\ connect' = [ connect EXCEPT ![m] = @ \cup {n} ]
    /\ UNCHANGED connections

respond(n) ==
    LET msg  == CHOOSE m \in messages[n] : TRUE
        type == msg.type
        from == msg.from
    IN
    CASE type = "conn_req" ->
         CASE \* if one node has too few connections and the other can make another connection, ack
              \/ /\ Cardinality(connections[n]) < MIN
                 /\ Cardinality(connections[from]) < MAX
              \/ /\ Cardinality(connections[n]) < MAX
                 /\ Cardinality(connections[from]) < MIN -> ack(n, from)
           [] \* if either node has MAX connections, nack
              \/ Cardinality(connections[n]) = MAX
              \/ Cardinality(connections[from]) = MAX -> nack(n, from)
           [] OTHER -> ack(n, from) \/ nack(n, from)
      [] type = "ack" -> IF /\ from \in waiting[n]
                            /\ Cardinality(connections[n]) < MAX
                            /\ Cardinality(connections[from]) < MAX
                         THEN ack_connect(n, from)
                         ELSE nack(n, from)
      [] type = "nack" -> /\ waiting' = [ waiting EXCEPT ![n] = @ \ {from} ]
                          /\ messages' = [ messages EXCEPT ![n] = @ \ {msg} ]
                          /\ connect' = [ connect EXCEPT ![n] = @ \ {from} ]
                          /\ UNCHANGED connections

Respond == \E n \in NODES :
    /\ messages[n] /= {}
    /\ respond(n)

Connect == \E m, n \in NODES :
    /\ m /= n
    /\ m \in connect[n]
    /\ n \in connect[m]
    /\ connect' = [ connect EXCEPT ![m] = @ \ {n}, ![n] = @ \ {m} ]
    /\ connections' = [ connections EXCEPT ![m] = @ \cup {n}, ![n] = @ \cup {m} ]
    /\ messages' = [ messages EXCEPT ![m] = @ \ {[type |-> "ack", from |-> n]},
                                     ![n] = @ \ {[type |-> "ack", from |-> m]} ]
    /\ UNCHANGED waiting

(*****************)
(* Specification *)
(*****************)

\* initially there are no connections
Init ==
    /\ connect = [ n \in NODES |-> {} ]
    /\ connections = [ n \in NODES |-> {} ]
    /\ messages = [ n \in NODES |-> {} ]
    /\ waiting = [ n \in NODES |-> {} ]

Next ==
    \/ TryConnect
    \/ Respond
    \/ Connect

Fairness ==
    /\ WF_vars(TryConnect)
    /\ WF_vars(Respond)
    /\ WF_vars(Connect)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************)
(* Invariants & Properties *)
(***************************)

TypeOK ==
    /\ \A n \in NODES : connect[n] \subseteq NODES
    /\ \A n \in NODES : connections[n] \subseteq NODES
    /\ \A n \in NODES : messages[n] \subseteq Messages
    /\ \A n \in NODES : waiting[n] \subseteq NODES

Safety ==
    \* no self connections or messages
    /\ \A n \in NODES :
        /\ n \notin connect[n]
        /\ n \notin connections[n]
        /\ n \notin waiting[n]
        /\ n \notin { msg.from : msg \in messages[n] }
    \* symmetric connections
    /\ \A m, n \in NODES : m \in connections[n] <=> n \in connections[m]
    \* never exceed MAX connections
    /\ \A n \in NODES : Cardinality(connections[n]) <= MAX

Liveness ==
    /\ \A m, n \in NODES : Requested(m, n) => []<><<ack(n, m) \/ nack(n, m)>>_vars
    /\ <>[](\A n \in NODES : Cardinality(connections[n]) >= MIN)

========================================
