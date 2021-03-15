---------- MODULE Handshaking ----------

EXTENDS Naturals

CONSTANT NODES \* set of nodes in the network

VARIABLES
    connect,     \* tuple of nodes to make a connection with
    connections, \* tuple of each node's connections
    messages,    \* tuple of each node's incoming messages
    waiting      \* tuple of nodes each node is waiting for a response from

vars == <<connect, connections, messages, waiting>>

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
    \* node [m] is not connected to or waiting for a response from node [n]
    /\ n \notin connect[m]
    /\ n \notin connections[m]
    /\ n \notin waiting[m]
    \* node [m] requests to connect with node [n]
    /\ try_connect(m, n)

ack(m, n) ==
    /\ messages' = [ messages EXCEPT
                        ![n] = @ \cup {[type |-> "ack", from |-> m]},
                        ![m] = @ \ {[type |-> "conn_req", from |-> n]} ]
    /\ waiting' = [ waiting EXCEPT ![m] = @ \cup {n} ]
    /\ UNCHANGED <<connect, connections>>

nack(m, n) ==
    /\ connections[m] /= {}
    /\ ~Requested(m, n)
    /\ messages' = [ messages EXCEPT
                        ![n] = @ \cup {[type |-> "nack", from |-> m]},
                        ![m] = @ \ {[type |-> "conn_req", from |-> n]} ]
    /\ UNCHANGED <<connect, connections, waiting>>

ack_connect(m, n) ==
    /\ messages' = [ messages EXCEPT ![n] = @ \cup {[type |-> "ack", from |-> m]} ]
    /\ waiting' = [ waiting EXCEPT ![m] = @ \ {n} ]
    /\ connect' = [ connect EXCEPT ![m] = @ \cup {n} ]
    /\ UNCHANGED connections

respond(n) ==
    LET msg  == CHOOSE m \in messages[n] : TRUE
        type == msg.type
        from == msg.from
    IN
    CASE type = "conn_req" -> ack(n, from) \/ nack(n, from)
      [] type = "ack" -> IF from \in waiting[n]
                         THEN ack_connect(n, from)
                         ELSE UNCHANGED vars
      [] type = "nack" -> /\ waiting' = [ waiting EXCEPT ![n] = @ \ {from} ]
                          /\ messages' = [ messages EXCEPT ![n] = @ \ {msg} ]
                          /\ UNCHANGED <<connect, connections>>

Respond == \E n \in NODES :
    /\ messages[n] /= {}
    /\ respond(n)

Connect == \E m, n \in NODES :
    /\ m /= n
    /\ m \in connect[n]
    /\ n \in connect[m]
    /\ connect' = [ connect EXCEPT ![m] = @ \ {n}, ![n] = @ \ {m} ]
    /\ connections' = [ connections EXCEPT ![m] = @ \cup {n}, ![n] = @ \cup {m} ]
    /\ UNCHANGED <<messages, waiting>>

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
    \* all connections are symmetric
    /\ \A m, n \in NODES : m \in connections[n] <=> n \in connections[m]

Liveness ==
    /\ \A m, n \in NODES : Requested(m, n) => []<><<ack(n, m) \/ nack(n, m)>>_vars
    /\ <>[](\A n \in NODES : connections[n] /= {})

========================================
