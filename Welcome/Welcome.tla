---------- MODULE Welcome ----------

EXTENDS Naturals, Sequences

CONSTANT NODES \* set of node IDs

VARIABLES
    connected, \* tuple of each node's set of connected peers
    contacted, \* tuple of each node's set of contacted peers
    messages   \* tuple of each node's incoming message queue

vars == <<connected, contacted, messages>>

ASSUME NODES \subseteq Nat

Messages == [ type : {"request", "response"}, from : NODES ]

(***********)
(* Actions *)
(***********)

request(m, n) ==
    \* node [m] sends a request message to node [n]
    /\ messages' = [ messages EXCEPT ![n] = Append(@, [type |-> "request", from |-> m]) ]
    \* node [m] is now waiting for a response from node [n]
    /\ contacted' = [ contacted EXCEPT ![m] = @ \cup {n} ]
    /\ UNCHANGED connected

Request == \E m, n \in NODES :
    /\ m /= n
    \* node [m] is not currently connected to or waiting for a response from node [n]
    /\ n \notin contacted[m] \cup connected[m]
    /\ request(m, n)

reponse_req(m, n) ==
    \* node [m] sends a request message to node [n]
    /\ messages' = [ messages EXCEPT ![m] = Tail(@),
                                     ![n] = Append(@, [type |-> "response", from |-> m]) ]
    \* node [m] is no longer waiting for a response from node [n]
    /\ contacted' = [ contacted EXCEPT ![m] = @ \cup {n} ]
    /\ UNCHANGED connected

reponse_res(m, n) ==
    \* node [m] sends a request message to node [n]
    /\ messages' = [ messages EXCEPT ![m] = Tail(@),
                                     ![n] = Append(@, [type |-> "response", from |-> m]) ]
    \* node [m] is no longer waiting for a response from node [n]
    /\ contacted' = [ contacted EXCEPT ![m] = @ \ {n} ]
    /\ connected' = [ connected EXCEPT ![m] = @ \cup {n} ]

drop_msg(n) ==
    /\ messages' = [ messages EXCEPT ![n] = Tail(@) ]
    /\ UNCHANGED <<connected, contacted>>

Response == \E m \in NODES :
    /\ messages[m] /= <<>>
    /\ LET msg  == Head(messages[m])
           type == msg.type
           from == msg.from
       IN
       IF type = "request"
       THEN reponse_req(m, from)
       ELSE IF from \in contacted[m]
            THEN reponse_res(m, from)
            ELSE drop_msg(m)

(*****************)
(* Specification *)
(*****************)

Init ==
    /\ connected = [ n \in NODES |-> {} ]
    /\ contacted = [ n \in NODES |-> {} ]
    /\ messages  = [ n \in NODES |-> <<>> ]

Next == Request \/ Response

Fairness ==
    /\ WF_vars(Request)
    /\ WF_vars(Response)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************)
(* Invariants & Properties *)
(***************************)

TypeOK ==
    /\ \A n \in NODES : connected[n] \subseteq NODES
    /\ \A n \in NODES : contacted[n] \subseteq NODES
    /\ \A n \in NODES : messages[n] \in Seq(Messages)

Safety ==
    /\ \A n \in NODES : n \notin connected[n]
    /\ \A n \in NODES : n \notin contacted[n]

Liveness ==
    /\ \A m, n \in NODES : m \in contacted[n] ~> m \in connected[n]
    /\ \A m, n \in NODES : m \in connected[n] ~> n \in connected[m]

====================================