-------------------------- MODULE ReadersWriters2 -------------------------
\*  https://en.wikipedia.org/wiki/Readers%E2%80%93writers_problem

(* Full solution *)

EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES
    readers, \* set of processes currently reading
    writers, \* set of processes currently writing
    waiting  \* queue of processes waiting to access the resource

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

ToSet(s) == { s[i] : i \in DOMAIN s }

fst(s)  == s[1]
nfst(s) == ~s[1]

WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, fst)) }

WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, nfst)) }

---------------------------------------------------------------------------

\* Actions

TryRead(actor) ==
    /\ actor \notin WaitingToRead
    /\ waiting' = Append(waiting, <<TRUE, actor>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite(actor) ==
    /\ actor \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<FALSE, actor>>)
    /\ UNCHANGED <<readers, writers>>

Read(actor) ==
    /\ readers' = readers \union {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers
                  
Write(actor) ==
    /\ readers = {}
    /\ writers' = writers \union {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    /\ LET pair  == Head(waiting)
           read  == pair[1]
           actor == pair[2]
       IN IF read
          THEN Read(actor)
          ELSE Write(actor)

Stop == \E actor \in readers \cup writers : StopActivity(actor)

---------------------------------------------------------------------------

\* Invariants

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq(BOOLEAN \times Actors)

Safety ==
    /\ readers /= {} => writers = {}
    /\ writers /= {} => readers = {}
    /\ Cardinality(writers) <= 1

---------------------------------------------------------------------------

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

Fairness ==
    /\ \A actor \in Actors : SF_vars(TryRead(actor))
    /\ \A actor \in Actors : SF_vars(TryWrite(actor))
    /\ SF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

Spec == Init /\ [][Next]_vars /\ Fairness

Liveness ==
    /\ []<>(readers /= {})
    /\ []<>(writers /= {})

============================================================================