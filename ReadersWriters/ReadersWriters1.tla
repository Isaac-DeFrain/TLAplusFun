-------------------------- MODULE ReadersWriters1 -------------------------
\*  https://en.wikipedia.org/wiki/Readers%E2%80%93writers_problem

(* This spec does not satisfy Liveness... *)

EXTENDS FiniteSets, Naturals

CONSTANT Actors

VARIABLES readers, writers

vars == <<readers, writers>>

Init ==
    /\ readers = {}
    /\ writers = {}

BusyActors == readers \cup writers

Reading(actor) ==
    /\ actor \notin BusyActors
    /\ writers = {}
    /\ readers' = readers \union {actor}
    /\ UNCHANGED writers
                  
Writing(actor) ==
    /\ actor \notin BusyActors
    /\ BusyActors = {}
    /\ writers' = writers \union {actor }
    /\ UNCHANGED readers

StopActivity(actor) ==
    /\ actor \in BusyActors
    /\ \/ /\ actor \in readers
          /\ readers' = readers \ {actor}
          /\ UNCHANGED writers
       \/ /\ actor \in writers
          /\ writers' = writers \ {actor}
          /\ UNCHANGED readers

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors

Safety ==
    /\ readers /= {} => writers = {}
    /\ writers /= {} => readers = {}
    /\ Cardinality(writers) <= 1

Next == \E actor \in Actors :
    \/ Reading(actor)
    \/ Writing(actor)
    \/ StopActivity(actor)

Fairness == \A actor \in Actors :
    /\ SF_vars(Reading(actor))
    /\ SF_vars(Writing(actor))
    /\ WF_vars(StopActivity(actor))

Spec == Init /\ [][Next]_vars /\ Fairness

Liveness ==
    /\ []<>(readers /= {})
    /\ []<>(writers /= {})

=============================================================================