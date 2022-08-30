---- MODULE B ----

EXTENDS Naturals, Sequences

VARIABLES
    count,
    switch,
    timer

vars == <<count, switch, timer>>

Init ==
    /\ count = 0
    /\ switch = TRUE
    /\ timer = 0

Count ==
    /\ switch
    /\ count < 10
    /\ count' = count + 2
    /\ UNCHANGED <<switch, timer>>

Switch ==
    /\ switch
    /\ count < 10
    /\ switch' = FALSE
    /\ timer' = 3
    /\ UNCHANGED count

Timer ==
    /\ ~switch
    /\ timer > 0
    /\ timer' = timer - 1
    /\ UNCHANGED <<count, switch>>

SwitchBack ==
    /\ ~switch
    /\ timer = 0
    /\ switch' = TRUE
    /\ UNCHANGED <<count, timer>>

Next ==
    \/ Count
    \/ Switch
    \/ SwitchBack
    \/ Timer

Spec == Init /\ [][Next]_vars

==================
