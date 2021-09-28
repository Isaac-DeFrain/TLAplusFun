---- MODULE A ----

EXTENDS Naturals, Sequences, TLC

VARIABLES
    count,
    switch,
    timer

vars == <<count, switch, timer>>

Init ==
    /\ count = 0
    /\ switch = TRUE
    /\ timer = 0

Count(data) ==
    LET b == data[1]
        n == data[2]
    IN
    /\ b
    /\ switch
    /\ count < 10
    /\ count' = count + n
    /\ UNCHANGED <<switch, timer>>

Switch(data) ==
    /\ switch
    /\ switch' = FALSE
    /\ count' = 0
    /\ timer' = data[1]

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
    \/ \E data \in BOOLEAN \X 1..10 : Count(data)
    \/ \E data \in 1..5 : Switch(<<data>>)
    \/ SwitchBack
    \/ Timer

Spec == Init /\ [][Next]_vars

==================
