---- MODULE Compose ----

EXTENDS Parser

\* model variables
VARIABLES
    count,
    switch

\* trace reader variable
VARIABLE i

vars == <<count, switch, i>>

Counter == INSTANCE Counter
Switch  == INSTANCE Switch

Trace == parser("./ex/ex2.txt")

Read ==
    LET state == Trace[1] IN
    /\ i = 1
    /\ count = state[1]
    /\ switch = state[2]

Init ==
    /\ Read
    /\ Counter!Init
    /\ Switch!Init

ReadNext ==
    LET state == Trace[i'] IN
    /\ i < Len(Trace)
    /\ i' = i + 1
    /\ count' = state[1]
    /\ switch' = state[2]

\* Counter action, Switch variables unchanged
CounterAction ==
    /\ Counter!Next
    /\ UNCHANGED Switch!vars

\* Switch action, Counter variables unchanged
SwitchAction ==
    /\ Switch!Next
    /\ UNCHANGED Counter!vars

\* model stuttering step
ModelStutter ==
    UNCHANGED <<Counter!vars, Switch!vars>>

Action ==
    \/ CounterAction
    \/ SwitchAction
    \/ ModelStutter

Next ==
    /\ ReadNext
    /\ Action

Spec == Init /\ [][Next]_vars

Incorrect == i < Len(Trace)

========================
