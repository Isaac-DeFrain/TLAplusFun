---- MODULE Compose ----

EXTENDS Parser

\* model variables
VARIABLES
    count,
    switch,
    timer

\* action Trace reader variables
VARIABLES
    i,
    action

vars == <<count, switch, timer, i, action>>

Trace == parser("./ex/ex1.txt")

\* models have the same variables declared, but different actions
A == INSTANCE A
B == INSTANCE B

Translate(a) ==
    LET act  == a[1]
        data == a[2]
    IN
    CASE act = "Count_A"    -> A!Count(data)
      [] act = "Count_B"    -> B!Count
      [] act = "Switch_A"   -> A!Switch(data)
      [] act = "Switch_B"   -> B!Switch
      [] act = "Timer"      -> A!Timer
      [] act = "SwitchBack" -> A!SwitchBack

Read ==
    /\ i = 1
    /\ action = Trace[1]

Init ==
    /\ Read
    /\ A!Init
    /\ B!Init

ReadNext ==
    \* more actions to apply in Trace
    \/ /\ i < Len(Trace)
       /\ i' = i + 1
       /\ action' = Trace[i']
    \* no more actions in Trace
    \/ /\ i = Len(Trace)
       /\ i' = i + 1
       /\ action' = "Done"

Next ==
    /\ ReadNext
    /\ Translate(action)

Spec == Init /\ [][Next]_vars

\* this invariant will be violated if we are unable to apply all actions in the Trace
Incorrect == i <= Len(Trace)

========================
