---- MODULE Counter ----

EXTENDS Naturals

VARIABLES count

vars == <<count>>

Init == count = 0

Next == count' = count + 1

Spec == Init /\ [][Next]_vars

========================
