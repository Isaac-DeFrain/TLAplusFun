---- MODULE Switch ----

EXTENDS TLC

VARIABLES switch

vars == <<switch>>

Init == switch = TRUE

Next == switch' = ~switch

Spec == Init /\ [][Next]_vars

=======================
