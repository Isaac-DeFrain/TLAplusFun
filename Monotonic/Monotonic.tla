---------------------------- MODULE Monotonic -------------------------------

EXTENDS Naturals

VARIABLES x

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_x

TypeOK == x \in Nat

\* check that x is increasing on each non-stuttering step
Monotonic == [][x' > x]_x

=============================================================================
