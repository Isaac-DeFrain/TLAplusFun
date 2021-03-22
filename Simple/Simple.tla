---- MODULE Simple ----

EXTENDS Naturals

VARIABLE x

Incr == x' = x + 1

Init == x = 0

Next == Incr

\* Original specification
Spec == Init /\ [][Next]_x

\* Fair specification
Fairness == []<><<x' /= x>>_x

FairSpec == Spec /\ Fairness

\* Type invariant
TypeOK == x \in Nat

\* Liveness properties
Liveness0 == <>(x > 0)

LivenessN == \A n \in 0..10 : <>(x > n)

=======================
