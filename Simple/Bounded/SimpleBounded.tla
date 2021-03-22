---- MODULE SimpleBounded ----

EXTENDS Naturals

CONSTANT BOUND

VARIABLE x

ASSUME BOUND \in Nat

Incr ==
    /\ x < BOUND
    /\ x' = x + 1

Init == x = 0

Next == Incr

\* Original specification
Spec == Init /\ [][Next]_x

\* Fair specification
Fairness == []<><<x' /= x \/ x = BOUND>>_x

FairSpec == Spec /\ Fairness

\* Type invariant
TypeOK == x \in 0..BOUND

\* Liveness properties
Liveness0 == <>(x > 0)

LivenessN == \A n \in 0..(BOUND - 1) : <>[](x > n)

==============================
