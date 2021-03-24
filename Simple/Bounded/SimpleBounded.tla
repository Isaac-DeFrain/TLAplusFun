---- MODULE SimpleBounded ----

EXTENDS Naturals

CONSTANT BOUND

VARIABLE x

ASSUME BOUND >= 1

Incr == x' = x + 1

Init == x = 0

Next == x < BOUND /\ Incr

\* Original specification
Spec == Init /\ [][Next]_x

\* Fair specification
Fairness == WF_x(Incr)

FairSpec == Spec /\ Fairness

\* Type invariant
TypeOK == x \in 0..BOUND

\* Liveness properties
Liveness0 == <>(x > 0)

LivenessN == <>(x = BOUND)

\* Property satisfaction
Equivalence1 == []<><<x' /= x>>_x

Equivalence2 == []<><<Incr>>_x

LEMMA Liveness0 => LivenessN

THEOREM FairSpec <=> Spec /\ Equivalence1

THEOREM FairSpec <=> Spec /\ Equivalence2

THEOREM FairSpec => /\ LivenessN
                    /\ Equivalence1
                    /\ Equivalence2

==============================
