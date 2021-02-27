---------------------------- MODULE Properties -------------------------------

EXTENDS Naturals

VARIABLES x

Init == x = 0

Next ==
    IF x = 0
    THEN x' = 1
    ELSE UNCHANGED x

Fairness == WF_x(x = 0 /\ x' = 1)

Spec == Init /\ [][Next]_x /\ Fairness

TypeOK == x \in 0..1

\* x = 0 in the intial state => [](x = 1) = FALSE
Prop1 == ~[](x = 1)

\* without a fairness condition, <>[](x = 1) = FALSE
Prop2 == <>[](x = 1)

\* since properties need to be stuttering-invariant:
\*   []StepThatMayBeStuttering must be written as [][StepThatMaybeBeStuttering]_<<>>
Prop3 == [][IF x' /= x THEN x' = 1 ELSE x = 0]_<<>>

============================================================================
