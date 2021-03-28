# Transfer

This is a series of several TLA+ specs which specify a transfer between two accounts (`alice_account` and `bob_account`) at varying degrees of correctness, exhaustiveness, and specificity.

## Transfer1

Defines a spec for a non-atomic transfer from a PlusCal algorithm which features fixed initial balances and no explicit fairness condition.

## Transfer2

Defines a spec for a non-atomic transfer from a PlusCal algorithm which features fixed initial balances, no explicit fairness condition, and an assertion to catch overdraft bugs.

## Transfer3

Defines a spec for a non-atomic transfer from a PlusCal algorithm which features fixed initial balances, no explicit fairness condition, and a check to ensure the absence of overdraft bugs.

## Transfer4

Defines a spec for a non-atomic transfer which features parametric initial balances, explicit fairness conditions, and a check to ensure the absence of overdraft bugs.

## Transfer5

Defines a spec for a non-atomic transfer which features exhaustive initial balance executions, explicit fairness conditions, and balance and conservation invariants.

## Transfer6

Defines a spec for an atomic transfer which features exhaustive initial balance executions, explicit fairness conditions, and balance and conservation invariants.
