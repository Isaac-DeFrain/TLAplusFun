---- MODULE Transfer4 ----

\* non-atomic transfers
\* parametric initial balances
\* valid transfers only
\* termination property

EXTENDS Naturals, TLC

CONSTANTS ALICE_BALANCE, BOB_BALANCE

VARIABLES alice_account, bob_account, money, pc

vars == <<alice_account, bob_account, money, pc>>

ASSUME ALICE_BALANCE > 0
ASSUME BOB_BALANCE > 0

total == ALICE_BALANCE + BOB_BALANCE

(***********)
(* Actions *)
(***********)

Transfer ==
    /\ pc = "Transfer"
    /\ IF alice_account >= money
       THEN pc' = "A"
       ELSE pc' = "C"
    /\ UNCHANGED <<alice_account, bob_account, money>>

A ==
    /\ pc = "A"
    /\ alice_account' = alice_account - money
    /\ pc' = "B"
    /\ UNCHANGED <<bob_account, money>>

B ==
    /\ pc = "B"
    /\ bob_account' = bob_account + money
    /\ pc' = "C"
    /\ UNCHANGED <<alice_account, money>>

C ==
    /\ pc = "C"
    /\ Assert(alice_account >= 0, "Failure of assertion")
    /\ pc' = "Done"
    /\ UNCHANGED <<alice_account, bob_account, money>>

Terminating == pc = "Done" /\ UNCHANGED vars

(*****************)
(* Specification *)
(*****************)

Init ==
    /\ alice_account = ALICE_BALANCE
    /\ bob_account = BOB_BALANCE
    /\ money \in 1..20
    /\ pc = "Transfer"

Next ==
    \/ Transfer
    \/ A
    \/ B
    \/ C
    \/ Terminating

Fairness ==
    /\ WF_vars(Transfer)
    /\ WF_vars(A)
    /\ WF_vars(B)
    /\ WF_vars(C)

Spec == Init /\ [][Next]_vars /\ Fairness

(************)
(* Property *)
(************)

Termination == <>(pc = "Done")

==========================
