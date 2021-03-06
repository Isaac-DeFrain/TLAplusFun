---- MODULE Transfer6 ----

\* atomic transfers
\* check all initial balances
\* valid transfers only
\* termination property
\* conservation invariant

EXTENDS Naturals, TLC

VARIABLES alice_account, bob_account, money, pc, total

vars == <<alice_account, bob_account, money, pc, total>>

(***********)
(* Actions *)
(***********)

Transfer ==
    /\ pc = "Transfer"
    /\ IF alice_account >= money
       THEN pc' = "A"
       ELSE pc' = "C"
    /\ UNCHANGED <<alice_account, bob_account, money, total>>

AtoB ==
    /\ pc = "A"
    /\ alice_account' = alice_account - money
    /\ bob_account' = bob_account + money
    /\ pc' = "C"
    /\ UNCHANGED <<money, total>>

C ==
    /\ pc = "C"
    /\ Assert(alice_account >= 0, "Failure of assertion")
    /\ pc' = "Done"
    /\ UNCHANGED <<alice_account, bob_account, money, total>>

Terminating == pc = "Done" /\ UNCHANGED vars

(*****************)
(* Specification *)
(*****************)

Init ==
    /\ alice_account \in 0..20
    /\ bob_account \in 0..20
    /\ money \in 1..20
    /\ pc = "Transfer"
    /\ total = alice_account + bob_account

Next ==
    \/ Transfer
    \/ AtoB
    \/ C
    \/ Terminating

Fairness ==
    /\ WF_vars(Transfer)
    /\ WF_vars(AtoB)
    /\ WF_vars(C)

Spec == Init /\ [][Next]_vars /\ Fairness

Termination == <>(pc = "Done")

(**************)
(* Properties *)
(**************)

MoneyNotNegative ==
    /\ money >= 0
    /\ alice_account >= 0
    /\ bob_account >= 0

ConservationOfMoney == alice_account + bob_account = total

==========================
