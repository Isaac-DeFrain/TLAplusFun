---- MODULE Transfer3 ----

\* non-atomic transfers
\* fixed initial balances
\* valid transfers only
\* termination property

EXTENDS Naturals, TLC

(* transfer algorithm
variables alice_account = 10, bob_account = 10, money \in 1..20;

begin
Transfer:
  if alice_account >= money then
    A: alice_account := alice_account - money;
    B: bob_account := bob_account + money;
end if;
C: assert alice_account >= 0;
end algorithm *)

\* BEGIN TRANSLATION
VARIABLES alice_account, bob_account, money, pc

vars == <<alice_account, bob_account, money, pc>>

Init ==
    /\ alice_account = 10
    /\ bob_account = 10
    /\ money \in 1..20
    /\ pc = "Transfer"

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

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

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

Termination == <>(pc = "Done")

\* END TRANSLATION

==========================
