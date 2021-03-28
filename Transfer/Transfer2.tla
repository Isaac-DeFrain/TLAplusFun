---- MODULE Transfer2 ----

\* non-atomic transfers
\* fixed initial balances
\* non-negative balance assertion
\* termination property

EXTENDS Naturals, TLC

(* new transfer algorithm
variables alice_account = 10, bob_account = 10, money \in 1..20;

begin
A: alice_account := alice_account - money;
B: bob_account := bob_account + money;
C: assert alice_account >= 0;
end algorithm *)

\* BEGIN TRANSLATION
VARIABLES alice_account, bob_account, money, pc

vars == <<alice_account, bob_account, money, pc>>

Init ==
    /\ alice_account = 10
    /\ bob_account = 10
    /\ money \in 1..20
    /\ pc = "A"

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
    /\ Assert(alice_account >= 0, "Failure of assertion: alice_account >= 0")
    /\ pc' = "Done"
    /\ UNCHANGED <<alice_account, bob_account, money>>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next ==
    \/ A
    \/ B
    \/ C
    \/ Terminating

Fairness ==
    /\ WF_vars(A)
    /\ WF_vars(B)
    /\ WF_vars(C)

Spec == Init /\ [][Next]_vars /\ Fairness

Termination == <>(pc = "Done")

\* END TRANSLATION

==========================
