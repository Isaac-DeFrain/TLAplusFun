---- MODULE Transfer1 ----

\* non-atomic transfers
\* fixed initial balances
\* termination property

EXTENDS Naturals

(* transfer algorithm
variables alice_account = 10, bob_account = 10, money = 5;

begin
A: alice_account := alice_account - money;
B: bob_account := bob_account + money;

end algorithm *)

\* BEGIN TRANSLATION
VARIABLES alice_account, bob_account, money, pc

vars == <<alice_account, bob_account, money, pc>>

Init ==
    /\ alice_account = 10
    /\ bob_account = 10
    /\ money = 5
    /\ pc = "A"

A ==
    /\ pc = "A"
    /\ alice_account' = alice_account - money
    /\ pc' = "B"
    /\ UNCHANGED <<bob_account, money>>

B ==
    /\ pc = "B"
    /\ bob_account' = bob_account + money
    /\ pc' = "Done"
    /\ UNCHANGED <<alice_account, money>>

(* Allow infinite stuttering once done to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next ==
    \/ A
    \/ B
    \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

\* Q: Is Termination satisfied?























\* We need fairness to ensure that both A and B steps are taken!
Fairness == WF_vars(A) /\ WF_vars(B)

FairSpec == Spec /\ Fairness

==========================
