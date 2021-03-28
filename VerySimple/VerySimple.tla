---- MODULE VerySimple ----

VARIABLE status

(***********)
(* Actions *)
(***********)

Initial == status = "Initial"

InitialToRunning ==
    /\ status = "Initial"
    /\ status' = "Running"

RunningToStopped ==
    /\ status = "Running"
    /\ status' = "Stopped"

Done ==
    /\ status = "Stopped"
    /\ UNCHANGED status

Next ==
    \/ InitialToRunning
    \/ RunningToStopped
    \/ Done

(*****************)
(* Specification *)
(*****************)

Fairness == WF_status(InitialToRunning) /\ WF_status(RunningToStopped)

Spec == Initial /\ [][Next]_status /\ Fairness

(***************************)
(* Invariants & Properties *)
(***************************)

PossibleStatuses == { "Initial", "Running", "Stopped" }

TypeOK == status \in PossibleStatuses

Termination == <>(status = "Stopped")

===========================
