--------------------------- MODULE SimpleProgram ---------------------------
EXTENDS Integers
VARIABLES i, pc

Init == (pc = "start") /\ (i = 0)

Pick == /\ pc = "start"
        /\ i' \in 0..1000
        /\ pc' = "middle"
        
Add1 == /\ pc = "middle"
        /\ i' = i + 1
        /\ pc' = "done"

Next == Pick \/ Add1

=============================================================================
\* Modification History
\* Last modified Thu Nov 14 13:41:06 EST 2019 by isaac
\* Created Thu Nov 14 13:37:32 EST 2019 by isaac
