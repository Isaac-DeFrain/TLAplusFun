------------------------------ MODULE bitclock ------------------------------
VARIABLE clock            \* value of bitclock

Init == clock \in {0,1}   \* state predicate - to be check in initial only

TypeOK == clock \in {0,1} \* state predicate - to be checked in all states

Tick == IF clock = 0 THEN clock' = 1 ELSE clock' = 0 \* next-state relation

Spec == Init /\ [][Tick]_clock

\* It this clock useful? Does it ever have to tick? Is it an allowable 
\* behavior to never change value?



































-----------------------------------------------------------------------------
VARIABLE init_clock            \* auxilliary variable

EInit == /\ clock \in {0,1}
         /\ init_clock = clock \* init_clock initialized to same value as clock

ETick == /\ IF clock = 0 THEN clock' = 1 ELSE clock' = 0
         /\ UNCHANGED init_clock

ESpec == EInit /\ [][ETick]_<<clock,init_clock>>

ClockEventuallyTicks == <>(clock # init_clock)

=============================================================================
\* Modification History
\* Last modified Sat Nov 23 21:25:06 EST 2019 by isaac
\* Created Sat Nov 23 21:00:38 EST 2019 by isaac
