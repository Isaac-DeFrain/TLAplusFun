------------------------------ MODULE bitclock ------------------------------
VARIABLE clock            \* value of bitclock

Init == clock \in {0,1}   \* state predicate - to be check in initial only

TypeOK == clock \in {0,1} \* state predicate - to be checked in all states

Tick == IF clock = 0 THEN clock' = 1 ELSE clock' = 0 \* next-state relation
                                                     \* implicit enabling condition: clock = 0 \/ clock = 1

Spec == Init /\ [][Tick]_clock

\* It this clock useful? Does it necessarily have the desired behavior?
\* Is it an allowable behavior for clock to never change value?


\* Indentifying the problem: ClockEventuallyTicks is not satisfied
-----------------------------------------------------------------------------
\*VARIABLE init_clock              \* auxilliary variable

\*EInit == /\ clock \in {0,1}
\*         /\ init_clock = clock   \* init_clock initialized with same value as clock

\*ETick == /\ IF clock = 0 THEN clock' = 1 ELSE clock' = 0
\*         /\ UNCHANGED init_clock \* init_clock value does not change

\*ESpec == EInit /\ [][ETick]_<<init_clock,clock>> \* the initial state satisfies EInit predicate and
                                                 \* the only allowable transitions to the next state are either ETick or a stuttering step
                                                 \* i.e. a step in which both init_clock and clock are not changed

\*ClockEventuallyTicks == <>(clock # init_clock)





















\* Solution: require weak fairness of Tick, i.e. if enabling condition of Tick is repeatedly satisfied,
                                              \* a Tick step must be taken, i.e. cannot be all stuttering steps
-----------------------------------------------------------------------------
SpecCorrect == Init /\ [][Tick]_clock /\ WF_clock(Tick)

=============================================================================
\* Modification History
\* Last modified Sat Nov 23 21:39:23 EST 2019 by isaac
\* Created Sat Nov 23 21:00:38 EST 2019 by isaac
