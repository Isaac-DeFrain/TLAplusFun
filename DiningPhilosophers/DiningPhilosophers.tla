---- MODULE DiningPhilosophers ----

EXTENDS Naturals, TLC

CONSTANT N  \* number of philosophers and chopsticks

VARIABLES
    state,  \* each philosopher is either hungry (true) or thinking (false)
    left,   \* each philosopher either has a left chopstick or not
    right   \* each philosopher either has a right chopstick or not

vars == <<state, left, right>>

-----------------------------------

\* A subtle point:
\* each chopstick can be held by either of two adjacent philosophers at any given time

-----------------------------------

Philosopher == 0..(N-1)

TypeOK ==
    /\  left  \in [ Philosopher -> BOOLEAN ]
    /\  right \in [ Philosopher -> BOOLEAN ]
    /\  state \in [ Philosopher -> BOOLEAN ]

-----------------------------------

GetHungry(n) ==
    /\  ~state[n]   \* currently thinking
    /\  state' = [ state EXCEPT ![n] = TRUE ]
    /\  UNCHANGED <<left, right>>

GrabLeft(n) ==
    /\  state[n]            \* currently hungry
    /\  ~left[n]            \* currently not holding the left chopstick
    /\  ~right[(n + 1) % N] \* philosopher to n's left does not have their right, n's left, chopstick
    /\  left' = [ left EXCEPT ![n] = TRUE ]
    /\  UNCHANGED <<right, state>>

GrabRight(n) ==
    /\  state[n]            \* currently hungry
    /\  ~right[n]           \* currently not holding the right chopstick
    /\  ~left[(n - 1) % N]  \* philosopher to n's right does not have their left chopstick
    /\  right' = [ right EXCEPT ![n] = TRUE ]
    /\  UNCHANGED <<left, state>>

Eat(n) ==
    \*  hungry and holding both chopsticks => time to eat
    /\  state[n]
    /\  left[n]
    /\  right[n]
    /\  left'  = [ left  EXCEPT ![n] = FALSE ]
    /\  right' = [ right EXCEPT ![n] = FALSE ]
    /\  state' = [ state EXCEPT ![n] = FALSE ]

-----------------------------------

\* specification

Init ==
    /\  left  = [ p \in Philosopher |-> FALSE ]
    /\  right = [ p \in Philosopher |-> FALSE ]
    /\  state = [ p \in Philosopher |-> FALSE ]

Next == \E p \in Philosopher :
    \/  GetHungry(p)
    \/  GrabLeft(p)
    \/  GrabRight(p)
    \/  Eat(p)

Spec == Init /\ [][Next]_vars

-----------------------------------

\* this condition is violated in the execution where either
\* all philosophers get hungry and grab their left chopsticks, or
\* all philosophers get hungry and grab their right chopsticks
NoDeadlock == ENABLED Next

\* hence this invariant holds
Inv ==
    ~ENABLED Next <=>
        \/  \A p \in Philosopher : state[p] /\ left[p]
        \/  \A p \in Philosopher : state[p] /\ right[p]

===================================
