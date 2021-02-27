---------------------------- MODULE BadSubmodule -------------------------------

VARIABLE submodule_a, submodule_b

Variables == <<submodule_a, submodule_b>>

Init(given_a, given_b) ==
    /\ submodule_a = given_a
    /\ submodule_b = given_b

ChangeA ==
    /\ submodule_a' = ~submodule_a
    /\ UNCHANGED submodule_b

ChangeB ==
    /\ submodule_b' = ~submodule_b
    /\ UNCHANGED submodule_a

TypeOK ==
    /\ submodule_a \in BOOLEAN
    /\ submodule_b \in BOOLEAN

================================================================================
