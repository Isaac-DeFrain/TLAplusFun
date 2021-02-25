---------------------------------- MODULE Bad ----------------------------------

EXTENDS TLC

VARIABLE a, b

Variables == <<a, b>>

ModuleInstance == INSTANCE BadSubmodule WITH submodule_a <- a, submodule_b <- b

Init == ModuleInstance!Init(TRUE, FALSE)

Next == ModuleInstance!ChangeA \/ ModuleInstance!ChangeB

Spec == Init /\ [][Next]_Variables

TypeOK == ModuleInstance!TypeOK

\* Oddly enough, both of these properties hold,
\* but Variables and ModuleInstance!Variables are NOT interchangeable
Prop1 == <>[][UNCHANGED Variables => UNCHANGED ModuleInstance!Variables]_Variables
Prop2 == <>[][UNCHANGED ModuleInstance!Variables => UNCHANGED Variables]_Variables

================================================================================
