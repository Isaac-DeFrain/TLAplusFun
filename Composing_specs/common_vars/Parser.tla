---- MODULE Parser ----

EXTENDS Naturals, Sequences

Data ==
    {<<>>} \cup
    {<<n>> : n \in Nat} \cup
    BOOLEAN \X Nat

parser(path) == CHOOSE x \in Data : TRUE

=======================
