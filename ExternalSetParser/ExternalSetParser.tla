---- MODULE ExternalSetParser ----

EXTENDS Integers, TLC

\* parses the log to a TLA+ sequence of TLA+ records
ExSetParser(path) == CHOOSE r \in SUBSET (Int \cup BOOLEAN \cup STRING) : TRUE

==================================
