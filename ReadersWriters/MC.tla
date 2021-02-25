---- MODULE MC ----

EXTENDS ReadersWriters2, TLC

n == 3

\* The following "invariants" are all violated:
\* - Cardinality(readers) < n
\* - Cardinality(WaitingToWrite) < n
\* - WaitingToRead /= {} => WaitingToWrite = {}
\* - WaitingToWrite /= {} => WaitingToRead = {}

===================