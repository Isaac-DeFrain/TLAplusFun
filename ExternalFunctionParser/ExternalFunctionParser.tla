---- MODULE ExternalFunctionParser ----

EXTENDS Integers, Sequences, TLC

\* parses the log to seq of input-output pairs
ExFunParser(path) == CHOOSE s \in Seq(Int \X Int): TRUE

\* tranforms the seq of pairs to a function
RECURSIVE SeqToFn(_, _)
SeqToFn(s, acc) ==
    IF s = <<>> THEN acc
    ELSE
        LET xy == Head(s)
            x  == xy[1]
            y  == xy[2]
            f  == x :> y
        IN
        SeqToFn(Tail(s), acc @@ f)

parseFn(path) == SeqToFn(ExFunParser(path), <<>>)

=======================================
