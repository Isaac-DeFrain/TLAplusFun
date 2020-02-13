-------------------------------- MODULE AB2H --------------------------------
(***************************************************************************)
(* This is spec AB2 with history variables AtoB and BtoA added so the spec *)
(* implements spec AB under the identity refinement mapping.               *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Data, Bad
ASSUME Bad \notin (Data \X {0,1}) \cup {0,1}
  \* We need to asssume that Bad is different from any of the legal
  \* messsages. 


VARIABLES AVar, BVar,   \* The same as in module ABSpec
          AtoB2, \* The sequence of data messages in transit from sender to receiver
          BtoA2  \* The sequence of ack messages in transit from receiver to sender
                 \* Messages are sent by appending them to the end of the sequence
                 \* and received by removing them from the head of the sequence.

AB2 == INSTANCE AB2

(***************************************************************************)
(* We define RemoveBad so that RemoveBad(seq) removes from the sequence    *)
(* seq all elements that equal Bad.                                        *)
(***************************************************************************)
RECURSIVE RemoveBad(_)
  RemoveBad(seq) == 
  IF seq = << >> THEN << >>
                 ELSE (IF Head(seq) = Bad THEN << >> ELSE <<Head(seq)>>) 
                      \o RemoveBad(Tail(seq)) 
                      
RECURSIVE RemoveBad2(_)
RemoveBad2(seq) == 
  IF seq = << >> THEN << >>
                 ELSE IF Head(seq) = Bad 
                        THEN RemoveBad(Tail(seq))
                        ELSE <<Head(seq)>> \o RemoveBad(Tail(seq))

VARIABLES AtoB, BtoA \* Note that TLA+ allows multiple VARIABLE statements.


SpecH == /\ AB2!Spec
         /\ [] /\ AtoB  \in Seq(Data \X {0,1})
               /\ BtoA \in Seq({0,1})

AB == INSTANCE AB

(***************************************************************************)
(* The following theorem asserts that SpecH implements/refines the AB      *)
(* protocol.  However, it can't be checked by TLC because it doesn't have  *)
(* the form TLC requires of a specification.                               *)
(***************************************************************************)
THEOREM SpecH => AB!Spec
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define SpecHH to be a specification that is equivalent to SpecH  *)
(* and that TLC can check.  We write the definition of SpecHH in a way     *)
(* that should makes it clear that SpecHH is equivalent to SpecH.          *)
(***************************************************************************)
TypeOKH == /\ AB2!TypeOK
           /\ AtoB \in Seq(Data \X {0,1})
           /\ BtoA \in Seq({0,1})

InitH == /\ AB2!Init
         /\ AtoB = RemoveBad(AtoB2)
         /\ BtoA = RemoveBad(BtoA2)

NextH == /\ AB2!Next
         /\ AtoB' = RemoveBad(AtoB2')
         /\ BtoA' = RemoveBad(BtoA2')

(***************************************************************************)
(* We would normally define varsH to be the tuple of all the variables of  *)
(* the current module.  However, we can use the following shorter          *)
(* definition instead because                                              *)
(*                                                                         *)
(*    UNCHANGED << <<AVar, ... , BtoA2>>, AtoB, BtoA >>                    *)
(*                                                                         *)
(* equals                                                                  *)
(*                                                                         *)
(*    UNCHANGED << AVar, ... , BtoA2, AtoB, BtoA >>                        *)
(***************************************************************************)
varsH == << AB2!vars, AtoB, BtoA >>
         
SpecHH == InitH /\ [][NextH]_varsH
 
(***************************************************************************)
(* The following theorem asserts that SpecHH and SpecH are equivalent      *)
(* specifications.  It is equivalent to                                    *)
(*                                                                         *)
(*    /\ SpecHH => SpecH                                                   *)
(*    /\ SpecH  => SpecHH                                                  *)
(*                                                                         *)
(* TLC can check the first of these implications by showing that SpecH is  *)
(* a property satisfied by the specification SpecHH, but not the second.   *)
(***************************************************************************)
THEOREM SpecHH <=> SpecH

(***************************************************************************)
(* We can deduce that SpecH implies AB!Spec from SpecHH <=> SpecH and the  *)
(* following theorem, which TLC can check.                                 *)
(***************************************************************************)
THEOREM SpecHH => AB!Spec

=============================================================================
\* Modification History
\* Last modified Fri Nov 15 11:25:49 EST 2019 by isaac
\* Created Fri Nov 15 11:25:45 EST 2019 by isaac
