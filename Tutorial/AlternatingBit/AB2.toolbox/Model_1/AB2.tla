-------------------------------- MODULE AB2 --------------------------------
(***************************************************************************)
(* This is a modification of spec AB in which instead of losing messages,  *)
(* messages are detectably "corrupted"--represented by being changed to    *)
(* the value Bad.  The to communication channels are represented by the    *)
(* variables AtoB2 and BtoA2.                                              *)
(***************************************************************************)
EXTENDS Integers, Sequences\* , TLC

CONSTANT Data, Bad
ASSUME Bad \notin (Data \X {0,1}) \cup {0,1}
  \* We need to asssume that Bad is different from any of the legal
  \* messsages. 
VARIABLES AVar, BVar,   \* The same as in module ABSpec
          AtoB2, \* The sequence of data messages in transit from sender to receiver
          BtoA2  \* The sequence of ack messages in transit from receiver to sender
                 \* Messages are sent by appending them to the end of the sequence
                 \* and received by removing them from the head of the sequence.

vars == << AVar, BVar, AtoB2, BtoA2 >>

TypeOK == /\ AVar  \in Data \X {0,1}
          /\ BVar  \in Data \X {0,1}
          /\ AtoB2 \in Seq((Data \X {0,1}) \cup {Bad})
          /\ BtoA2 \in Seq({0,1, Bad})

Init == /\ AVar  \in Data \X {1} 
        /\ BVar  = AVar
        /\ AtoB2 = << >>
        /\ BtoA2 = << >>

(***************************************************************************)
(* The action of the sender sending a data message by appending AVar to    *)
(* the end of the message queue AtoB2.  It will keep sending the same      *)
(* message until it receives an acknowledgment for it from the receiver.   *)
(***************************************************************************)
ASnd == /\ AtoB2' = Append(AtoB2, AVar)
        /\ UNCHANGED <<AVar, BtoA2, BVar>>

(***************************************************************************)
(* The action of the sender receiving an ack message.  If that ack is for  *)
(* the value it is sending, then it chooses another message to send and    *)
(* sets AVar to that message.  If the ack is for the previous value it     *)
(* sent, it ignores the message.  In either case, it removes the message   *)
(* from BtoA2.  Note that Bad cannot equal AVar[2], which is in {0,1}.     *)
(***************************************************************************)
ARcv == /\ BtoA2 # << >>
        /\ IF Head(BtoA2) = AVar[2]  
             THEN \E d \in Data: AVar' = <<d, 1 - AVar[2]>>
             ELSE AVar' = AVar
        /\ BtoA2' = Tail(BtoA2)
        /\ UNCHANGED <<AtoB2, BVar>>

(***************************************************************************)
(* The action of the receiver sending an acknowledgment message for the    *)
(* last data item it received.                                             *)
(***************************************************************************)
BSnd == /\ BtoA2' = Append(BtoA2, BVar[2])
        /\ UNCHANGED <<AVar, BVar, AtoB2>>

(***************************************************************************)
(* The action of the receiver receiving a data message.  It ignores a Bad  *)
(* message.  Otherwise, it sets BVar to the message if it's not for the    *)
(* data item it has already received.                                      *)
(***************************************************************************)        
BRcv == /\ AtoB2 # << >>
        /\ IF (Head(AtoB2) # Bad) /\ (Head(AtoB2)[2] # BVar[2])  
             THEN BVar' = Head(AtoB2)
             ELSE BVar' = BVar
        /\ AtoB2' = Tail(AtoB2)
        /\ UNCHANGED <<AVar, BtoA2>>

(***************************************************************************)
(* CorruptMsg is the action that changes an arbitrary message in AtoB2 or  *)
(* BtoA2 to Bad.  (We don't bother testing if the message in AtoB2 already *)
(* equals Bad, since setting to Bad a message that already equals Bad is   *)
(* just a stuttering step.)                                                *)
(***************************************************************************)
CorruptMsg == /\ \/ /\ \E i \in 1..Len(AtoB2):
                         AtoB2' = [AtoB2 EXCEPT ![i] = Bad]
                    /\ BtoA2' = BtoA2
                 \/ /\ \E i \in 1..Len(BtoA2):
                         BtoA2' = [BtoA2 EXCEPT ![i] = Bad]
                    /\ AtoB2' = AtoB2
              /\ UNCHANGED << AVar, BVar >>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ CorruptMsg

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
ABS == INSTANCE ABSpec 

THEOREM Spec => ABS!Spec
-----------------------------------------------------------------------------
(***************************************************************************)
(* FairSpec is the analogue of formula FairSpec of module AB2.  That is,   *)
(* it is obtained by conjoining to formula Spec the fairness conditions    *)
(* that correspond to the ones in module AB2.  However, specification      *)
(* FairSpec of this module does not implement ABS!FairSpec.  You can use   *)
(* TLC to find a behavior in which no new values are ever sent.            *)
(***************************************************************************)
FairSpec == 
  Spec /\ SF_vars(ARcv) /\ SF_vars(BRcv) /\ WF_vars(ASnd) /\ WF_vars(BSnd)
  
(***************************************************************************)
(* A little thought reveals that, since messages are corrupted but not     *)
(* deleted, strong fairness of ARcv and BRcv is equivalent to weak         *)
(* fairness of those actions.  The shortest counterexample showing that    *)
(* FairSpec does not implement ABS!FairSpec, which is probably the one     *)
(* found by TLC, is a behavior in which a message is sent on an empty      *)
(* message channel, but is always corrupted before it can received.  This  *)
(* suggests that in addition to weak fairness of ARcv and BRcv, we want    *)
(* strong fairness of those actions when the head of the queue is not      *)
(* corrupt.  That leads to the following spec.                             *)
(***************************************************************************)
FairSpec2 == 
  Spec /\ WF_vars(ARcv) /\ WF_vars(BRcv) /\ WF_vars(ASnd) /\ WF_vars(BSnd)
       /\ SF_vars(ARcv /\ Head(BtoA2) # Bad) 
       /\ SF_vars(BRcv /\ Head(AtoB2) # Bad)
       
(***************************************************************************)
(* Running TLC shows that FairSpec2 also does not implement ABS!FairSpec.  *)
(* In fact, I believe that it is impossible to obtain a specification that *)
(* implements ABS!FairSpec by conjoining to Spec fairness conditions on    *)
(* subactions of Next.  Module AB2P shows how we can modify the AB2        *)
(* specification to obtain a specification that implements ABS!Spec.       *)
(***************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We define RemoveBad so that RemoveBad(seq) is the value obtained by     *)
(* removing from the sequence seq all elements that equal Bad.             *)
(***************************************************************************)
RECURSIVE RemoveBad(_)
RemoveBad(seq) == 
  IF seq = << >>
    THEN << >>
    ELSE (IF Head(seq) = Bad THEN << >> ELSE <<Head(seq)>>) 
           \o RemoveBad(Tail(seq))

(***************************************************************************)
(* There's an easy way to define RemoveBad using the SelectSeq operator of *)
(* the Sequences module.  Here's the alternative definition.               *)
(***************************************************************************)
RemoveBadAlt(seq) == LET Test(elt) == elt # Bad
                     IN  SelectSeq(seq, Test)
                   
(***************************************************************************)
(* The following statement defines AB!Spec to be the specification Spec of *)
(* module AB with RemoveBad(AtoB2) substituted for AtoB and                *)
(* RemoveBad(BtoA2) substituted for BtoA.                                  *)
(***************************************************************************)                   
AB == INSTANCE AB WITH AtoB <- RemoveBad(AtoB2), BtoA <- RemoveBad(BtoA2)

(***************************************************************************)
(* The following theorem asserts that the specification Spec of this       *)
(* module implements the specification Spec of module AB under the         *)
(* refinement mapping that substitutes RemoveBad(AtoB2) for AtoB and       *)
(* substitutes for every other variable and every constant of module AB    *)
(* the variable or constant of the same name.  This theorem is checked by  *)
(* having TLC check that the temporal property AB!Spec is satisfied by the *)
(* specification Spec.                                                     *)
(***************************************************************************)
THEOREM Spec => AB!Spec

=============================================================================
\* Modification History
\* Last modified Fri Nov 15 09:54:15 EST 2019 by isaac
\* Created Fri Nov 15 09:53:49 EST 2019 by isaac
