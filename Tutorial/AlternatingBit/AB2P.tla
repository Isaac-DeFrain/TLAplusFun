-------------------------------- MODULE AB2P --------------------------------
(***************************************************************************)
(* This is a version of specification AB2 modified so it implements the    *)
(* fairness requirement of the high-level AB specification in module       *)
(* ABSpec, which asserts that new values keep being sent and received.     *)
(* For AB2 to satisfy that fairness requirement, when a process keeps      *)
(* sending messages to the other process, at least one of those messages   *)
(* must not be corrupted.                                                  *)
(*                                                                         *)
(* It seems to be impossible to express this requirement by adding         *)
(* fairness conditions on subactions of the next-state action of AB2.  To  *)
(* allow the requirement to be expressed with fairness conditions, the     *)
(* current spec adds two variables AtoBgood and BtoAgood.  The value of    *)
(* AtoBgood controls which messages in AtoBgood may be corrupted, and the  *)
(* value of BtoAgood does the same for messages in BtoAgood.               *)
(*                                                                         *)
(* The value of AtoBgood is a sequence of Boolean values having the same   *)
(* length as AtoB2.  A value is appended to the end of AtoBgood whenever a *)
(* message is appended to the end of AtoB2; and a message is removed from  *)
(* the head of AtoBgood whenever a message or Bad is removed from the head *)
(* of AtoBgood.  If AtoBgood[i] equals TRUE, then message number i of      *)
(* AtoB2 cannot be corrupted.  So if TRUE is appended to AtoBgood when a   *)
(* message is appended to AtoB2, then that message cannot be corrupted.    *)
(* Similarly, BtoAgood controls whether messages in BtoA2 can be           *)
(* corrupted.                                                              *)
(***************************************************************************)

(***************************************************************************)
(* The following EXTENDS statement imports all the constant and variable   *)
(* declarations and all the definitions from module AB2 (with no           *)
(* renaming).                                                              *)
(***************************************************************************)

EXTENDS AB2

VARIABLES AtoBgood, BtoAgood

varsP == <<vars, AtoBgood, BtoAgood>>

(***************************************************************************)
(* The definitions of the type-correctness invariant, initial predicate,   *)
(* and actions of the sender and receiver in the current spec are obtained *)
(* in a straightforward way by conjoining conditions on the variables      *)
(* AtoBgood and BtoAgood to the corresponding definitions from module AB2  *)
(* (which are imported to the current module by the EXTENDS statement).    *)
(***************************************************************************)
TypeOKP == /\ TypeOK
           /\ AtoBgood \in Seq(BOOLEAN)
           /\ BtoAgood \in Seq(BOOLEAN)

InitP == /\ Init
         /\ AtoBgood = << >>
         /\ BtoAgood = << >>
                      
ASndP == /\ ASnd
         /\ \E b \in BOOLEAN : AtoBgood' = Append(AtoBgood, b)
         /\ UNCHANGED BtoAgood

ARcvP == /\ ARcv
         /\ BtoAgood' = Tail(BtoAgood)
         /\ UNCHANGED AtoBgood
  
BSndP == /\ BSnd
         /\ \E b \in BOOLEAN : BtoAgood' = Append(BtoAgood, b)
         /\ UNCHANGED AtoBgood

BRcvP == /\ BRcv
         /\ AtoBgood' = Tail(AtoBgood)
         /\ UNCHANGED BtoAgood

(***************************************************************************)
(* The CorruptMsg action of module AB is modified by adding an enabling    *)
(* condition that allows a message in AtoB2 or BtoA2 to be corrupted only  *)
(* if the corresponding element of AtoBgood or BtoAgood equals FALSE; and  *)
(* by requiring AtoBgood and BtoAgood to be unchanged.                     *)
(***************************************************************************)         
CorruptMsgP == /\ \/ /\ \E i \in 1..Len(AtoB2):
                          /\ ~ AtoBgood[i]
                          /\ AtoB2' = [AtoB2 EXCEPT ![i] = Bad]
                     /\ BtoA2' = BtoA2
                  \/ /\ \E i \in 1..Len(BtoA2):
                          /\ ~ BtoAgood[i]
                          /\ BtoA2' = [BtoA2 EXCEPT ![i] = Bad]
                     /\ AtoB2' = AtoB2
               /\ UNCHANGED << AVar, BVar, AtoBgood, BtoAgood >>
               
(***************************************************************************)
(* The next-state action and safety spec are named NextP and SpecP.        *)
(***************************************************************************)
NextP == ASndP \/ ARcvP \/ BSndP \/ BRcvP \/ CorruptMsgP

SpecP == InitP /\ [][NextP]_varsP
-----------------------------------------------------------------------------
(***************************************************************************)
(* It's clear that every assignment of values to the variables of module   *)
(* AB2 that satisfies InitP also satisfies the initial predicate Init of   *)
(* AB2, and every change to the variables of AB2 allowed by NextP is also  *)
(* allowed by the next-state relation Next of AB2.  Hence SpecP implements *)
(* the specification Spec of AB2.                                          *)
(***************************************************************************)
THEOREM SpecP => Spec

(***************************************************************************)
(* Since Spec implements the specification ABS!Spec of module ABSpec, we   *)
(* deduce the following theorem from SpecP => Spec.  (The definition of    *)
(* ABS!Spec is imported into the current module by the EXTENDS statement,  *)
(* along with all the other definitions from module AB2.)                  *)
(***************************************************************************)
THEOREM SpecP => ABS!Spec
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now obtain the spec FairSpecP by conjoining fairness conditions to   *)
(* SpecP.  Because messages are not deleted, weak fairness conditions on   *)
(* the receive actions ensure that every sent message or its corrupted Bad *)
(* replacement is eventually received.  To ensure that an uncorrupted      *)
(* version of every message eventually is received, we add fairness        *)
(* conditions not for the sending actions ASndP and BSndP, but for those   *)
(* sending actions that append TRUE to AtoBgood or BtoAgood.               *)
(*                                                                         *)
(* Note that a subaction of the next-state action NextP is any formula     *)
(* that implies NextP.  It doesn't have to be a disjunct in the definition *)
(* of NextP.  Thus the two actions                                         *)
(*                                                                         *)
(*    ASndP /\ AtoBgood'[Len(AtoBgood')]                                   *)
(*                                                                         *)
(*    BSndP /\ BtoAgood'[Len(BtoAgood')]                                   *)
(*                                                                         *)
(* are subactions of NextP, just like the actions ARcvP and BRcvP.         *)
(***************************************************************************)
FairSpecP == /\ SpecP 
             /\ WF_vars(ARcvP) 
             /\ WF_vars(BRcvP) 
             /\ WF_vars(ASndP /\ AtoBgood'[Len(AtoBgood')]) 
             /\ WF_vars(BSndP /\ BtoAgood'[Len(BtoAgood')])
             
(***************************************************************************)
(* The following theorem asserts that FairSpecP implements specification   *)
(* FairSpec of module ABSpec under the expected refinement mapping.  TLC   *)
(* can check this theorem.                                                 *)
(***************************************************************************)             
THEOREM FairSpecP => ABS!FairSpec

=============================================================================
\* Modification History
\* Last modified Fri Nov 15 11:17:13 EST 2019 by isaac
\* Created Fri Nov 15 11:13:54 EST 2019 by isaac
