-------------------------- MODULE GenesisCeremony ---------------------------
EXTENDS FiniteSets, Integers, Sequences

CONSTANT
  Nodes,          \* set of participating nodes
  None

VARIABLES
  nodes,          \* set of Node ids -- does not change
  nStatus,        \* tuple of Node statuses
  nInMsg,         \* tuple of incoming message tuples
  nOutStreamMsg,  \* tuple of outgoing stream message tuples
  nOutMsg         \* tuple of outgoing messages

vars == << nodes, nStatus, nInMsg, nOutStreamMsg, nOutMsg >>

-----------------------------------------------------------------------------
(*************************************************************************)
(* Auxiliary functions from SequencesExt community module                *)
(* See https://github.com/tlaplus/                                       *)
(*************************************************************************)
ToSet(s) == { s[i] : i \in DOMAIN s }

IsInjective(s) == \A i, j \in DOMAIN s: (s[i] = s[j]) => (i = j)
  
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

-----------------------------------------------------------------------------
(* Message _msg bundled with sender _from and receiver _to *)
Pack(_msg, _from, _to) == [msg |-> _msg, from |-> _from, to |-> _to]

(* _from, _to \in nodes *)
StreamMsg(_msg, _from, _to) ==
  nOutStreamMsg' = [nOutStreamMsg EXCEPT ![_from]
                    = Append(nOutStreamMsg[_from], Pack(_msg, _from, _to))]

(* Given a set of recipients _tos, the sender creates a message pack for *)
(* each and adds them to thier list of outgoing messages.                *)
(* _tos \in SUBSET nodes *)
(* Used to start genesis ceremony. *)
BroadcastStream(_msg, _from, _tos) ==
  LET CreatePacket(_to) == Pack(_msg, _from, _to)
  IN  nOutStreamMsg' = [nOutStreamMsg EXCEPT ![_from] = nOutStreamMsg[_from]
                       \o SetToSeq({CreatePacket(to) : to \in_tos})]

(* Enabled when a node n has nonempty nOutStreamMsg whose head has correct msgType. *)
(* The head msg is deleted from sender's outgoing msgs and added to recipient's incoming msgs. *)
TransferStreamMsg(msgType) == \E n \in nodes :
  /\ nOutStreamMsg[n] # << >>
  /\ Head(nOutStreamMsg[n]).msg.type = msgType
  /\ nOutStreamMsg' = [nOutStreamMsg EXCEPT ![n] = Tail(nOutStreamMsg[n])]
  /\ nInMsg' = [nInMsg EXCEPT ![Head(nOutStreamMsg[n]).to]
                = Append(nInMsg[Head(nOutStreamMsg[n]).to], Head(nOutStreamMsg[n]))]
  /\ UNCHANGED << nodes, nStatus, nOutMsg >>

(* Next OutStream message is dropped. *)
LooseStreamMsg == \E n \in nodes :
  /\ nOutStreamMsg[n] # << >>
  /\ nOutStreamMsg' = [nOutStreamMsg EXCEPT ![n] = Tail(nOutStreamMsg[n])]
  /\ UNCHANGED << nodes, nStatus, nInMsg, nOutMsg >>

SendingStatus == {"init", "success", "failed"}

SentMsgStatus(_status, _packet) == [status |-> _status, packet |-> _packet]

(* Initializes an outgoing message. *)
SendMsg(_msg, _from, _to) ==
  nOutMsg' = [nOutMsg EXCEPT ![_from]
              = SentMsgStatus("init", Pack(_msg, _from, _to))]

(* When an outgoing message is initialized, it can be successfully transmitted. *)
TransferMsg == \E n \in nodes :
  /\ nOutMsg[n] # None
  /\ nOutMsg[n].status = "init"
  /\ nOutMsg' = [nOutMsg EXCEPT ![n].status = "success"]
  /\ nInMsg'  = [nInMsg EXCEPT ![nOutMsg[n].packet.to]
                 = Append(nInMsg[nOutMsg[n].packet.to], nOutMsg[n].packet)]
  /\ UNCHANGED << nodes, nStatus, nOutStreamMsg >>

(* When an outgoing message is initialized, transmission can be unsuccessful. *)
LooseMsg == \E n \in nodes :
  /\ nOutMsg[n] # None
  /\ nOutMsg[n].status = "init"
  /\ nOutMsg' = [nOutMsg EXCEPT ![n].status = "failed"]
  /\ UNCHANGED << nodes, nStatus, nInMsg, nOutStreamMsg >>
 
-----------------------------------------------------------------------------
(* Checks that given node's next In message has given type. *)
NextInMsgIs(n, msgType) ==
  /\ nInMsg[n] # << >> (* Len(nInMsg[n]) > 0 *)
  /\ Head(nInMsg[n]).msg.type = msgType

(* Deletes the next In message from given node. *)
PopNextInMsg(n) == nInMsg' = [nInMsg EXCEPT ![n] = Tail(nInMsg[n])]

(*  *)
Handling(n, status, msgType) ==
  /\ nStatus[n] = status
  /\ NextInMsgIs(n, msgType)
  /\ PopNextInMsg(n)

DoNotHandle(status, msgType) == \E n \in nodes :
  /\ Handling(n, status, msgType)
  /\ UNCHANGED << nodes, nStatus, nOutStreamMsg, nOutMsg >>

Sender(n) == Head(nInMsg[n]).from

-----------------------------------------------------------------------------
(* Messages definition -- type, status, packet *)

MessageType ==
  {"UnapprovedBlock", "BlockApproval", "ApprovedBlockRequest", "ApprovedBlock"}

(* Set of all message types *)
Messages == [type : MessageType]
(* Set of packets *)
Packets  == [msg : Messages, from : nodes, to : nodes]

NewMessage(_type) == [type |-> _type]
NewUnapprovedBlock == NewMessage("UnapprovedBlock")
NewBlockApproval == NewMessage("BlockApproval")
NewApprovedBlockRequest == NewMessage("ApprovedBlockRequest")
NewApprovedBlock == NewMessage("ApprovedBlock")

-----------------------------------------------------------------------------

PossibleStatuses ==
  {"new", "init", "running", "genesis_validator", "ceremony_master"}

HoldsMessageType(msgQueue) == ToSet(msgQueue) \subseteq Packets

(* Verifies correctness of node status, formation of In and OutStream messages, *)
(* and formation of Out messages for all nodes.                                 *)
TypeOK ==
  /\ \A n \in nodes : nStatus[n] \in PossibleStatuses
  /\ \A n \in nodes : HoldsMessageType(nInMsg[n]) 
  /\ \A n \in nodes : HoldsMessageType(nOutStreamMsg[n])
  /\ \A n \in nodes : nOutMsg[n] \in ([status : SendingStatus, packet : Packets] \cup {None})

-----------------------------------------------------------------------------
(* Returns bootstrap node for given node *)
Bootstrap(n) == LET node == (CHOOSE cn \in Nodes : cn.id = n)
                IN  node.bootstrap

(* Transistions the given node to the given status. *)
TransitionTo(n, status) == nStatus' = [nStatus EXCEPT ![n] = status]

(* If node has no Out messages and "new" status, it can change status to "init" *)
(* while sending a NewApprovedBlockRequest to its bootstrap. *)
LaunchFromNewToInit == \E n \in nodes :
  /\ nStatus[n] = "new"
  /\ nOutMsg[n] = None
  /\ TransitionTo(n, "init")  
  /\ SendMsg(NewApprovedBlockRequest, n, Bootstrap(n))
  /\ UNCHANGED << nodes, nInMsg, nOutStreamMsg >>

(* If the node's bootstrapped NewApprovedBlockRequest is successful, the success *)
(* message can be removed from the node's Out message queue. *)
SuccessFromNewToInit == \E n \in nodes :
  /\ nStatus[n] = "init"
  /\ nOutMsg[n] = SentMsgStatus("success", Pack(NewApprovedBlockRequest, n, Bootstrap(n)))
  /\ nOutMsg' = [nOutMsg EXCEPT ![n] = None]
  /\ UNCHANGED << nodes, nInMsg, nOutStreamMsg, nStatus >>

(* If the node's bootstrapped NewApprovedBlockRequest is unsuccessful, another *)
(* attempt can be made. *)
(* Does this allow for inifinite loops of failing/retrying NewApprovedBlockRequests? *)
FailedFromNewToInit == \E n \in nodes :
  /\ nStatus[n] = "init"
  /\ nOutMsg[n] = SentMsgStatus("failed", Pack(NewApprovedBlockRequest, n, Bootstrap(n)))
  /\ SendMsg(NewApprovedBlockRequest, n, Bootstrap(n))  
  /\ UNCHANGED << nodes, nInMsg, nOutStreamMsg, nStatus >>

ResendWhileInit == \E n \in nodes :
  /\ nStatus[n] = "init"
  /\ nOutMsg[n] = None
  /\ ~(Pack(NewApprovedBlockRequest, n, Bootstrap(n)) \in ToSet(nInMsg[Bootstrap(n)]))
  /\ ~(Pack(NewApprovedBlock, Bootstrap(n), n) \in ToSet(nOutStreamMsg[Bootstrap(n)]))
  /\ SendMsg(NewApprovedBlockRequest, n, Bootstrap(n))
  /\ UNCHANGED << nodes, nInMsg, nOutStreamMsg, nStatus >>

FromNewToInit ==
  \/ LaunchFromNewToInit
  \/ SuccessFromNewToInit
  \/ FailedFromNewToInit
  \/ ResendWhileInit

-----------------------------------------------------------------------------
(***************************************************************************)
(* Genesis ceremony begins                                                 *)
(***************************************************************************)
(* node with ceremony_master status and without NewUnapprovedBlock in their In *)
(* or OutStream queues, can broadcast NewUnapprovedBlock to all other nodes.   *)
CMBroadcastUnapprovedBlock == \E n \in nodes :
  /\ nStatus[n] = "ceremony_master"
  /\ ~(\E p \in ToSet(nOutStreamMsg[n]) : p.msg.type = NewUnapprovedBlock.type)
  /\ ~(\E p \in ToSet(nInMsg[n]) : p.msg.type = NewUnapprovedBlock.type)
  /\ BroadcastStream(NewUnapprovedBlock, n, nodes \ {n})
  /\ UNCHANGED << nodes, nStatus, nInMsg, nOutMsg >>

LaunchCeremonyMaster == CMBroadcastUnapprovedBlock

(***************************************************************************)
(*  Ceremony master message handling                                       *)
(***************************************************************************)
(* Ceremony master node turns a BlockApproval into a NewApprovedBlock and  *)
(* broadcasts the NewApprovedBlock to all other nodes and changes to *)
(* running status. *)
CeremonyMasterHandlesBlockApproval == \E n \in nodes :
  /\ Handling(n, "ceremony_master", "BlockApproval")
  /\ TransitionTo(n, "running")
  /\ BroadcastStream(NewApprovedBlock, n, nodes \ {n})
  /\ UNCHANGED << nodes, nOutMsg>>

(* Ceremony master node(s) only handle BlockApproval *)
CeremonyMasterHandlesApprovedBlock        == DoNotHandle("ceremony_master", "ApprovedBlock")
CeremonyMasterHandlesApprovedBlockRequest == DoNotHandle("ceremony_master", "ApprovedBlockRequest")
CeremonyMasterHandlesUnapprovedBlock      == DoNotHandle("ceremony_master", "UnapprovedBlock")

(***************************************************************************)
(*  Genesis validator message handling                                     *)
(***************************************************************************)
(* Genesis validator node turns an UnapprovedBlock in their In queue into  *)
(* a NewBlockApproval in their OutStream queue and ~> init status. *)
GenesisValidatorHandlesUnapprovedBlock == \E n \in nodes :
  /\ Handling(n, "genesis_validator", "UnapprovedBlock")
  /\ TransitionTo(n, "init")
  /\ StreamMsg(NewBlockApproval, n, Sender(n))
  /\ UNCHANGED << nodes, nOutMsg >>

(* Genesis validator node(s) only handle UnapprovedBlock *)
GenesisValidatorHandlesApprovedBlock        == DoNotHandle("genesis_validator", "ApprovedBlock")
GenesisValidatorHandlesApprovedBlockRequest == DoNotHandle("genesis_validator", "ApprovedBlockRequest")
GenesisValidatorHandlesBlockApproval        == DoNotHandle("genesis_validator", "BlockApproval")

(***************************************************************************)
(*  Initializing message handling                                          *)
(***************************************************************************)
(* init node + ApprovedBlock in In queue ~> running status *)
InitHandlesApprovedBlock == \E n \in nodes :
  /\ Handling(n, "init", "ApprovedBlock")
  /\ TransitionTo(n, "running")
  /\ UNCHANGED << nodes, nOutMsg, nOutStreamMsg >>

(* init node with UnapprovedBlock in In queue, sends a NewBlockApproval to the *)
(* sender of that UnapprovedBlock. *)
InitHandlesUnapprovedBlock == \E n \in nodes :
  /\ Handling(n, "init", "UnapprovedBlock")
  /\ StreamMsg(NewBlockApproval, n, Sender(n))
  /\ UNCHANGED << nodes, nStatus, nOutMsg >>

(* init nodes only handle ApprovedBlock or UnapprovedBlock *)
InitHandlesApprovedBlockRequest == DoNotHandle("init", "ApprovedBlockRequest")
InitHandlesBlockApproval        == DoNotHandle("init", "BlockApproval")

(***************************************************************************)
(*  Running message handling                                               *)
(***************************************************************************)
(* running node with ApprovedBlockRequest in In queue, sends a NewApprovedBlock *)
(* to the sender of that ApprovedBlockRequest. *)
RunningHandlesApprovedBlockRequest == \E n \in nodes :
  /\ Handling(n, "running", "ApprovedBlockRequest")
  /\ StreamMsg(NewApprovedBlock, n, Sender(n))
  /\ UNCHANGED << nodes, nOutMsg, nStatus >>

(* running nodes only handle ApprovedBlockRequest *)
RunningHandlesApprovedBlock   == DoNotHandle("running", "ApprovedBlock")
RunningHandlesUnapprovedBlock == DoNotHandle("running", "UnapprovedBlock")
RunningHandlesBlockApproval   == DoNotHandle("running", "BlockApproval")

-----------------------------------------------------------------------------
(* At some point, in all later states, all nodes have running status. *)
EventuallyAllNodesAreRunning == <>[](\A n \in nodes : nStatus[n] = "running")

WeakRunningNode == ~(<>(\E n \in nodes : nStatus[n] = "running"))

-----------------------------------------------------------------------------
(* Status of Node with given id *)
InitNodeStatus(n) == (CHOOSE cn \in Nodes : cn.id = n).status

(* Never used... *)
InitNodeState(n) == [bootstrap |-> Bootstrap(n)]
(* LET node == (CHOOSE cn \in Nodes : cn.id = n)
   IN  [bootstrap |-> node.bootstrap] *)

(* nodes are the set of Node ids, nodes are given initial statuses,   *)
(* In and OutStream queues are empty, and Out queues are set to << >>. *)
Init ==
  /\ nodes = {n.id : n \in Nodes}
  /\ nStatus = [n \in nodes |-> InitNodeStatus(n)]
  /\ nInMsg = [n \in nodes |-> << >>]
  /\ nOutStreamMsg = [n \in nodes |-> << >>]
  /\ nOutMsg = [n \in nodes |-> None]
  /\ \E n \in nodes : nStatus[n] = "ceremony_master"
  /\ \E n \in nodes : nStatus[n] = "genesis_validator"

Next ==
  (* Message drops/transfers *)
  \/ \E mt \in MessageType : TransferStreamMsg(mt)
  \/ TransferMsg  
  \/ LooseStreamMsg
  \/ LooseMsg
  (* Message/node status changes *)
  \/ FromNewToInit
  (* Genesis ceremony *)
  \/ LaunchCeremonyMaster
  \/ CeremonyMasterHandlesApprovedBlock
  \/ CeremonyMasterHandlesApprovedBlockRequest
  \/ CeremonyMasterHandlesUnapprovedBlock
  \/ CeremonyMasterHandlesBlockApproval
  \/ GenesisValidatorHandlesApprovedBlock
  \/ GenesisValidatorHandlesApprovedBlockRequest
  \/ GenesisValidatorHandlesUnapprovedBlock
  \/ GenesisValidatorHandlesBlockApproval
  \/ InitHandlesApprovedBlock
  \/ InitHandlesApprovedBlockRequest
  \/ InitHandlesUnapprovedBlock
  \/ InitHandlesBlockApproval  
  \/ RunningHandlesApprovedBlock
  \/ RunningHandlesApprovedBlockRequest
  \/ RunningHandlesUnapprovedBlock
  \/ RunningHandlesBlockApproval  

Spec ==
  (* safety *)
  /\ Init /\ []([Next]_vars)
  (* liveness *)
  /\ SF_vars(TransferMsg)
  /\ \A mt \in MessageType : SF_vars(TransferStreamMsg(mt))
  /\ WF_vars(FromNewToInit)
  /\ WF_vars(LaunchCeremonyMaster)
  /\ WF_vars(CeremonyMasterHandlesApprovedBlock)
  /\ WF_vars(CeremonyMasterHandlesApprovedBlockRequest)
  /\ WF_vars(CeremonyMasterHandlesUnapprovedBlock)
  /\ WF_vars(CeremonyMasterHandlesBlockApproval)
  /\ WF_vars(GenesisValidatorHandlesApprovedBlock)
  /\ WF_vars(GenesisValidatorHandlesApprovedBlockRequest)
  /\ WF_vars(GenesisValidatorHandlesUnapprovedBlock)
  /\ WF_vars(GenesisValidatorHandlesBlockApproval)
  /\ WF_vars(InitHandlesApprovedBlock)
  /\ WF_vars(InitHandlesApprovedBlockRequest)
  /\ WF_vars(InitHandlesUnapprovedBlock)
  /\ WF_vars(InitHandlesBlockApproval)  
  /\ WF_vars(RunningHandlesApprovedBlock)
  /\ WF_vars(RunningHandlesApprovedBlockRequest)
  /\ WF_vars(RunningHandlesUnapprovedBlock)
  /\ WF_vars(RunningHandlesBlockApproval)
  
THEOREM Spec => EventuallyAllNodesAreRunning

=============================================================================
\* Modification History
\* Last modified Mon Nov 18 21:02:52 EST 2019 by isaac
\* Created Fri Nov 15 13:26:32 EST 2019 by isaac
