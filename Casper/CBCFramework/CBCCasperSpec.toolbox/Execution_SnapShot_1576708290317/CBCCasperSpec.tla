--------------------------- MODULE CBCCasperSpec ---------------------------
EXTENDS FiniteSets, Integers, Sequences, TLC

CONSTANTS
  nodes,      \* set of validator ids
  weights,    \* tuple of validator weights
  threshold,  \* fault tolerance threshold
  values,     \* set of consensus values
  genesis     \* genesis message

VARIABLES
  dags,       \* tuple of local DAGs for each validator (only contains parent pointers)
  faulty,     \* tuple of sets of observed equivocating validators
  scored_q,   \* tuple of records of scored messages with score
  unscored_q, \* tuple of tuples of messages which have not been scored
  sent_msgs,  \* tuple of tuples of messages sent by each validator
  equiv_pairs, \* tuple of sets of tuples of equivocated messages
  estimates,  \* tuple of sets of best current estimates
  states      \* tuple of validator states (contains all justification pointers)

vars == <<faulty,scored_q,unscored_q,sent_msgs,equiv_pairs,estimates,states>>

----------------------------------------------------------------------------
(************)
(* Messages *)
(************)
\* Unscored message = (estimate, sender, justification)
Msg(est,from,just) == [estimate |-> est, sender |-> from, justification |-> just]

\* Scored message.
ScoredMsg(_msg,_score) == [msg |-> _msg, score |-> _score]

\* Scored estimate.
ScoredEst(_est,_score) == [est |-> _est, score |-> _score]

\* Message decomposition functions.
Estimate(msg) == msg.estimate
Sender(msg) == msg.sender
Justification(msg) == msg.justification
\*LET j == msg.justification
\*IN  j.parents \cup j.nonparents
\*Just(p,n)  == [parents |-> p, nonparents |-> n]
\*OnlyPar(p) == [parents |-> p, nonparents |-> {}]
\*Parents(msg) == msg.justification.parents

\* The genesis message is abstract - it does not have estimate, sender, or justification fields.

\* Set of nodes who have sent at least one message.
Senders == {n \in nodes: sent_msgs[n] # <<>>}
Observed(msgs) == {Sender(m): m \in (msgs \ {genesis})}

----------------------------------------------------------------------------
(*************)
(* Estimator *)
(*************)
\*TODO: make precise
\* GHOST fork choice rule - latest honest estimate driven
\* output should be ranked set of tips
GHOST(state) ==
  IF state = {genesis}
  THEN values
  ELSE {Estimate(m): m \in (state \ {genesis})}

----------------------------------------------------------------------------
(***********************************************************)
(* Auxiliary functions from SequencesExt community module. *)
(* See https://github.com/tlaplus/                         *)
(***********************************************************)
ToSet(s) == {s[i]: i \in DOMAIN s}

IsInjective(f) == \A i, j \in DOMAIN f : (f[i] = f[j]) => (i = j)

SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

----------------------------------------------------------------------------
(*************************************)
(* Auxiliary Functions & Definitions *)
(*************************************)
\* Returns the tuple of unscored messages from tuple of scored messages.
RECURSIVE Unscore(_)
Unscore(seq) ==
  IF seq = <<>>
  THEN <<>>
  ELSE <<Head(seq).msg>> \o Unscore(Tail(seq))

\* Set of all messages received by a given validator.
ReceivedMsgs(n) == ToSet(unscored_q[n] \o Unscore(scored_q[n])) \ {genesis}

\* Pick an arbitrary element from the given set.
Pick(S) == CHOOSE s \in S : TRUE

\* Maximum element of a set.
Max(S) == Pick({n \in S : \A m \in S : m =< n})

\* Set of nodes who have received at least one message (excludes genesis).
Receivers == {n \in nodes: ReceivedMsgs(n) # {}}

\* Broadcast given message to all other validators in given set.
\* arguments: message, sender, set of receivers (sender is excluded)
Broadcast(msg,n,rec) ==
  [i \in nodes |-> IF i \in (rec \ {n})
                   THEN <<msg>>
                   ELSE <<>>
  ]

\* Apply binary operation over entire set.
RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) ==
  IF S = {}
  THEN value
  ELSE LET s == Pick(S)
       IN  SetReduce(Op, S \ {s}, Op(s, value)) 

SetSum(S) == LET op(a,b) == a + b  IN SetReduce(op,S,0)
SetAnd(S) == LET op(a,b) == a /\ b IN SetReduce(op,S,TRUE)
SetOr(S)  == LET op(a,b) == a \/ b IN SetReduce(op,S,FALSE)

\* Apply binary operation over entire tuple.
RECURSIVE SeqReduce(_, _, _)
SeqReduce(Op(_, _), s, value) ==
  IF s = <<>>
  THEN value
  ELSE LET h == Head(s)
       IN  SeqReduce(Op, Tail(s), Op(h, value))

SeqSum(S) == LET op(a,b) == a + b  IN SeqReduce(op,S,0)
SeqAnd(S) == LET op(a,b) == a /\ b IN SeqReduce(op,S,TRUE)
SeqOr(S)  == LET op(a,b) == a \/ b IN SeqReduce(op,S,FALSE)

\* Turns a set of 2-tuples into the set of individual elements.
RECURSIVE UnSeqSet(_)
UnSeqSet(S) ==
  IF S = {}
  THEN {}
  ELSE LET s == Pick(S)
       IN  {Head(s),Head(Tail(s))} \cup UnSeqSet(S \ {s})

\* Union with each tuple element.
UnionEach(seq,set) == [i \in DOMAIN seq |-> seq[i] \cup set]

\* Turns set of elements into the set of all possible 2-tuples.
Pairs(S) == {s \in Seq(S): Len(s) = 2}

\* Global set of faulty validators.
GlobalFaultySet == UNION(ToSet(faulty))

\* Initialize tuple with given value.
SetAllTo(val) == [i \in 1..Cardinality(nodes) |-> val]

(* The dependencies of a message m are the messages in the justification *)
(* of m and in the justifications of the justifications of m and so on,  *)
(* i.e. justifications all the way down.                                 *)
RECURSIVE Dep(_)
Dep(msg) ==
  IF msg = genesis
  THEN {genesis}
  ELSE IF Cardinality(Justification(msg)) = 1
       THEN Justification(msg)
       ELSE Justification(msg)
            \cup UNION{Dep(m): m \in (Justification(msg) \ {genesis})}

\* Gets the set of dependencies of all the messages in a set of messages.
DepSet(msgs) == UNION{Dep(m) : m \in msgs}

\* Dependency depth of a message.
RECURSIVE Depth(_)
Depth(msg) ==
  IF msg = genesis
  THEN 0
  ELSE 1 + Max({Depth(m): m \in Dep(msg)})

\* Dependency depth of a set of messages.
DepthSet(msgs) ==
  IF msgs = {genesis}
  THEN 0
  ELSE Max({Depth(m): m \in msgs})

\* Latest message(s) from a validator in a given set of messages.
LatestMsgs(n,msgs) == {genesis} \cup
  {m \in (msgs \ {genesis}):
     /\ Sender(m) = n
     /\ ~\E m0 \in (msgs \ {genesis}) :
        /\ Sender(m0) = n
        /\ m # m0
        /\ m \in Dep(m0)
  }

\* Latest estimate(s) from a validator in a given set of messages.
LatestEsts(n,msgs) == {Estimate(m): m \in (LatestMsgs(n,msgs) \ {genesis})}

\* Set of estimates in a state.
Estimates(state) == {Estimate(m): m \in ((state \cup DepSet(state)) \ {genesis})}

\* Justifications of a set of messages.
Justifications(msgs) == UNION{Justification(m): m \in (msgs \ {genesis})}

\* Two messages are equivocating if they have the same sender, but do not justify each other.
Equivocation(m1,m2) ==
  /\ m1 # m2
  /\ Sender(m1) = Sender(m2)
  /\ m1 \notin (Dep(m2) \ {genesis})
  /\ m2 \notin (Dep(m1) \ {genesis})

CheckDepsForEquiv(msgs) ==
  LET deps == DepSet(msgs)
  IN  /\ Cardinality(deps) > 1
      /\ \E m1,m2 \in (deps \ {genesis}) : Equivocation(m1,m2)

EquivPairsInDeps(msgs) ==
  IF ~CheckDepsForEquiv(msgs)
  THEN {}
  ELSE {<<m1,m2>> \in (DepSet(msgs) \ {genesis}) \X (DepSet(msgs) \ {genesis}): Equivocation(m1,m2)}

\* A validator is faulty if it sends equivocating messages.
\* Checks if a validator equivicates in a given set of messages.
FaultyNode(n,msgs) ==
  /\ \E m1 \in (DepSet(msgs) \ {genesis}) : 
     /\ \E m2 \in (DepSet(msgs) \ {genesis}) :
        /\ Sender(m1) = n
        /\ Equivocation(m1,m2)

\* Set of faulty validators in an observed set of messages.
FaultyNodes(msgs) == {n \in nodes : FaultyNode(n,msgs)}

\* Messages from equivocating validators in a given set of messages.
EquivocatedMsgs(n,msgs) == DepSet(msgs) \cap UnSeqSet(equiv_pairs[n])

\* Checks existence of equivocated messages received by the given validator.
EquivReceived(n) == \E <<m1,m2>> \in Pairs(DepSet(ReceivedMsgs(n))) : Equivocation(m1,m2)

\* Arbitrary node who has observed an equivocation.
Equiv_node == CHOOSE n \in nodes : EquivReceived(n)

\* Set of messages later than a given message in a given set of messages.
Later(msg,msgs) == {m \in (msgs \ {genesis}): msg \in Justification(m)}

\* Honest messages - messages from non-faulty validators.
HonestMsgs(n,msgs) == DepSet(msgs) \ (EquivocatedMsgs(n,msgs) \cup {genesis})

\* Set of latest honest messages received by a validator.
LatestHonestMsgs(n,msgs) == {m \in HonestMsgs(n,msgs): m \in LatestMsgs(n,msgs)}

\* Set of latest honest estimates received by a validator.
LatestHonestEsts(n,msgs) == {Estimate(m): m \in LatestHonestMsgs(n,msgs)}

\* Weights of subsets of validators.
Weight(set) ==
  SeqSum([n \in 1..Cardinality(nodes) |-> IF n \in set THEN weights[n] ELSE 0])

TotalWeight == Weight(nodes)
FaultWeight(state) == Weight(FaultyNodes(state))

\* Two validators are agreeing with each other on an estimate in a set of messages if:
\*  - n1 has exactly one latest message in the set
\*  - n2 has exactly one latest message in the justification of n1's latest message
\*  - the estimates of these latest messages agree with the given estimate
\* i.e. n1 is not equivocating in the set of messages and
\*      n2 is not equivocating in the justification of n1's latest message
Agreeing(n1,n2,estimate,msgs) ==
  LET n1_latest_msg == Pick(LatestMsgs(n1,msgs))
      n2_latest_msg == Pick(LatestMsgs(n2,Justification(n1_latest_msg)))
  IN  /\ Cardinality(LatestMsgs(n1, msgs)) = 1
      /\ Cardinality(LatestMsgs(n2,Justification(n1_latest_msg))) = 1
      /\ Estimate(n1_latest_msg) = estimate
      /\ Estimate(n2_latest_msg) = estimate

\* Two validators are disagreeing with each other on an estimate in a set of messages if:
\*  - n1 has exactly one latest message in messages
\*  - n2 has exactly one latest message in the justification of n1's latest message
\*  - n2 has a new latest message that doens't agree with the estimate
Disagreeing(n1,n2,estimate,msgs) == 
  /\ Cardinality(LatestMsgs(n1,msgs)) = 1
  /\ LET n1_latest_msg == Pick(LatestMsgs(n1,msgs))
     IN  /\ Cardinality(LatestMsgs(n2,Justification(n1_latest_msg))) = 1
         /\ LET n2_latest_msg == Pick(LatestMsgs(n2,Justification(n1_latest_msg)))
            IN  \E m \in msgs: /\ n2_latest_msg \in Dep(m)
                               /\ estimate # Estimate(m)

\* An e-clique is a group of non-faulty nodes in a set of observed messages such that:
\*  - they mutually see each other agreeing with the given estimate in the given set of messages, and
\*  - they mutually cannot see each other disagreeing with the given estimate in the given set of messages.
(* If nodes in an e-clique see each other agreeing on e and can't see each other disagreeing on e, *)
(* then there does not exist any new message from inside the clique that will cause them to assign *)
(* lower scores to e. Further, if the clique has more than half of the validators by weight,       *)
(* then no messages external to the clique can raise the scores these validators assign to         *)
(* a competing estimate to cause it to become larger than the score they assign to e.              *)
Eclique(estimate,state) ==
  {sub \in SUBSET(nodes):
     /\ Cardinality(sub) > 1
     /\ \A n1 \in sub :
          \A n2 \in (sub \ {n1}) :
            /\ Agreeing(n1,n2,estimate,state) 
            /\ ~Disagreeing(n1,n2,estimate,state)
            /\ ~FaultyNode(n1,state)
            /\ ~FaultyNode(n2,state)
  }

\* Set of messges received from honest validators by a particular valiadtor.
HonestReceivedMsgs(n) == {m \in ReceivedMsgs(n): m \notin UnSeqSet(equiv_pairs[n])}

----------------------------------------------------------------------------
(******************************)
(* Protocol Messages & States *)
(******************************)
\* Protocol messages have an estimate given by the estimator applied to the justification.
ValidMsg(msg) ==
  \/ msg = genesis            \* genesis is a valid message
  \/ /\ msg # genesis         \* non-genesis message is valid if sender and estimate are valid
     /\ Sender(msg) \in nodes
     /\ Estimate(msg) \in GHOST(Justification(msg))

ProtocolMsgs == {m \in UNION({ToSet(sent_msgs[n]): n \in nodes}): ValidMsg(m)}

(* Protocol states are finite sets of protocol messages which contain *)
(* their justifications and have fault weight less than the theshold. *)
ValidState(state) ==
  \/ state = {genesis}
  \/ \A m \in (state \ {genesis}) :
     /\ Justification(m) \subseteq state
     /\ FaultWeight(state) < threshold

ProtocolStates ==
  {s \in SUBSET(ProtocolMsgs):
     /\ ValidState(s)
     /\ IsFiniteSet(s)
  }

SentSet  == UNION({ToSet(sent_msgs[n]): n \in nodes})
StateSet == UNION({states[n]: n \in nodes})

----------------------------------------------------------------------------
(***************************)
(* Decisions & Consistency *)
(***************************)
\* Futures of a given state.
Futures(state) == {s \in ProtocolStates: state \subseteq s}

\* Check whether a given property is decided in a given state.
Decided(prop,state) == \A s \in Futures(state) : prop[s]

\* Decisions in a given state: set of properties which are decided in the state.
Decisions(state) ==
  {prop \in [ProtocolStates -> {FALSE, TRUE}]: Decided(prop,state)}

----------------------------------------------------------------------------
(**************************)
(* (Clique) Safety Oracle *)
(**************************)
\* Checks for existence of an e-clique with sufficient cumulative weight.
EcliqueEstimateSafety(estimate,state) ==
  \* state is valid
  \E ec \in Eclique(estimate,state) :
    2 * SeqSum(Weight(ec)) > TotalWeight + threshold - FaultWeight(state)

\* A temporal property checking that finality can eventually be reached.
CheckSafetyOracle ==
  \A n \in (nodes \ GlobalFaultySet) :  <>(\E v \in values : EcliqueEstimateSafety(v,states[n]))

----------------------------------------------------------------------------
\* Previous messages.
PrevMsg(msg) ==
  IF Justification(msg) = {genesis}
  THEN {genesis}
  ELSE {genesis} \cup
       UNION{LatestMsgs(n,Justification(msg)): n \in Observed(Justification(msg))}

\* Previous estimates.
PrevEst(msg) ==
  IF Justification(msg) = {genesis}
  THEN {}
  ELSE UNION{LatestEsts(n,Justification(msg)): n \in Observed(Justification(msg))}

\*TODO: Distinguish parents from non-parents for scoring.

\* Message ancestry.
RECURSIVE n_cestorMsg(_,_)
n_cestorMsg(msg,n) ==
  IF n = 0 \/ msg = genesis
  THEN msg
  ELSE UNION(n_cestorMsg(PrevMsg(msg),n-1))

\* Estimate ancestry.
RECURSIVE n_cestorEst(_,_)
n_cestorEst(msg,n) ==
  IF msg = genesis
  THEN {}
  ELSE IF n = 0
       THEN msg
       ELSE UNION(n_cestorMsg(PrevEst(msg),n-1))

\* Block membership: b1 is conatined in b2's chain/dag.
\*Membership(b1,b2) == \E n \in Nat : b1 = n_cestor(b2,n)
Membership(m1,m2) ==
 \/ m1 = genesis
 \/ m1 = m2
 \/ /\ m1 # genesis
    /\ Estimate(m1) \in Estimates({m2} \cup Dep(m2))

\* Set of validators supporting a given estimate in a dag.
RECURSIVE Supporters(_,_)
Supporters(est,state) ==
  IF state = {genesis} \/ est \notin Estimates(state)
  THEN {}
  ELSE LET m == Pick(state \ {genesis})
       IN  IF est \in Estimates({m})
           THEN {Sender(m)} \cup Supporters(est,Justification(m)) \cup Supporters(est,(state \ {m}))
           ELSE Supporters(est,(state \ {m}))

\* Score of a block (estimate) in a given state.
\*Score(msg,state) ==
\*  LET S == {n \in nodes: \E m \in LatestHonestEsts(n,state) : Membership(msg,m)}
\*  IN  SeqSum([n \in S |-> weights[n]])

\* Score: validator weight only propogates down parent pointers.
Score(est,state) == Weight(Supporters(est,state) \ GlobalFaultySet)

\* Children: a child of a block has that block as (one of) its Prev blocks.
Children(msg,state) == {m \in state: msg \in PrevMsg(m)}

\* Updates scored message scores in current state.
RECURSIVE UpdateScores(_,_)
UpdateScores(n,scored) ==
  IF scored = <<>>
  THEN <<>>
  ELSE LET hd == Head(scored)
           tl == Tail(scored)
       IN  IF hd = genesis
           THEN <<ScoredMsg(genesis,TotalWeight)>> \o UpdateScores(n,tl)
           ELSE <<ScoredMsg(hd.msg,Score(Estimate(hd.msg),states[n]))>>
                \o UpdateScores(n,tl)

\* Scores all unscored messages in current state.
RECURSIVE ScoreUnscored(_,_)
ScoreUnscored(n,unscored) ==
  IF unscored = <<>>
  THEN <<>>
  ELSE LET hd == Head(unscored)
           tl == Tail(unscored)
       IN  IF hd \in EquivReceived(n)
           THEN ScoreUnscored(n,tl)
           ELSE <<ScoredMsg(hd,Score(hd,states[n]))>> \o ScoreUnscored(n,tl)

----------------------------------------------------------------------------
\* Local DAG views
\* - dags[n] consists of a set of nested sets of estimates
\* - what is the exact relation between dags[n] and states[n]? refinement?

\* Set of estimates present in a DAG.
RECURSIVE DagEstimateSet(_)
DagEstimateSet(dag) ==
  LET l == Len(dag)
  IN  IF dag = <<genesis>>
      THEN {}
      ELSE ToSet(SubSeq(dag,1,l-1)) \cup DagEstimateSet(dag[l])

\* DAG height.
RECURSIVE DagHeight(_)
DagHeight(dag) ==
  IF Len(dag) <= 1
  THEN 0
  ELSE 1 + DagHeight(dag[Len(dag)])

\* Depth of estimate in DAG.
RECURSIVE DagDepth(_,_)
DagDepth(est,dag) ==
  LET l == Len(dag)
      d == DagDepth(est,dag[l])
  IN  IF est = genesis
      THEN DagHeight(dag)
      ELSE IF est \notin DagEstimateSet(dag)
           THEN -1
           ELSE IF l <= 1
                THEN 0
                ELSE 1 + d

\* Set of DAG tips.
Tips(dag) == ToSet(SubSeq(dag,1,Len(dag)-1))

\* Add scored estimate at level.
AddAtLevel(est,dag) ==
  IF dag = <<>>
  THEN <<est>>
  ELSE IF Depth(<<>>) \* finish
       THEN <<>>      \* finish
       ELSE <<>>      \* finish

\* Add estimate to dag.
AddEstimateToDag(n,est) ==
  LET e == <<est>>
      d == dags[n]
  IN  IF dags[n] = <<>>
      THEN e
      ELSE IF Depth(est.est) > DagHeight(d)
           THEN e \o <<d>>
           ELSE <<>> \* finish

\* TODO
\* Update DAG with recently received tuple of messages.
UpdateDag(dag,msgs) == dag

----------------------------------------------------------------------------
\* Preliminary conditions
ThresholdCheck == threshold \geq 0 /\ threshold < TotalWeight
NodeWeightLen  == Len(weights) = Cardinality(nodes)
AllSendsValid  == SentSet  = {m \in SentSet: ValidMsg(m)}
AllStatesValid == StateSet = {s \in StateSet: ValidState(s)}

\* Must hold in all reachable states.
TypeOK ==
  /\ AllSendsValid
  /\ AllStatesValid

----------------------------------------------------------------------------
\* Initial state conditions
\* All validators start with scored genesis block only.
Init ==
  /\ ThresholdCheck
  /\ NodeWeightLen
  /\ dags       = SetAllTo(<<genesis>>)
  /\ faulty     = SetAllTo({})
  /\ scored_q   = SetAllTo(<<ScoredMsg(genesis,TotalWeight)>>)
  /\ unscored_q = SetAllTo(<<>>)
  /\ sent_msgs  = SetAllTo(<<>>)
  /\ equiv_pairs = SetAllTo({})
  /\ estimates  = SetAllTo(values)
  /\ states     = SetAllTo({genesis})

----------------------------------------------------------------------------
\* Updates

\* A validator can update their dag.
Update_Dag_And_Scores ==
  /\ dags'       = [n \in nodes |-> UpdateDag(dags[n],scored_q[n])]
  /\ unscored_q' = SetAllTo(<<>>)
  /\ scored_q'   = [n \in nodes |->
     UpdateScores(scored_q[n],states[n]) \o ScoreUnscored(unscored_q[n],states[n])]
  /\ UNCHANGED <<faulty,sent_msgs,equiv_pairs,estimates,states>>

\* A validator can update their set of valid estimates.
Update_Estimates ==
  /\ estimates' = [n \in nodes |-> GHOST(states[n])]
  /\ UNCHANGED <<dags,faulty,scored_q,unscored_q,sent_msgs,equiv_pairs,states>>

Update ==
  /\ Update_Dag_And_Scores
  /\ Update_Estimates

----------------------------------------------------------------------------
(***************)
(* Transitions *)
(***************)
\* Sending/Receiving/Dropping messages
\* Given validator sends given message to given set of validators.
Send_Msg(msg,n,rec) ==
  /\ unscored_q' = unscored_q \o Broadcast(msg,n,rec)
  /\ sent_msgs'  = [sent_msgs EXCEPT ![n] = sent_msgs[n] \o <<msg>>]
  /\ scored_q'   = [scored_q  EXCEPT ![n] = scored_q[n] \o <<ScoredMsg(msg,weights[n])>>]
  /\ states'     = [states    EXCEPT ![n] = states[n] \cup {msg}]

\* Honest validator sends honest message.
Send_Honest ==
  /\ \E n \in (nodes \ GlobalFaultySet) : estimates[n] # {} \* enabling condition: honest node with valid estimates
  /\ LET v == RandomElement({n \in (nodes \ GlobalFaultySet): estimates[n] # {}}) \* honest validator with valid estimate
         e == RandomElement(estimates[v])
     IN  /\ Send_Msg(Msg(e,v,states[v]),v,nodes)
         /\ UNCHANGED <<dags,faulty,equiv_pairs,estimates>>

\* Dropped message.
Send_Drop ==
  /\ \E n \in nodes : estimates[n] # {}        \* enabling condition: node with valid estimates
  /\ LET v == RandomElement({n \in nodes : estimates[n] # {}})
         e == RandomElement(estimates[v])
     IN  /\ sent_msgs'  = [sent_msgs EXCEPT ![v] = sent_msgs[v] \o <<Msg(e,v,states[v])>>] 
         /\ scored_q'   = [scored_q  EXCEPT ![v] = scored_q[v] \o <<ScoredMsg(Msg(e,v,states[v]),weights[v])>>]
         /\ states'     = [states    EXCEPT ![v] = states[v] \cup {Msg(e,v,states[v])}]
         /\ UNCHANGED <<dags,faulty,unscored_q,equiv_pairs,estimates>>

\* Equivocations.
\* Send messages with different estimates to disjoint sets of validators.
Send_Equiv_Est ==
  /\ \E n \in nodes : Cardinality(estimates[n]) > 1
  /\ LET v == RandomElement({n \in nodes: Cardinality(estimates[n]) > 1})
        N1 == RandomElement({sub1 \in SUBSET(nodes \ {v}): sub1 # {}})
        N2 == RandomElement({sub2 \in SUBSET(nodes \ (N1 \cup {v})): sub2 # {}})
        e1 == RandomElement(estimates[v])
        e2 == RandomElement(estimates[v] \ {e1})
     IN /\ Send_Msg(Msg(e1,v,states[v]),v,N1)
        /\ Send_Msg(Msg(e2,v,states[v]),v,N2)
        /\ UNCHANGED <<dags,faulty,equiv_pairs>>

\* Send messages with different justifications to disjoint sets of validators.
Send_Equiv_Just ==
  /\ \E n \in nodes : Cardinality(states[n]) > 1 /\ estimates[n] # {}
  /\ LET v == RandomElement({n \in nodes: Cardinality(states[n]) > 1})
         e == RandomElement(estimates[v])
        N1 == RandomElement({sub1 \in SUBSET(nodes \ {v}): sub1 # {}})
        N2 == RandomElement({sub2 \in SUBSET(nodes \ (N1 \cup {v})): sub2 # {}})
        j1 == RandomElement(SUBSET(states[v]))
        j2 == RandomElement({j \in SUBSET(states[v]): j # j1})
     IN /\ Send_Msg(Msg(e,v,j1),v,N1)
        /\ Send_Msg(Msg(e,v,j2),v,N2)
        /\ UNCHANGED <<dags,faulty,equiv_pairs>>

\* Send messages with different estimates and different justifications to disjoint sets of validators.
Send_Equiv_Both ==
  /\ \E n \in nodes : Cardinality(states[n]) > 1 /\ Cardinality(estimates[n]) > 1
  /\ LET v == RandomElement({n \in nodes: Cardinality(states[n]) > 1})
        e1 == RandomElement(estimates[v])
        e2 == RandomElement(estimates[v] \ {e1})
        N1 == RandomElement({sub1 \in SUBSET(nodes \ {v}): sub1 # {}})
        N2 == RandomElement({sub2 \in SUBSET(nodes \ (N1 \cup {v})): sub2 # {}})
        j1 == RandomElement(SUBSET(states[v]))
        j2 == RandomElement({j \in SUBSET(states[v]): j # j1})
     IN /\ Send_Msg(Msg(e1,v,j1),v,N1)
        /\ Send_Msg(Msg(e2,v,j2),v,N2)
        /\ UNCHANGED <<dags,faulty,equiv_pairs>>

Send_Success ==
  \/ Send_Honest
  \/ Send_Equiv_Est
  \/ Send_Equiv_Just
  \/ Send_Equiv_Both

Send ==
  \/ Send_Success
  \/ Send_Drop

------
\*TODO
\* Catch and report equivocation:
(* all validators except the equivocating validator add the equivicating validator *)
(* to faulty set and the equivocated messages to equiv_pairs and states *)
HandleEquiv ==
  /\ \E n \in nodes : CheckDepsForEquiv(ReceivedMsgs(n))
  /\ LET n == RandomElement({v \in nodes: CheckDepsForEquiv(ReceivedMsgs(v))})
         E == EquivPairsInDeps(ReceivedMsgs(n))
         p == Pick(E)
         e == Sender(Head(p))
     IN  /\ faulty'     = [UnionEach(faulty,{e})      EXCEPT ![e] = faulty[e]]
         /\ equiv_pairs' = [UnionEach(equiv_pairs,E)  EXCEPT ![e] = equiv_pairs[e]]
         /\ states'     = [UnionEach(states,ToSet(E)) EXCEPT ![e] = states[e]]
         /\ UNCHANGED <<dags,scored_q,unscored_q,sent_msgs,estimates>>

Next ==
  \/ Send
  \/ HandleEquiv

SafetySpec ==
  /\ Init
  /\ [][Next]_vars

LivenessSpec ==
  /\ WF_vars(Send)
  /\ SF_vars(Update)
  /\ SF_vars(HandleEquiv)

Spec ==
  /\ SafetySpec
  /\ LivenessSpec

=============================================================================
\* Modification History
\* Last modified Wed Dec 18 17:24:21 EST 2019 by isaac
\* Created Wed Nov 27 17:00:08 EST 2019 by isaac
