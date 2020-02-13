-------------------------- MODULE cbccasper_binary --------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

\* The first four are parameters of the protocol, and the rest are defined for purposes of model checking
\*    - validators: a set specifying the names (consecutive integers) of the validators
\*    - validator_weights: a tuple assigning a weight (integer) to each validator
\*    - byzantine_threshold: a number less than the sum of the weights of all the validators
\*    - consensus_values: the set of values the validators decide on; the binary values 0 and 1 in this model
\*    - validators_initial_values: the estimates without receiving other messages
\*    - message_ids: a number used to limit the number of messages sent in the model
\*    - byzantine_fault_nodes: define the equivocating nodes
CONSTANTS           
    validators,   
    validator_weights,                               
    byzantine_threshold,
    consensus_values, 
    validators_initial_values,
    message_ids, 
    byzantine_fault_nodes
    
\* The following is written in PlusCal, which will be transpiled to TLA+. 
\* The transpiled TLA+ code is appended to the PlusCal code, and the PlusCal code will appear as comments. 
    
(* --algorithm algo
\*    variables are updated as the model checker runs:
\*       - all_msg: a set of all messages ids (integers)
\*       - equivocating_msg: a set specifying all the equivocating messages
\*                          (not all the validators receive that same message)
\*       - msg_sender: a tuple specifying the sender of the message with the given id
\*       - msg_estimate: a tuple specifying the estimate of the message with the given id
\*       - msg_justification: a tuple specifying the justification of the message
\*                           (set of messages used to calculate the estimate) with the given id,
\*       - cur_msg_id: the id of the current message being sent; incremented after every message
\*       - validator_init_done: a tuple indicating whether the validator has sent the initial message
\*                             (1 is done; all the validators are initialized to 0 in the beginning)
\*       - equiv_msg_receivers: a tuple specifying a subset of all validators receiving a certain equivocating message;
\*                              if the message is not equivocating append the empty set
\*       - cur_subset: a 'temp' variable used to store the set of validators receiving the current equivocating message
    variables
        all_msg = {},
        equivocating_msg = {},
        msg_sender = <<>>,
        msg_estimate = <<>>,
        msg_justification = <<>>,
        cur_msg_id = 1,
        validator_init_done = <<0, 0, 0, 0, 0, 0, 0, 0, 0, 0>>,
        equiv_msg_receivers = <<>>,
        cur_subset

    define        
\*       The dependencies of a message m are the messages in the justification of m
\*       and in the justifications of the justifications of m and so on. The set is generated
\*       using a recursive function until the base case is reached - the only justification of
\*       a message is itself.
         dependencies(message) ==
            LET
                RECURSIVE dep(_)
                dep(msg) ==
                    IF Cardinality(msg_justification[msg]) = 1 /\ msg \in msg_justification[msg]
                    THEN {msg}
                    ELSE UNION{dep(msg2) : msg2 \in msg_justification[msg]}
            IN dep(message)
            
\*      Gets the set of dependencies of all the messages in a set of messages.
        dep_set(messages) == messages \union UNION{dependencies(m) : m \in messages}
            
\*      The latest message of a validator in an observed set of messages is the message for which
\*      no other messages sent by the same validator justifies it.
        latest_message(validator, messages) ==
            {msg \in messages:
                /\ msg_sender[msg] = validator
                /\ ~\E msg2 \in messages:
                    /\ msg_sender[msg2] = validator
                    /\ msg /= msg2
                    /\ msg \in dependencies(msg2)
            }
       
\*      Defines the Pick operator used to choose an arbitrary element from a set.
        Pick(S) == CHOOSE s \in S : TRUE
        
\*      Defines the Sum operator used to find the sum of all the elements in a set.
        RECURSIVE SetReduce(_, _, _)
            SetReduce(Op(_, _), S, value) == 
                IF S = {} THEN value
                ELSE LET s == Pick(S) IN SetReduce(Op, S \ {s}, Op(s, value)) 
                                     
        Sum(S) == LET _op(a, b) == a + b IN SetReduce(_op, S, 0)
            
\*      The following defines the estimator used in the binary consesnsus protocol.
\*      The score of an estimate is the sum of the weights of all the validators having
\*      the given estimate in its latest message in a set of observed messages.
\*      The estimator returns the estimate with the larger score. If there's a tie,
\*      in this example, the value 0 is used.
        score(estimate, messages) == 
            LET ss == 
                {v \in validators:
                    /\ Cardinality(latest_message(v, messages)) = 1
                    /\ \E m \in latest_message(v, messages):
                        msg_estimate[m] = estimate}
                ss2 == {validator_weights[v] : v \in ss}
            IN Sum(ss2)
        binary_estimator(messages) ==
            IF score(1, messages) > score(0, messages)
            THEN 1
            ELSE 0
            
\*      Two messages are equivocating if they have the same sender but do not justify each other.
        equivocation(m1, m2) ==
            /\ m1 /= m2
            /\ msg_sender[m1] = msg_sender[m2]
            /\ m1 \notin dependencies(m2)
            /\ m2 \notin dependencies(m1)
            
\*      A validator is byzantine if it sends equivocating messages.
        faulty_node(validator, messages) ==
            /\ \E m1 \in dep_set(messages): 
                /\ \E m2 \in dep_set(messages):
                    /\ validator = msg_sender[m1]
                    /\ equivocation(m1, m2)
                    
\*      Set of byzantine validators in an observed set of messages.
        faulty_nodes(messages) == {v \in validators : faulty_node(v, messages)}
            
\*      Returns the total weight of all byzatine validators.
        fault_weight(messages) == 
            LET byz == faulty_nodes(messages)
            IN Sum({validator_weights[v] : v \in byz})
               
\*      For a given fault tolerance threshold t, a protocol state is the set of messages
\*      with fault weight less than t.
\*      A state transition is possible if one state is a subset of another.       
        protocol_states(messages, t) == {s \in SUBSET(messages) : fault_weight(s) < t}
        protocol_executions(state1, state2) == state1 \subseteq state2
        
\*      Two validators v1 and v2 are agreeing with each other if:
\*        - v1 has exactly one latest message in messages
\*        - v2 has exactly one latest message in the justification of v1's latest message
\*        - the latest messages have estimates that agree with each other
        validators_agreeing(v1, v2, estimate, messages) ==
            /\ Cardinality(latest_message(v1, messages)) = 1
            /\ LET v1_latest_msg == Pick(latest_message(v1, messages))
                IN Cardinality(latest_message(v2, msg_justification[v1_latest_msg])) = 1
                /\ LET v2_latest_msg == Pick(latest_message(v2, msg_justification[v1_latest_msg]))
                    IN estimate = msg_estimate[v2_latest_msg]
                    
\*      Two validators are disagreeing with each other if:
\*        - v1 has exactly one latest message in messages
\*        - v2 has exactly one latest message in the justification of v1's latest message
\*        - v2 has a new latest message that doens't agree with the estimate
        validators_disagreeing(v1, v2, estimate, messages) == 
            /\ Cardinality(latest_message(v1, messages)) = 1
            /\ LET v1_latest_msg == CHOOSE x \in latest_message(v1, messages) : TRUE
                IN Cardinality(latest_message(v2, msg_justification[v1_latest_msg])) = 1
                /\ LET v2_latest_msg == CHOOSE x \in latest_message(v2, msg_justification[v1_latest_msg]) : TRUE
                    IN \E m \in messages: v2_latest_msg \in dependencies(m)
                        /\ estimate /= msg_estimate[m]
 
 
\*      An "e-clique" is a group of non-byzantine nodes in a set of observed messages such that :
\*        - they mutually see each other agreeing with estimate in messages
\*        - they mutually cannot see each other disagreeing with estimate in messages
        e_clique(estimate, messages) == {
            ss \in SUBSET(validators) : 
                /\ \A v1 \in ss:
                    /\ \A v2 \in ss:
                       \/ v1 = v2
                       \/ /\ validators_agreeing(v1, v2, estimate, messages) 
                          /\ ~validators_disagreeing(v1, v2, estimate, messages)
            }
\*      Finds the existence of an e-clique
        e_clique_estimate_safety(estimate, messages) == 
            /\ \E ss \in e_clique(estimate, messages):
                /\ 2 * Sum({validator_weights[v] : v \in ss}) > Sum({validator_weights[v] : v \in validators}) + byzantine_threshold - fault_weight(messages)
            
\*      Gets the set of messges received by a particular valiadtor
        validator_received_msg(validator) == 
          (all_msg \ equivocating_msg) \union
          {x \in equivocating_msg : validator \in equiv_msg_receivers[x]}
            
\*      Returns a subset of received messages for an equivocating validator to generate potentially equivocating messages 
        get_equivocation_subset_msg(validator) == CHOOSE x \in SUBSET(validator_received_msg(validator)) : TRUE
        
\*      Returns a subset of validators receiving a particular equivocating message
        get_equiv_receivers(validator) == CHOOSE x \in (SUBSET(validators \ {validator})) : x /= {}
        
\*      A temporal property checking that finality can eventually be reached in a binary consensus protocol
        check_safety_with_oracle ==
          LET v == CHOOSE v \in (validators \ byzantine_fault_nodes) : TRUE
          IN  <>(e_clique_estimate_safety(0, validator_received_msg(v)) \/ e_clique_estimate_safety(1, validator_received_msg(v)))
    
    end define;
\*  A message from a non-byzantine validator is received by all the validators 
    macro make_message(validator, estimate, justification) begin
      equiv_msg_receivers := Append(equiv_msg_receivers, {});
      msg_sender := Append(msg_sender, validator);
      msg_estimate := Append(msg_estimate, estimate);
      msg_justification := Append(msg_justification, justification);
      all_msg := all_msg \union {cur_msg_id};
      cur_msg_id := cur_msg_id + 1;
    end macro;
    
\*  A validator sends an initial message without receiving information from other validators.
\*  An initial message is only justified by itself.
    macro init_validator(validator) begin
      make_message(validator, validators_initial_values[validator], {cur_msg_id});
      validator_init_done[validator] := 1;
    end macro;
    
\*  An equivocating validator takes different subsets of its received messages to generate
\*  different estimates and sends the different messages to different subsets of validators. 
    macro make_equivocating_messages(validator) begin
      equiv_msg_receivers := Append(equiv_msg_receivers, get_equiv_receivers(validator));
      cur_subset := get_equivocation_subset_msg(validator);
      equivocating_msg := equivocating_msg \union {cur_msg_id};
      msg_sender := Append(msg_sender, validator);
      msg_estimate := Append(msg_estimate, binary_estimator(cur_subset));
      msg_justification := Append(msg_justification, cur_subset);
      all_msg := all_msg \union {cur_msg_id};
      cur_msg_id := cur_msg_id + 1;
    end macro;
    
\*  A general macro for sending messages.
\*  Non-equivocating and equivocating validators behave differently.
\*  No honest validator will send the same message multiple times consecutively.
\*  Equivocating validators may send different messages to different subsets of validators consecutively.
    macro send_message(validator) begin
      if (cur_msg_id > 1 /\ msg_sender[cur_msg_id - 1] /= validator) \/ (validator \in byzantine_fault_nodes) then
          if validator \notin byzantine_fault_nodes then
               make_message(validator, binary_estimator(validator_received_msg(validator)), validator_received_msg(validator));
          else
               make_equivocating_messages(validator);
          end if;
      else
          skip;
      end if;
    end macro;
    
\*  Each process is an individual validator.
\*  Validators send messages in random orders.
\*  Validators keep on sending messages until the maximum limit is reached.
    fair process v \in validators begin
        Validate:
        while cur_msg_id <= message_ids do 
            if validator_init_done[self] = 0 /\ self \notin byzantine_fault_nodes then
                init_validator(self);
            else
                send_message(self);
            end if;
        end while;
    end process;
        
end algorithm; *)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue

VARIABLES
  all_msg,
  equivocating_msg,
  msg_sender,
  msg_estimate, 
  msg_justification,
  cur_msg_id,
  validator_init_done, 
  equiv_msg_receivers,
  cur_subset,
  pc

(* define statement *)
dependencies(message) ==
  LET
    RECURSIVE dep(_)
      dep(msg) ==
        IF Cardinality(msg_justification[msg]) = 1 /\ msg \in msg_justification[msg]
        THEN {msg}
        ELSE UNION{dep(msg2) : msg2 \in msg_justification[msg]}
  IN dep(message)

dep_set(messages) ==
  messages \union UNION{dependencies(m) : m \in messages}

latest_message(validator, messages) ==
  {msg \in messages:
     /\ msg_sender[msg] = validator
     /\ ~\E msg2 \in messages:
         /\ msg_sender[msg2] = validator
         /\ msg # msg2
         /\ msg \in dependencies(msg2)
  }

Pick(S) == CHOOSE s \in S : TRUE
  RECURSIVE SetReduce(_, _, _)
    SetReduce(Op(_, _), S, value) ==
      IF S = {} THEN value
      ELSE LET s == Pick(S) IN SetReduce(Op, S \ {s}, Op(s, value))

Sum(S) == LET _op(a, b) == a + b IN SetReduce(_op, S, 0)

score(estimate, messages) ==
  LET ss ==
      {v \in validators:
         /\ Cardinality(latest_message(v, messages)) = 1
         /\ \E m \in latest_message(v, messages):
            msg_estimate[m] = estimate}
      ss2 == {validator_weights[v] : v \in ss}
  IN  Sum(ss2)

binary_estimator(messages) ==
  IF score(1, messages) > score(0, messages)
  THEN 1
  ELSE 0

equivocation(m1, m2) ==
    /\ m1 # m2
    /\ msg_sender[m1] = msg_sender[m2]
    /\ m1 \notin dependencies(m2)
    /\ m2 \notin dependencies(m1)

faulty_node(validator, messages) ==
  /\ \E m1 \in dep_set(messages):
     /\ \E m2 \in dep_set(messages):
        /\ validator = msg_sender[m1]
        /\ equivocation(m1, m2)

faulty_nodes(messages) ==
  {v \in validators : faulty_node(v, messages)}


fault_weight(messages) ==
  LET byz == faulty_nodes(messages)
  IN Sum({validator_weights[v] : v \in byz})


protocol_states(messages, t) == {ss \in SUBSET(messages) : fault_weight(ss) < t}
protocol_executions(state1, state2) == state1 \subseteq state2


validators_agreeing(v1, v2, estimate, messages) ==
    /\ Cardinality(latest_message(v1, messages)) = 1
    /\ LET v1_latest_msg == CHOOSE x \in latest_message(v1, messages) : TRUE
        IN Cardinality(latest_message(v2, msg_justification[v1_latest_msg])) = 1
        /\ LET v2_latest_msg == CHOOSE x \in latest_message(v2, msg_justification[v1_latest_msg]) : TRUE
            IN estimate = msg_estimate[v2_latest_msg]


validators_disagreeing(v1, v2, estimate, messages) ==
    /\ Cardinality(latest_message(v1, messages)) = 1
    /\ LET v1_latest_msg == CHOOSE x \in latest_message(v1, messages) : TRUE
        IN Cardinality(latest_message(v2, msg_justification[v1_latest_msg])) = 1
        /\ LET v2_latest_msg == CHOOSE x \in latest_message(v2, msg_justification[v1_latest_msg]) : TRUE
            IN \E m \in messages: v2_latest_msg \in dependencies(m)
                /\ estimate /= msg_estimate[m]


e_clique(estimate, messages) == {
    ss \in SUBSET(validators) :
        /\ \A v1 \in ss:
            /\ \A v2 \in ss:
                IF v1 = v2
                THEN TRUE
                ELSE
                    /\ validators_agreeing(v1, v2, estimate, messages)
                    /\ ~validators_disagreeing(v1, v2, estimate, messages)
    }


e_clique_estimate_safety(estimate, messages) ==
    /\ \E ss \in e_clique(estimate, messages):
        /\ 2 * Sum({validator_weights[v] : v \in ss}) > Sum({validator_weights[v] : v \in validators}) + byzantine_threshold - fault_weight(messages)


validator_received_msg(validator) ==
    (all_msg \ equivocating_msg) \union
    {x \in equivocating_msg : validator \in equiv_msg_receivers[x]}


get_equivocation_subset_msg(validator) == CHOOSE x \in SUBSET(validator_received_msg(validator)) : TRUE


get_equiv_receivers(validator) == CHOOSE x \in (SUBSET(validators \ {validator})) : x /= {}


check_safety_with_oracle ==
    LET v == CHOOSE v \in (validators \ byzantine_fault_nodes) : TRUE
    IN <>(e_clique_estimate_safety(0, validator_received_msg(v)) \/ e_clique_estimate_safety(1, validator_received_msg(v)))


vars == << all_msg, equivocating_msg, msg_sender, msg_estimate, 
           msg_justification, cur_msg_id, validator_init_done, 
           equiv_msg_receivers, cur_subset, pc >>

ProcSet == (validators)

Init == (* Global variables *)
        /\ all_msg = {}
        /\ equivocating_msg = {}
        /\ msg_sender = <<>>
        /\ msg_estimate = <<>>
        /\ msg_justification = <<>>
        /\ cur_msg_id = 1
        /\ validator_init_done = <<0, 0, 0, 0, 0, 0, 0, 0, 0, 0>>
        /\ equiv_msg_receivers = <<>>
        /\ cur_subset = defaultInitValue
        /\ pc = [self \in ProcSet |-> "Validate"]

Validate(self) == /\ pc[self] = "Validate"
                  /\ IF cur_msg_id <= message_ids
                     THEN /\ IF validator_init_done[self] = 0 /\ self \notin byzantine_fault_nodes
                             THEN 
                               /\ equiv_msg_receivers' = Append(equiv_msg_receivers, {})
                               /\ msg_sender' = Append(msg_sender, self)
                               /\ msg_estimate' = Append(msg_estimate, (validators_initial_values[self]))
                               /\ msg_justification' = Append(msg_justification, ({cur_msg_id}))
                               /\ all_msg' = (all_msg \union {cur_msg_id})
                               /\ cur_msg_id' = cur_msg_id + 1
                               /\ validator_init_done' = [validator_init_done EXCEPT ![self] = 1]
                               /\ UNCHANGED << equivocating_msg,cur_subset >>
                             ELSE
                               /\ IF (cur_msg_id > 1 /\ msg_sender[cur_msg_id - 1] /= self) \/ (self \in byzantine_fault_nodes)
                                  THEN /\ IF self \notin byzantine_fault_nodes
                                          THEN
                                            /\ equiv_msg_receivers' = Append(equiv_msg_receivers, {})
                                            /\ msg_sender' = Append(msg_sender, self)
                                            /\ msg_estimate' = Append(msg_estimate, (binary_estimator(validator_received_msg(self))))
                                            /\ msg_justification' = Append(msg_justification, (validator_received_msg(self)))
                                            /\ all_msg' = (all_msg \union {cur_msg_id})
                                            /\ cur_msg_id' = cur_msg_id + 1
                                            /\ UNCHANGED << equivocating_msg,cur_subset >>
                                          ELSE
                                            /\ equiv_msg_receivers' = Append(equiv_msg_receivers, get_equiv_receivers(self))
                                            /\ cur_subset' = get_equivocation_subset_msg(self)
                                            /\ equivocating_msg' = (equivocating_msg \union {cur_msg_id})
                                            /\ msg_sender' = Append(msg_sender, self)
                                            /\ msg_estimate' = Append(msg_estimate, binary_estimator(cur_subset'))
                                            /\ msg_justification' = Append(msg_justification, cur_subset')
                                            /\ all_msg' = (all_msg \union {cur_msg_id})
                                            /\ cur_msg_id' = cur_msg_id + 1
                                  ELSE
                                    /\ TRUE
                                    /\ UNCHANGED << all_msg, 
                                                    equivocating_msg, 
                                                    msg_sender, 
                                                    msg_estimate, 
                                                    msg_justification, 
                                                    cur_msg_id, 
                                                    equiv_msg_receivers, 
                                                    cur_subset >>
                                        /\ UNCHANGED validator_init_done
                             /\ pc' = [pc EXCEPT ![self] = "Validate"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                             /\ UNCHANGED << all_msg, equivocating_msg, 
                                             msg_sender, msg_estimate, 
                                             msg_justification, cur_msg_id, 
                                             validator_init_done, 
                                             equiv_msg_receivers, cur_subset >>

v(self) == Validate(self)

Next == (\E self \in validators: v(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init 
        /\ [][Next]_vars
        /\ \A self \in validators : WF_vars(v(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Dec 01 10:51:30 EST 2019 by isaac
\* Created Tue Nov 19 11:24:16 EST 2019 by isaac
