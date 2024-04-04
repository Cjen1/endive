---- MODULE FastPaxos ----
\*
\* Basic FastPaxos specification using unanimous quorums
\* 

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC, Apalache

CONSTANTS
  \* @typeAlias: rid = Str;
  \* @type: Set($rid);
  Replicas

CONSTANTS
  \* @typeAlias: value = Int;
  \* @type: $value;
  Nil,
  \* @type: Set($value);
  Values 

VARIABLE 
  \* @type: $rid -> Int;
  RepTerm,
  \* @type: $rid -> Int;
  RepVTerm,
  \* @type: $rid -> $value;
  RepVVal

VARIABLE
  \* @type: Set({term : Int, val : $value});
  ProposalMsgs,
  \* @type: Set({rep : $rid, term : Int, vterm : Int, vval : $value});
  StateMsgs

vars == << RepTerm, RepVTerm, RepVVal, ProposalMsgs, StateMsgs>>

Init ==
  /\ RepTerm  = [n \in Replicas |-> 0]
  /\ RepVTerm = [n \in Replicas |-> 0]
  /\ RepVVal  = [n \in Replicas |-> Nil]
  /\ ProposalMsgs = {[term |-> 0, val |-> v] : v \in Values}
  /\ StateMsgs = {}

Vote(r) ==
  \E m \in ProposalMsgs:
  /\ m.term >= RepTerm[r]
  /\ \/ m.term > RepVTerm[r]
     \/ m.term = RepVTerm[r] /\ RepVVal[r] = Nil
  /\ RepTerm' = [RepTerm EXCEPT ![r] = m.term]
  /\ RepVTerm' = [RepVTerm EXCEPT ![r] = m.term]
  /\ RepVVal' = [RepVVal EXCEPT ![r] = m.val]
  /\ UNCHANGED << ProposalMsgs, StateMsgs>>

IncrTerm(r) == 
  /\ RepTerm' = [RepTerm EXCEPT ![r] = RepTerm[r] + 1]
  /\ UNCHANGED << RepVTerm, RepVVal >>
  /\ UNCHANGED << ProposalMsgs, StateMsgs>>

BroadcastState(r) ==
  /\ StateMsgs' = StateMsgs \union { [
       rep |-> r,
       term |-> RepTerm[r],
       vterm |-> RepVTerm[r],
       vval |-> RepVVal[r]] }
  /\ UNCHANGED << RepTerm, RepVTerm, RepVVal, ProposalMsgs >>

Propose ==
  \E t \in {m.term: m \in StateMsgs}:
  \E S \in SUBSET {m \in StateMsgs : m.term = t}:
  \* One replica is sufficient to recover
  /\ \E r \in Replicas: \E m \in S: m.rep = r
  /\ LET max_vterm == ApaFoldSet( 
           LAMBDA a,b: IF a < b THEN b ELSE a,
           -10000,
           {m.vterm: m \in S})
         PossCommitable(v) ==
           \A r \in Replicas:
           \/ \E m \in S: m.rep = r /\ m.vval = v
           \/ ~\E m \in S: m.rep = r
         max_vterm_msgs == {m \in S: m.vterm = max_vterm}
         max_vterm_vals == {m.vval : m \in max_vterm_msgs}
         ChoosableVals == {v \in max_vterm_vals: PossCommitable(v)}
                    
     IN
     \E v \in Values:
     \* For inductive base case
     /\ \A lb \in ChoosableVals: lb = Nil \/ lb = v
     \* For inductive case
     /\ \E lb \in max_vterm_vals: lb = Nil \/ lb = v
     /\ ProposalMsgs' = ProposalMsgs \union {[term|-> t, val |-> v]}
     /\ UNCHANGED << RepTerm, RepVTerm, RepVVal, StateMsgs>>

Next ==
  \/ \E r \in Replicas: \/ IncrTerm(r)
                        \/ Vote(r)
                        \/ BroadcastState(r)
  \/ Propose

\* ====================

CONSTANTS
  \* @type: Int;
  MaxTerm

Terms == 0..MaxTerm

ProposalMsgType == [
  term : Terms,
  val : Values
]

StateMsgType == [
  rep : Replicas,
  term : Terms,
  vterm : Terms,
  vval : Values \union {Nil}
]

TypeOK ==
  /\ ProposalMsgs \in SUBSET ProposalMsgType
  /\ StateMsgs \in SUBSET StateMsgType
  /\ RepTerm \in [Replicas -> Nat]
  /\ RepVTerm \in [Replicas -> Nat]
  /\ RepVVal \in [Replicas -> Values]

Spec == Init /\ [][Next]_vars

CInit ==
  /\ Replicas := {"a", "b", "c", "d"}
  /\ Values := {1,2,3,4}
  /\ Nil := -1
  /\ MaxTerm := 3

Symmetry == Permutations(Replicas)
\* ====================
\* Invariants
\* ====================

StateConstraint ==
  /\ \A r \in Replicas: RepTerm[r] <= MaxTerm
  /\ \A r \in Replicas: RepVTerm[r] <= MaxTerm

Misc ==
  /\ ~ Nil \in Values

Committable(v) ==
  \E t \in {m.vterm: m \in StateMsgs}:
  \A r \in Replicas:
  \E m \in StateMsgs: m.vterm = t /\ m.rep = r /\ m.vval = v

Safety == \A v1, v2 \in {v \in Values : Committable(v)} : v1 = v2

====
