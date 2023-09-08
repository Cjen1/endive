--------------------------------- MODULE AsyncRaft ---------------------------------
(* NOTES 

Spec of Raft with message passing.

Author: Jack Vanlightly
This specification is based on (with heavy modification) the original Raft specification 
by Diego Ongaro which can be found here: https://github.com/ongardie/raft.tla 

This is a model checking optimized fork of original spec.

- Summary of changes:
    - updated message helpers:
        - prevent resending the same message multiple times (unless explicity via the duplicate action)
        - can only receive a message that hasn't been delivered yet
    - optimized for model checking (reduction in state space)
        - removed history variables (using simple invariants instead)
        - decomposed "receive" into separate actions
        - compressed multi-step append_entries_req processing into one.
        - compressed timeout and requestvote into single action
        - server directly votes for itself in an election (it doesn't send itself a vote request)
    - fixed some bugs
        - adding the same value over and over again
        - allowing actions to remain enabled producing odd results
    
Notes on action enablement.
 - Send is only enabled if the mesage has not been previously sent.
   This is leveraged to disable actions once executed, such as sending a specific 
   AppendEntrieRequest. It won't be sent again, so no need for extra variables to track that. 

Original source: https://github.com/Vanlightly/raft-tlaplus/blob/main/specifications/standard-raft/Raft.tla
*)

EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, 
          RequestVoteResponse,
          AppendEntriesRequest, 
          AppendEntriesResponse

\* Used for filtering messages under different circumstance
CONSTANTS EqualTerm, LessOrEqualTerm

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
VARIABLE messages

VARIABLE requestVoteMsgs

----
\* Auxilliary variables (used for state-space control, invariants etc)

\* The server's term number.
VARIABLE currentTerm

\* The server's state (Follower, Candidate, or Leader).
VARIABLE state

\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log

\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex


\* The following variables are used only on candidates:

\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted


\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex

\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex


serverVars == <<currentTerm, state, votedFor>>
logVars == <<log, commitIndex>>
candidateVars == <<votesGranted>>
leaderVars == <<nextIndex, matchIndex>>

\* End of per server variables.-

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, currentTerm, state, votedFor, votesGranted, nextIndex, matchIndex, log, commitIndex>>

view == <<messages, serverVars, candidateVars, leaderVars, logVars >>
Symmetry == Permutations(Server)



\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

\* Send the message whether it already exists or not.
SendNoRestriction(m) ==
    IF m \in DOMAIN messages
    THEN messages' = [messages EXCEPT ![m] = @ + 1]
    ELSE messages' = messages @@ (m :> 1)
    
\* Will only send the message if it hasn't been sent before.
\* Basically disables the parent action once sent.    
SendOnce(m) ==
    /\ m \notin DOMAIN messages
    /\ messages' = messages @@ (m :> 1)    

\* Add a message to the bag of messages. 
\* Note 1: to prevent infinite cycles, empty 
\* AppendEntriesRequest messages can only be sent once.
\* Note 2: a message can only match an existing message
\* if it is identical (all fields).
Send(m) ==
    IF /\ m.mtype = AppendEntriesRequest
       /\ m.mentries = <<>>
    THEN SendOnce(m)
    ELSE SendNoRestriction(m)

\* Will only send the messages if it hasn't done so before
\* Basically disables the parent action once sent.
SendMultipleOnce(msgs) ==
    /\ \A m \in msgs : m \notin DOMAIN messages
    /\ messages' = messages @@ [msg \in msgs |-> 1]    

\* Explicit duplicate operator for when we purposefully want message duplication
Duplicate(m) == 
    /\ m \in DOMAIN messages
    /\ messages' = [messages EXCEPT ![m] = @ + 1]

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) ==
    /\ m \in DOMAIN messages
    /\ messages[m] > 0 \* message must exist
    /\ messages' = [messages EXCEPT ![m] = @ - 1]

\* Combination of Send and Discard
Reply(response, request) ==
    /\ messages[request] > 0 \* request must exist
    /\ \/ /\ response \notin DOMAIN messages \* response does not exist, so add it
          /\ messages' = [messages EXCEPT ![request] = @ - 1] @@ (response :> 1)
       \/ /\ response \in DOMAIN messages \* response was sent previously, so increment delivery counter
          /\ messages' = [messages EXCEPT ![request] = @ - 1,
                                          ![response] = @ + 1]

\* The message is of the type and has a matching term.
\* Messages with a higher term are handled by the
\* action UpdateTerm
ReceivableRequestVoteMessage(m, mtype, term_match) ==
    \* /\ requestVoteMsgs # {}
    /\ m.mtype = mtype
    /\ \/ /\ term_match = EqualTerm
          /\ m.mterm = currentTerm[m.mdest]
       \/ /\ term_match = LessOrEqualTerm
          /\ m.mterm <= currentTerm[m.mdest]

\* The message is of the type and has a matching term.
\* Messages with a higher term are handled by the
\* action UpdateTerm
ReceivableMessage(m, mtype, term_match) ==
    /\ messages[m] > 0
    /\ m.mtype = mtype
    /\ \/ /\ term_match = EqualTerm
          /\ m.mterm = currentTerm[m.mdest]
       \/ /\ term_match = LessOrEqualTerm
          /\ m.mterm <= currentTerm[m.mdest]

\* Return the minimum value from a set, or undefined if the set is empty.
\* Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
\* Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Define initial values for all variables

InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log             = [i \in Server |-> << >>]
               /\ commitIndex     = [i \in Server |-> 0]

Init == 
    /\ messages = [m \in {} |-> 0]
    /\ requestVoteMsgs = {}
    /\ currentTerm = [i \in Server |-> 1]
    /\ state       = [i \in Server |-> Follower]
    /\ votedFor    = [i \in Server |-> Nil]
    /\ votesGranted = [i \in Server |-> {}]
    /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]        
    /\ log             = [i \in Server |-> << >>]
    /\ commitIndex     = [i \in Server |-> 0]
    
----
\* Define state transitions

\* ACTION: Restart -------------------------------------
\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor and log.
Restart(i) ==
    /\ state'           = [state EXCEPT ![i] = Follower]
    /\ votesGranted'    = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'       = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'      = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'     = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, requestVoteMsgs>>

\* ACTION: RequestVote
\* Combined Timeout and RequestVote of the original spec to reduce
\* state space.
\* Server i times out and starts a new election. 
\* Sends a RequestVote request to all peers but not itself.
RequestVote(i) ==
    /\ state[i] \in {Follower, Candidate}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ requestVoteMsgs' = requestVoteMsgs \cup
           {[mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i] + 1,
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j] : j \in Server \ {i}}
    /\ UNCHANGED <<leaderVars, logVars, messages>>

\* ACTION: AppendEntries ----------------------------------------
\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex]
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN 
          /\ Send([mtype          |-> AppendEntriesRequest,
                   mterm          |-> currentTerm[i],
                   mprevLogIndex  |-> prevLogIndex,
                   mprevLogTerm   |-> prevLogTerm,
                   mentries       |-> entries,
                   mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                   msource        |-> i,
                   mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, nextIndex, matchIndex, logVars, requestVoteMsgs>>

\* ACTION: BecomeLeader -------------------------------------------
\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, requestVoteMsgs>>

\* ACTION: ClientRequest ----------------------------------
\* Leader i receives a client request to add v to the log.
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ LET newLog == Append(log[i], currentTerm[i])
       IN  /\ log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex, requestVoteMsgs>>

\* ACTION: AdvanceCommitIndex ---------------------------------
\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         /\ matchIndex[i][k] >= index }
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) : 
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)] = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN 
          /\ commitIndex[i] < newCommitIndex \* only enabled if it actually advances
          /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, requestVoteMsgs>>

\* ACTION: UpdateTerm
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm ==
    \E m \in DOMAIN messages :
        /\ m.mterm > currentTerm[m.mdest]
        /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
        /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
        /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
           \* messages is unchanged so m can be processed further.
        /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, requestVoteMsgs>>

\* ACTION: HandleRequestVoteRequest ------------------------------
\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest ==
    \E m \in requestVoteMsgs :
        /\ ReceivableRequestVoteMessage(m, RequestVoteRequest, LessOrEqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                        \/ /\ m.mlastLogTerm = LastTerm(log[i])
                           /\ m.mlastLogIndex >= Len(log[i])
               grant == /\ m.mterm = currentTerm[i]
                        /\ logOk
                        /\ votedFor[i] \in {Nil, j}
            IN /\ m.mterm <= currentTerm[i]
               /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
                  \/ ~grant /\ UNCHANGED votedFor
               /\ requestVoteMsgs' = requestVoteMsgs \cup{[
                         mtype        |-> RequestVoteResponse,
                         mterm        |-> currentTerm[i],
                         mvoteGranted |-> grant,
                         msource      |-> i,
                         mdest        |-> j]}
               /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, messages>>

\* ACTION: HandleRequestVoteResponse --------------------------------
\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse ==
    \E m \in requestVoteMsgs :
        \* This tallies votes even when the current state is not Candidate, but
        \* they won't be looked at, so it doesn't matter.
        /\ ReceivableRequestVoteMessage(m, RequestVoteResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ \/ /\ m.mvoteGranted
                    /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                              votesGranted[i] \cup {j}]
                 \/ /\ ~m.mvoteGranted
                    /\ UNCHANGED <<votesGranted>>
              /\ Discard(m)
              /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, requestVoteMsgs>>

\* ACTION: RejectAppendEntriesRequest -------------------
\* Either the term of the message is stale or the message
\* entry is too high (beyond the last log entry + 1)
LogOk(i, m) ==
    \/ m.mprevLogIndex = 0
    \/ /\ m.mprevLogIndex > 0
       /\ m.mprevLogIndex <= Len(log[i])
       /\ m.mprevLogTerm = log[i][m.mprevLogIndex]

RejectAppendEntriesRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesRequest, LessOrEqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == LogOk(i, m)
           IN  /\ \/ m.mterm < currentTerm[i]
                  \/ /\ m.mterm = currentTerm[i]
                     /\ state[i] = Follower
                     /\ \lnot logOk
               /\ Reply([mtype           |-> AppendEntriesResponse,
                         mterm           |-> currentTerm[i],
                         msuccess        |-> FALSE,
                         mmatchIndex     |-> 0,
                         msource         |-> i,
                         mdest           |-> j],
                         m)
               /\ UNCHANGED <<state, candidateVars, leaderVars, serverVars, logVars, requestVoteMsgs>>

\* ACTION: AcceptAppendEntriesRequest ------------------
\* The original spec had to three sub actions, this version is compressed.
\* In one step it can:
\* - truncate the log
\* - append an entry to the log
\* - respond to the leader         
CanAppend(m, i) ==
    /\ m.mentries /= << >>
    /\ Len(log[i]) = m.mprevLogIndex
    
\* truncate in two cases:
\* - the last log entry index is >= than the entry being received
\* - this is an empty RPC and the last log entry index is > than the previous log entry received
NeedsTruncation(m, i, index) ==
   \/ /\ m.mentries /= <<>>
      /\ Len(log[i]) >= index
   \/ /\ m.mentries = <<>>
      /\ Len(log[i]) > m.mprevLogIndex

TruncateLog(m, i) ==
    [index \in 1..m.mprevLogIndex |-> log[i][index]]

AcceptAppendEntriesRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesRequest, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == LogOk(i, m)
               index == m.mprevLogIndex + 1
           IN 
              /\ state[i] \in { Follower, Candidate }
              /\ logOk
              /\ LET new_log == 
                    IF CanAppend(m, i) THEN [log EXCEPT ![i] = Append(log[i], m.mentries[1])] ELSE
                    IF NeedsTruncation(m, i , index) /\ m.mentries # <<>> THEN [log EXCEPT ![i] = Append(TruncateLog(m, i), m.mentries[1])] ELSE
                    IF NeedsTruncation(m, i , index) /\ m.mentries = <<>> THEN [log EXCEPT ![i] = TruncateLog(m, i)] ELSE
                    log 
                 IN
                    /\ state' = [state EXCEPT ![i] = Follower]
                    /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                              m.mcommitIndex]
                    /\ log' = new_log
                    /\ Reply([mtype           |-> AppendEntriesResponse,
                              mterm           |-> currentTerm[i],
                              msuccess        |-> TRUE,
                              mmatchIndex     |-> m.mprevLogIndex +
                                                    Len(m.mentries),
                              msource         |-> i,
                              mdest           |-> j],
                              m)
                    /\ UNCHANGED <<candidateVars, leaderVars, votedFor, currentTerm, requestVoteMsgs>>
       
\* ACTION: HandleAppendEntriesResponse
\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ \/ /\ m.msuccess \* successful
                    /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                 \/ /\ \lnot m.msuccess \* not successful
                    /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                                         Max({nextIndex[i][j] - 1, 1})]
                    /\ UNCHANGED <<matchIndex>>
              /\ Discard(m)
              /\ UNCHANGED <<serverVars, candidateVars, logVars, requestVoteMsgs>>

RestartAction == TRUE /\ \E i \in Server : Restart(i)
RequestVoteAction == TRUE /\ \E i \in Server : RequestVote(i)
BecomeLeaderAction == TRUE /\ \E i \in Server : BecomeLeader(i)
ClientRequestAction == TRUE /\ \E i \in Server : ClientRequest(i)
AdvanceCommitIndexAction == TRUE /\ \E i \in Server : AdvanceCommitIndex(i)
AppendEntriesAction == TRUE /\ \E i,j \in Server : AppendEntries(i, j)
UpdateTermAction == UpdateTerm
HandleRequestVoteRequestAction == HandleRequestVoteRequest
HandleRequestVoteResponseAction == HandleRequestVoteResponse
RejectAppendEntriesRequestAction == RejectAppendEntriesRequest
AcceptAppendEntriesRequestAction == AcceptAppendEntriesRequest
HandleAppendEntriesResponseAction == HandleAppendEntriesResponse

\* Defines how the variables may transition.
Next == 
    \/ RestartAction
    \/ RequestVoteAction
    \/ BecomeLeaderAction
    \/ ClientRequestAction
    \/ AdvanceCommitIndexAction
    \/ AppendEntriesAction
    \/ UpdateTermAction
    \/ HandleRequestVoteRequestAction
    \/ HandleRequestVoteResponseAction
    \/ RejectAppendEntriesRequestAction
    \/ AcceptAppendEntriesRequestAction
    \/ HandleAppendEntriesResponseAction

NextUnchanged == UNCHANGED vars

CTICost == 0


CONSTANT MaxTerm
CONSTANT MaxLogLen

Terms == 0..MaxTerm
LogIndices == 1..MaxLogLen
LogIndicesWithZero == 0..MaxLogLen

SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

\* RequestVoteRequestType == [
\*     mtype         : {RequestVoteRequest},
\*     mterm         : Terms,
\*     mlastLogTerm  : Terms,
\*     mlastLogIndex : LogIndicesWithZero,
\*     msource       : Server,
\*     mdest         : Server
\* ]

RequestVoteRequestTypeOp(T) == [
    mtype         : {RequestVoteRequest},
    mterm         : T,
    mlastLogTerm  : Terms,
    mlastLogIndex : LogIndicesWithZero,
    msource       : Server,
    mdest         : Server
]


\* RequestVoteResponseType == [
\*     mtype        : {RequestVoteResponse},
\*     mterm        : Terms,
\*     mvoteGranted : BOOLEAN,
\*     msource      : Server,
\*     mdest        : Server
\* ]

RequestVoteResponseTypeOp(T) == [
    mtype        : {RequestVoteResponse},
    mterm        : T,
    mvoteGranted : BOOLEAN,
    msource      : Server,
    mdest        : Server
]


\* Set of all subsets of a set of size <= k.
kOrSmallerSubset(k, S) == UNION {(kSubset(n, S)) : n \in 0..k}


\* Work around size limitations of TLC subset computations.

RequestVoteResponseTypeSampled == UNION {   
    kOrSmallerSubset(2, RequestVoteResponseTypeOp({t})) : t \in Terms 
}

RequestVoteRequestTypeSampled == UNION {   
    kOrSmallerSubset(2, RequestVoteRequestTypeOp({t})) : t \in Terms 
}

\* TODO: Fill in type-correctness.
TypeOK == 
    /\ messages \in {[m \in {} |-> 0]}
    /\ requestVoteMsgs \in (RequestVoteResponseTypeSampled \cup RequestVoteRequestTypeSampled)
    /\ currentTerm \in [Server -> Terms]
    /\ state       \in [Server -> {Leader, Follower, Candidate}]
    /\ votedFor    \in [Server -> {Nil} \cup (SUBSET Server)]
    /\ votesGranted \in [Server -> (SUBSET Server)]
    /\ nextIndex  \in [Server -> [Server -> LogIndices]]
    /\ matchIndex \in [Server -> [Server -> LogIndicesWithZero]]        
    /\ log             \in [Server -> BoundedSeq(Terms, MaxLogLen)]
    /\ commitIndex     \in [Server -> LogIndicesWithZero]


Spec == Init /\ [][Next]_vars

----

\* INVARIANTS -------------------------

H_QuorumsSafeAtTerms ==
    \A s \in Server : state[s] = Leader => 
        \E Q \in Quorum : \A t \in Q : currentTerm[t] >= currentTerm[s]

\* If two nodes are in the same term, then their votes granted
\* sets cannot have intersecting voters.
H_CandidateVotesGrantedInTermAreUnique ==
    \A s,t \in Server :
        (/\ s # t
         /\ currentTerm[s] = currentTerm[t]) =>
            (votesGranted[s] \cap votesGranted[t]) = {}

\* If a node has garnered votes in a term as candidate, there must
\* be no other leader in that term in existence.
H_CandidateWithVotesGrantedInTermImplyNoOtherLeader ==
    \A s,t \in Server :
        (/\ s # t
         /\ votesGranted[s] \in Quorum
         /\ currentTerm[s] = currentTerm[t]) =>
            state[t] # Leader

H_OnePrimaryPerTerm == 
    \A s,t \in Server : 
        (s # t /\ state[s] = Leader /\ state[t] = Leader) => currentTerm[s] # currentTerm[t]

H_LogTermsMonotonic == 
    \A s \in Server : \A i,j \in DOMAIN log[s] : (i <= j) => (log[s][i] <= log[s][j])
    

MinCommitIndex(s1, s2) ==
    /\ PrintT(commitIndex)
    /\ IF commitIndex[s1] < commitIndex[s2]
        THEN commitIndex[s1]
        ELSE commitIndex[s2]

\* INV: NoLogDivergence
\* The log index is consistent across all servers (on those
\* servers whose commitIndex is equal or higher than the index).
NoLogDivergence ==
    \A s1, s2 \in Server :
        (s1 # s2) =>
        (LET lowest_common_ci == MinCommitIndex(s1, s2) IN
         IF lowest_common_ci > 0
            THEN \A index \in 1..lowest_common_ci : 
                    /\ index \in DOMAIN log[s1]
                    /\ index \in DOMAIN log[s2]
                    /\ log[s1][index] = log[s2][index]
            ELSE TRUE)

\* INV: Used in debugging
TestInv ==
    TRUE

\* INV: LeaderHasAllAckedValues
\* A non-stale leader cannot be missing an acknowledged value
\* LeaderHasAllAckedValues ==
\*     \* for every acknowledged value
\*     \A v \in Value :
\*         IF acked[v] = TRUE
\*         THEN
\*             \* there does not exist a server that
\*             ~\E i \in Server :
\*                 \* is a leader
\*                 /\ state[i] = Leader
\*                 \* and which is the newest leader (aka not stale)
\*                 /\ ~\E l \in Server : 
\*                     /\ l # i
\*                     /\ currentTerm[l] > currentTerm[i]
\*                 \* and that is missing the value
\*                 /\ ~\E index \in DOMAIN log[i] :
\*                     log[i][index].value = v
\*         ELSE TRUE

\* INV: CommittedEntriesReachMajority
\* There cannot be a committed entry that is not at majority quorum
\* Don't use this invariant when allowing data loss on a server.
CommittedEntriesReachMajority ==
    IF \E i \in Server : state[i] = Leader /\ commitIndex[i] > 0
    THEN \E i \in Server :
           /\ state[i] = Leader
           /\ commitIndex[i] > 0
           /\ \E quorum \in SUBSET Server :
               /\ Cardinality(quorum) = (Cardinality(Server) \div 2) + 1
               /\ i \in quorum
               /\ \A j \in quorum :
                   /\ Len(log[j]) >= commitIndex[i]
                   /\ log[j][commitIndex[i]] = log[i][commitIndex[i]]
    ELSE TRUE

\* Model checking stuff.

StateConstraint == 
    /\ \A s \in Server : currentTerm[s] <= MaxTerm
    /\ \A s \in Server : Len(log[s]) <= MaxLogLen

===============================================================================