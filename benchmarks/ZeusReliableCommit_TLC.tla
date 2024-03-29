------------------------------- MODULE ZeusReliableCommit_TLC -------------------------------

EXTENDS ZeusReliableCommit, TLC, Randomization, FiniteSets

TypeOKRandom ==  \* The type correctness invariant
    /\  rMsgsINV            \in RandomSetOfSubsets(4, 1, RMessageINV)
    /\  rMsgsVAL            \in RandomSetOfSubsets(4, 1, RMessageVAL)
    /\  rMsgsACK            \in RandomSetOfSubsets(4, 1, RMessageACK)
    /\  rAliveNodes     \in SUBSET R_NODES
    /\  rKeyRcvedACKs \in [R_NODES -> SUBSET R_NODES]
    /\  \A n \in R_NODES: rKeyRcvedACKs[n] \subseteq (R_NODES \ {n})
    /\  rNodeEpochID    \in [R_NODES -> 0..R_MAX_EPOCH]
    /\  rKeyLastWriter  \in [R_NODES -> R_NODES]
    /\  rKeyVersion     \in [R_NODES -> 0..R_MAX_VERSION]
    /\  rKeySharers     \in [R_NODES -> {"owner", "reader", "non-sharer"}]
    /\  rKeyState       \in [R_NODES -> {"valid", "invalid", "write", "replay"}]
    /\ rEpochID \in 0..(Cardinality(R_NODES) - 1)

    
    \* /\ msgsINV \in RandomSetOfSubsets(4, 2, INVMessage) \* {INVMessageRandom(0),INVMessageRandom(0)}
    \* /\ msgsVAL \in RandomSetOfSubsets(4, 2, VALMessage) \* SUBSET {VALMessageRandom(0),VALMessageRandom(0)}
    \* /\ msgsACK \in RandomSetOfSubsets(4, 2, ACKMessage) \* SUBSET {ACKMessageRandom(0),ACKMessageRandom(0)}

=============================================================================