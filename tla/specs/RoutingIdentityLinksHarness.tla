------------------------------ MODULE RoutingIdentityLinksHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* RoutingIdentityLinksHarness.tla
*
* R3++: identityLinks semantics (DM session collapsing).
*
* We represent identity links as explicit groups (sets of peer ids).
* To keep TLC configs simple, we define canonicalization from the groups
* deterministically: CanonicalPeer(p) is the minimum element of p’s group.
*
* Assumptions:
*  - Peers is a set of Naturals (ids).
*  - LinkGroups is a partition of Peers (covers all peers; disjoint).
*
* Property:
*  - Two peers collapse (share session key) iff they are in the same group.
******************************************************************************)

CONSTANTS
  Peers,        \* SUBSET Nat
  LinkGroups    \* SUBSET (SUBSET Peers)

ASSUME
  /\ Peers /= {}
  /\ Peers \subseteq Nat
  /\ LinkGroups \subseteq SUBSET Peers
  /\ \A g \in LinkGroups: g /= {} /\ g \subseteq Peers

InSameGroup(a,b) == \E g \in LinkGroups: a \in g /\ b \in g

PartitionOk ==
  /\ \A p \in Peers: \E g \in LinkGroups: p \in g
  /\ \A g1 \in LinkGroups: \A g2 \in LinkGroups:
       (g1 /= g2) => (g1 \cap g2 = {})

GroupOf(p) == CHOOSE g \in LinkGroups: p \in g

MinOf(S) == CHOOSE m \in S: \A x \in S: m <= x

CanonicalPeer(p) == MinOf(GroupOf(p))

SessionKey(p) == <<"dm", CanonicalPeer(p)>>

Inv_NoUnlinkedCollapse ==
  PartitionOk /\
  (\A p1 \in Peers: \A p2 \in Peers:
     (~InSameGroup(p1,p2)) => (SessionKey(p1) /= SessionKey(p2)))

\* Trivial behavior for TLC
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
