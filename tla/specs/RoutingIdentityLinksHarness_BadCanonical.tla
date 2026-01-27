------------------------------ MODULE RoutingIdentityLinksHarness_BadCanonical ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* BUG: canonicalization collapses peers too aggressively.
*
* Same inputs (Peers + LinkGroups), but CanonicalPeer ignores LinkGroups and
* returns a constant (1), collapsing unrelated peers.
******************************************************************************)

CONSTANTS
  Peers,
  LinkGroups

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

\* BUG: ignores groups
CanonicalPeer(_p) == 1

SessionKey(p) == <<"dm", CanonicalPeer(p)>>

Inv_NoUnlinkedCollapse ==
  PartitionOk /\
  (\A p1 \in Peers: \A p2 \in Peers:
     (~InSameGroup(p1,p2)) => (SessionKey(p1) /= SessionKey(p2)))

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
