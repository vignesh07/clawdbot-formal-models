------------------------------ MODULE RoutingIsolationHarness_BadAlwaysMain ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* BUG: DM session key always collapses to "main" regardless of dmScope.
******************************************************************************)

CONSTANTS
  Peers,
  DmScope,
  IdentityLinks

ASSUME
  /\ Peers /= {}
  /\ DmScope \in {"main","per-peer"}
  /\ IdentityLinks \subseteq (Peers \X Peers)

Linked(a,b) == <<a,b>> \in IdentityLinks \/ <<b,a>> \in IdentityLinks \/ a=b

\* BUG: always main
SessionKey(_p) == "main"

Inv_NoUnlinkedCollapse ==
  DmScope = "per-peer" =>
    \A p1 \in Peers: \A p2 \in Peers:
      (~Linked(p1,p2)) => (SessionKey(p1) /= SessionKey(p2))

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
