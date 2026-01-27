------------------------------ MODULE RoutingIsolationHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* RoutingIsolationHarness.tla
*
* Roadmap R3: Routing/session-key isolation.
*
* Minimal model of DM session key construction with optional identity linking.
* We model:
*   - a set of peers (senders)
*   - dmScope policy
*   - identityLinks relation that explicitly allows collapsing sessions
*
* Property: distinct peers should map to distinct session keys unless explicitly
* identity-linked.
******************************************************************************)

CONSTANTS
  Peers,
  DmScope,          \* "main" | "per-peer"
  IdentityLinks     \* SUBSET (Peers \X Peers)

ASSUME
  /\ Peers /= {}
  /\ DmScope \in {"main","per-peer"}
  /\ IdentityLinks \subseteq (Peers \X Peers)

\* Symmetric closure of identity links
Linked(a,b) == <<a,b>> \in IdentityLinks \/ <<b,a>> \in IdentityLinks \/ a=b

\* Canonical session key for a peer
\* - main scope collapses all DMs into one session
\* - per-peer scope gives each peer its own session unless identity-linked
SessionKey(p) ==
  IF DmScope = "main" THEN "main"
  ELSE
    \* choose a representative for the identity-link equivalence class
    CHOOSE r \in Peers: \A q \in Peers: Linked(p,q) <=> Linked(r,q)

\* Invariant: if two peers are not linked, their session keys differ (when per-peer).
Inv_NoUnlinkedCollapse ==
  DmScope = "per-peer" =>
    \A p1 \in Peers: \A p2 \in Peers:
      (~Linked(p1,p2)) => (SessionKey(p1) /= SessionKey(p2))

\* Trivial behavior for TLC
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
