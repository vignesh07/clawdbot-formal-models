--------------------------- MODULE SessionKeyStabilityHarness ---------------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* SessionKeyStabilityHarness.tla
*
* Non-security correctness model:
* - Session keys should be stable under repeated resolution for the same
*   logical peer + same config.
*
* This models session key construction at the level of dmScope + identityLinks
* collapsing.
*
* NOTE: This is an abstraction of OpenClaw routing/session-key behavior:
* - openclaw/src/routing/session-key.ts
* - openclaw/src/routing/resolve-route.ts (dmScope selection)
******************************************************************************)

CONSTANTS
  Peers,
  DmScope,          \* "main" | "per-peer"
  IdentityLinks     \* SUBSET (Peers \X Peers)

ASSUME
  /\ Peers /= {}
  /\ DmScope \in {"main","per-peer"}
  /\ IdentityLinks \subseteq (Peers \X Peers)

Linked(a,b) == <<a,b>> \in IdentityLinks \/ <<b,a>> \in IdentityLinks \/ a=b

\* Canonical representative for the equivalence class of p
Rep(p) == CHOOSE r \in Peers: \A q \in Peers: Linked(p,q) <=> Linked(r,q)

SessionKey(p) ==
  IF DmScope = "main" THEN "main" ELSE Rep(p)

\* Stability: repeated resolution yields the same key (pure function).
Inv_Stable(p) == SessionKey(p) = SessionKey(p)

\* Non-collapse: under per-peer, unlinked peers should not collide.
Inv_NoUnlinkedCollapse ==
  DmScope = "per-peer" =>
    \A p1 \in Peers: \A p2 \in Peers:
      (~Linked(p1,p2)) => (SessionKey(p1) /= SessionKey(p2))

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
