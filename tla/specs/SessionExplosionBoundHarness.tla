------------------------ MODULE SessionExplosionBoundHarness ------------------------
EXTENDS Naturals, FiniteSets

(******************************************************************************
* SessionExplosionBoundHarness.tla
*
* Non-security reliability/correctness model:
* - With a bounded set of peers, the system should not create more sessions
*   than some simple bound implied by dmScope + identityLinks.
*
* This is a coarse upper-bound check, not an exact count model.
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

Rep(p) == CHOOSE r \in Peers: \A q \in Peers: Linked(p,q) <=> Linked(r,q)

SessionKey(p) == IF DmScope = "main" THEN "main" ELSE Rep(p)

Sessions == { SessionKey(p) : p \in Peers }

\* Upper bound: in per-peer mode, sessions <= |Peers|; in main mode, sessions = 1.
Inv_SessionCountBound ==
  IF DmScope = "main" THEN Cardinality(Sessions) = 1
  ELSE Cardinality(Sessions) <= Cardinality(Peers)

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
