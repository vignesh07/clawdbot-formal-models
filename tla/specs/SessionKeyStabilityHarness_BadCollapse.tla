---------------------- MODULE SessionKeyStabilityHarness_BadCollapse ----------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* Negative model:
* BUG: per-peer mode collapses all peers into the same session key.
******************************************************************************)

CONSTANTS
  Peers,
  DmScope

ASSUME
  /\ Peers /= {}
  /\ DmScope \in {"main","per-peer"}

SessionKey(p) == "main"  \* BUG: always main

Inv_NoUnlinkedCollapse ==
  DmScope = "per-peer" =>
    \A p1 \in Peers: \A p2 \in Peers:
      (p1 /= p2) => (SessionKey(p1) /= SessionKey(p2))

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
