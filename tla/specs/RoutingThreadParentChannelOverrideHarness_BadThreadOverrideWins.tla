----- MODULE RoutingThreadParentChannelOverrideHarness_BadThreadOverrideWins -----
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: thread-level channel override is used for thread messages.
******************************************************************************)

CONSTANTS
  GlobalDmScope,
  ParentDmScope,
  ThreadDmScope

ASSUME
  /\ GlobalDmScope \in {"main","per-peer"}
  /\ ParentDmScope \in {"main","per-peer"}
  /\ ThreadDmScope \in {"main","per-peer"}

\* BUG: even for thread messages, we use ThreadDmScope
EffectiveScope(isThread) == ThreadDmScope

Inv_ThreadInheritsParent == EffectiveScope(TRUE) = ParentDmScope

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
