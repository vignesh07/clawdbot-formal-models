----------- MODULE RoutingThreadParentChannelOverrideHarness -----------
EXTENDS Naturals

(******************************************************************************
* RoutingThreadParentChannelOverrideHarness.tla
*
* Correctness model:
* - Discord thread messages should inherit the *parent channel* routing policy
*   (dm scope / channel overrides), not the thread channel's own config.
*
* This is a tiny conformance-style harness that isolates just that rule.
******************************************************************************)

CONSTANTS
  GlobalDmScope,
  ParentDmScope,
  ThreadDmScope

ASSUME
  /\ GlobalDmScope \in {"main","per-peer"}
  /\ ParentDmScope \in {"main","per-peer"}
  /\ ThreadDmScope \in {"main","per-peer"}

\* Which channel's scope config should apply
EffectiveScope(isThread) ==
  IF isThread
    THEN ParentDmScope
    ELSE ThreadDmScope

Inv_ThreadInheritsParent == EffectiveScope(TRUE) = ParentDmScope

\* Trivial Spec for TLC
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
