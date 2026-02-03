--------------- MODULE MultiChannelIdentityOverrideHarness_BadIgnoresOverrides ---------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: if a link exists, the system collapses identities regardless of
* channel-level overrides.
******************************************************************************)

CONSTANTS
  LinkExists,
  ChannelA_AllowsCollapse,
  ChannelB_AllowsCollapse

ASSUME
  /\ LinkExists \in BOOLEAN
  /\ ChannelA_AllowsCollapse \in BOOLEAN
  /\ ChannelB_AllowsCollapse \in BOOLEAN

\* BUG: ignore per-channel overrides
CollapseAllowed == LinkExists

Inv_NoCollapseIfAnyOverrideDisables ==
  ((~ChannelA_AllowsCollapse) \/ (~ChannelB_AllowsCollapse)) => ~CollapseAllowed

Inv_NoCollapseWithoutLink ==
  (~LinkExists) => ~CollapseAllowed

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
