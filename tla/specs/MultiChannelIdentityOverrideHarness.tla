---------------------- MODULE MultiChannelIdentityOverrideHarness ----------------------
EXTENDS Naturals

(******************************************************************************
* MultiChannelIdentityOverrideHarness.tla
*
* Composition harness:
* - Two channels A and B.
* - Identity-link may exist between A:u and B:u.
* - Each channel may override whether identity-collapse is allowed (via dm scope
*   or explicit "disable collapse" policy).
*
* Property: a cross-channel identity collapse is allowed iff:
*   LinkExists AND CollapseAllowedByChannelOverrides.
******************************************************************************)

CONSTANTS
  LinkExists,              \* BOOLEAN
  ChannelA_AllowsCollapse, \* BOOLEAN
  ChannelB_AllowsCollapse  \* BOOLEAN

ASSUME
  /\ LinkExists \in BOOLEAN
  /\ ChannelA_AllowsCollapse \in BOOLEAN
  /\ ChannelB_AllowsCollapse \in BOOLEAN

CollapseAllowed ==
  LinkExists /\ ChannelA_AllowsCollapse /\ ChannelB_AllowsCollapse

Inv_NoCollapseIfAnyOverrideDisables ==
  ((~ChannelA_AllowsCollapse) \/ (~ChannelB_AllowsCollapse)) => ~CollapseAllowed

Inv_NoCollapseWithoutLink ==
  (~LinkExists) => ~CollapseAllowed

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
