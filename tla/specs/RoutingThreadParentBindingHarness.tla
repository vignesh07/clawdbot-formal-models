------------------------- MODULE RoutingThreadParentBindingHarness -------------------------
EXTENDS Naturals

(******************************************************************************
* RoutingThreadParentBindingHarness.tla
*
* Models OpenClaw routing behavior for Discord thread messages when
* "binding inheritance" from the parent channel is enabled.
*
* Code reference:
* - openclaw/src/routing/resolve-route.ts (matchedBy="binding.peer.parent")
* - discord preflight resolves thread parent and passes parentPeer
*
* Intended behavior:
* - If a thread peer has an explicit binding, it wins.
* - Otherwise, if the parent channel has a binding, inherit it.
* - Otherwise, fall back to default agent.
******************************************************************************)

CONSTANTS
  Agents,
  DefaultAgent,
  HasThreadBinding,       \* BOOLEAN
  HasParentBinding,       \* BOOLEAN
  ThreadAgent,
  ParentAgent

ASSUME
  /\ Agents /= {}
  /\ DefaultAgent \in Agents
  /\ HasThreadBinding \in BOOLEAN
  /\ HasParentBinding \in BOOLEAN
  /\ ThreadAgent \in Agents
  /\ ParentAgent \in Agents

ResolvedAgent ==
  IF HasThreadBinding THEN ThreadAgent
  ELSE IF HasParentBinding THEN ParentAgent
  ELSE DefaultAgent

Inv_ThreadBindingWins ==
  HasThreadBinding => ResolvedAgent = ThreadAgent

Inv_ParentBindingInheritedWhenNoThreadBinding ==
  (~HasThreadBinding /\ HasParentBinding) => ResolvedAgent = ParentAgent

Inv_DefaultWhenNoBindings ==
  (~HasThreadBinding /\ ~HasParentBinding) => ResolvedAgent = DefaultAgent

\* Trivial behavior for TLC
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
