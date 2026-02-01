------------------- MODULE RoutingThreadParentBindingHarness_BadThreadLoses -------------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* Demonstrates TLC catches a bug where parent binding incorrectly overrides
* an explicit thread binding.
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

\* BUG: parent wins even when thread binding exists
ResolvedAgent ==
  IF HasParentBinding THEN ParentAgent
  ELSE IF HasThreadBinding THEN ThreadAgent
  ELSE DefaultAgent

Inv_ThreadBindingWins ==
  HasThreadBinding => ResolvedAgent = ThreadAgent

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
