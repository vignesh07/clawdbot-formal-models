------------------------------ MODULE NodesCommandPolicy_BadNoDeclareCheck ------------------------------
EXTENDS Naturals, FiniteSets

(******************************************************************************
* Negative test: BUGGY node command policy that forgets to require declaredCommands.
******************************************************************************)

CONSTANTS
  Commands,
  PlatformDefaults,
  ExtraAllow,
  Deny,
  DeclaredByNode,
  Cmd

ASSUME
  /\ Commands /= {}
  /\ PlatformDefaults \subseteq Commands
  /\ ExtraAllow \subseteq Commands
  /\ Deny \subseteq Commands
  /\ DeclaredByNode \subseteq Commands

EffectiveAllowlist == (PlatformDefaults \cup ExtraAllow) \ Deny

\* BUG: ignore DeclaredByNode
IsAllowed(cmd) == (cmd \in EffectiveAllowlist)

Inv_AllowedImpliesDeclared == \A c \in Commands: IsAllowed(c) => (c \in DeclaredByNode)

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
