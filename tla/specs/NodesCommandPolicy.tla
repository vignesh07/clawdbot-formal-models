------------------------------ MODULE NodesCommandPolicy ------------------------------
EXTENDS Naturals, FiniteSets

(******************************************************************************
* NodesCommandPolicy.tla
*
* Models the gateway node command allowlist policy (simplified).
*
* Code reference:
*   clawdbot/src/gateway/node-command-policy.ts
*
* Key rules:
*   1) allowed if in effective allowlist (platform defaults + extra - deny)
*   2) AND command is declared by the node
******************************************************************************)

CONSTANTS
  Commands,                \* finite set of command ids
  PlatformDefaults,        \* SUBSET Commands
  ExtraAllow,              \* SUBSET Commands (gateway.nodes.allowCommands)
  Deny,                    \* SUBSET Commands (gateway.nodes.denyCommands)
  DeclaredByNode,          \* SUBSET Commands (node session declaredCommands)
  Cmd                       \* a specific command to check

ASSUME
  /\ Commands /= {}
  /\ PlatformDefaults \subseteq Commands
  /\ ExtraAllow \subseteq Commands
  /\ Deny \subseteq Commands
  /\ DeclaredByNode \subseteq Commands
  /\ Cmd \in Commands

EffectiveAllowlist == (PlatformDefaults \cup ExtraAllow) \ Deny

IsAllowed(cmd) == (cmd \in EffectiveAllowlist) /\ (cmd \in DeclaredByNode)

\* --- Invariants / properties ---

\* NC1: deny wins over allow/defaults
Inv_DenyWins == \A c \in Deny: c \notin EffectiveAllowlist

\* NC2: if node doesn't declare the command, it's not allowed
\* Stronger (and more direct): if a command is allowed, it must be declared.
Inv_AllowedImpliesDeclared == \A c \in Commands: IsAllowed(c) => (c \in DeclaredByNode)

\* NC3: if command is not in effective allowlist, it's not allowed
Inv_MustBeAllowlisted == \A c \in Commands: ~(c \in EffectiveAllowlist) => ~IsAllowed(c)

\* Trivial TLC behavior
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
