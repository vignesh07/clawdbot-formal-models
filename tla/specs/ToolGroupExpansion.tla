------------------------------ MODULE ToolGroupExpansion ------------------------------
EXTENDS Naturals, FiniteSets

(******************************************************************************
* ToolGroupExpansion.tla
*
* Conformance/security check: tool groups expand to specific tool sets.
*
* We treat tool ids as *strings* (TLC model values). This avoids confusion
* between TLA+ identifiers and model values.
******************************************************************************)

CONSTANTS
  Tools,        \* SUBSET STRING
  GroupMemory   \* SUBSET Tools (implementation's expansion of group:memory)

ASSUME
  /\ Tools /= {}
  /\ GroupMemory \subseteq Tools

MemorySearch == "memory_search"
MemoryGet == "memory_get"

Inv_GroupMemoryExact == GroupMemory = {MemorySearch, MemoryGet}

\* Trivial TLC behavior
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
