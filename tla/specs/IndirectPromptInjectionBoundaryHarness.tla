--------------------- MODULE IndirectPromptInjectionBoundaryHarness ---------------------
EXTENDS Naturals

(******************************************************************************
* IndirectPromptInjectionBoundaryHarness.tla
*
* Security/correctness model (tiny):
* - External content (links/attachments) is tainted.
* - Tainted content must never directly enable sensitive tool execution without
*   explicit approval.
*
* We model a single decision point: attempt to execute a sensitive tool.
******************************************************************************)

VARIABLES
  tainted,     \* BOOLEAN: whether the current instruction originates from untrusted external content
  approved,    \* BOOLEAN: whether an explicit approval was granted
  executed     \* BOOLEAN: whether sensitive tool execution occurred

Init ==
  /\ tainted \in BOOLEAN
  /\ approved \in BOOLEAN
  /\ executed = FALSE

CanExecuteSensitive ==
  \* Approval is always required; taint can only make it stricter (never looser).
  approved

ExecuteSensitive ==
  /\ ~executed
  /\ CanExecuteSensitive
  /\ executed' = TRUE
  /\ UNCHANGED <<tainted, approved>>

NoOp ==
  /\ executed' = executed
  /\ UNCHANGED <<tainted, approved>>

Next == ExecuteSensitive \/ NoOp

\* Key invariant: if tainted and not approved, execution must not happen.
Inv_NoExecFromTaintedWithoutApproval ==
  (tainted /\ ~approved) => ~executed

Spec == Init /\ [][Next]_<<tainted, approved, executed>>

=============================================================================
