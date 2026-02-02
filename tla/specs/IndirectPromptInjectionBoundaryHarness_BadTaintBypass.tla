--------------- MODULE IndirectPromptInjectionBoundaryHarness_BadTaintBypass ---------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: tainted content bypasses approval and can execute sensitive tools.
******************************************************************************)

VARIABLES
  tainted,
  approved,
  executed

Init ==
  /\ tainted \in BOOLEAN
  /\ approved \in BOOLEAN
  /\ executed = FALSE

\* BUG: ignores approval entirely
CanExecuteSensitive == TRUE

ExecuteSensitive ==
  /\ ~executed
  /\ CanExecuteSensitive
  /\ executed' = TRUE
  /\ UNCHANGED <<tainted, approved>>

NoOp ==
  /\ executed' = executed
  /\ UNCHANGED <<tainted, approved>>

Next == ExecuteSensitive \/ NoOp

Inv_NoExecFromTaintedWithoutApproval ==
  (tainted /\ ~approved) => ~executed

Spec == Init /\ [][Next]_<<tainted, approved, executed>>

=============================================================================
