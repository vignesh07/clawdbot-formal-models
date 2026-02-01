------------------------ MODULE DeliveryPipelineHarness_BadNoDedupe ------------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* Negative model:
* BUG: success path emits but fails to mark the event deduped.
* Result: retries can emit duplicates.
******************************************************************************)

CONSTANTS
  Events,
  Routes,
  MaxAttempts,
  Route0Route

ASSUME
  /\ Events /= {}
  /\ Routes /= {}
  /\ MaxAttempts \in Nat
  /\ MaxAttempts >= 1
  /\ Route0Route \in Routes

VARIABLES
  pending,
  attempts,
  deduped,
  emitLog

Init ==
  /\ pending = Events
  /\ attempts = [e \in Events |-> 0]
  /\ deduped = {}
  /\ emitLog = << >>

CanTry(e) == attempts[e] < MaxAttempts

\* transient failure
ProcessFail(e) ==
  /\ e \in pending
  /\ CanTry(e)
  /\ pending' = pending
  /\ attempts' = [attempts EXCEPT ![e] = @ + 1]
  /\ deduped' = deduped
  /\ emitLog' = emitLog

\* BUG: emits but never adds to deduped
ProcessSuccess(e) ==
  /\ e \in pending
  /\ CanTry(e)
  /\ pending' = pending
  /\ attempts' = [attempts EXCEPT ![e] = @ + 1]
  /\ deduped' = deduped
  /\ emitLog' = Append(emitLog, e)

Drop(e) ==
  /\ e \in pending
  /\ ~CanTry(e)
  /\ pending' = pending \ {e}
  /\ attempts' = attempts
  /\ deduped' = deduped
  /\ emitLog' = emitLog

Stutter ==
  /\ pending' = pending
  /\ attempts' = attempts
  /\ deduped' = deduped
  /\ emitLog' = emitLog

Next ==
  (\E e \in Events: ProcessFail(e) \/ ProcessSuccess(e) \/ Drop(e))
  \/ Stutter

NoDups(seq) ==
  \A i, j \in 1..Len(seq): (i /= j) => seq[i] /= seq[j]

Inv_AtMostOnce == NoDups(emitLog)

Spec == Init /\ [][Next]_<<pending, attempts, deduped, emitLog>>

=============================================================================
