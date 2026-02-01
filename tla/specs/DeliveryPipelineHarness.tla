------------------------------ MODULE DeliveryPipelineHarness ------------------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* DeliveryPipelineHarness.tla
*
* End-to-end-ish abstraction:
* - Ingress can retry the same logical event.
* - Routing determines a session key for that event.
* - Dedupe ensures at-most-once emission per event.
*
* We model a single worker that non-deterministically attempts to process
* pending events (either fails transiently or succeeds).
*
* Properties:
* - Safety: an event is emitted at most once.
* - Safety: if emitted, it is emitted to the stable intended session key.
******************************************************************************)

CONSTANTS
  Events,        \* finite set of event ids
  Routes,        \* finite set of route ids
  MaxAttempts,   \* small nat
  Route0Route    \* intended stable route for all events in this tiny harness

ASSUME
  /\ Events /= {}
  /\ Routes /= {}
  /\ MaxAttempts \in Nat
  /\ MaxAttempts >= 1
  /\ Route0Route \in Routes

VARIABLES
  pending,       \* SUBSET Events
  attempts,      \* [Events -> Nat]
  deduped,       \* SUBSET Events
  emitLog        \* Seq(Events)  (each element is the logical event id)

Init ==
  /\ pending = Events
  /\ attempts = [e \in Events |-> 0]
  /\ deduped = {}
  /\ emitLog = << >>

CanTry(e) == attempts[e] < MaxAttempts

SessionKey(e) == <<Route0Route, e>>

\* transient failure: increments attempts but does not emit
ProcessFail(e) ==
  /\ e \in pending
  /\ CanTry(e)
  /\ pending' = pending
  /\ attempts' = [attempts EXCEPT ![e] = @ + 1]
  /\ deduped' = deduped
  /\ emitLog' = emitLog

\* success path:
\* - if not deduped, emit once and mark deduped
\* - if deduped already, treat as a no-op success (idempotent)
ProcessSuccess(e) ==
  /\ e \in pending
  /\ CanTry(e)
  /\ pending' = pending \ {e}
  /\ attempts' = [attempts EXCEPT ![e] = @ + 1]
  /\ IF e \in deduped
        THEN /\ deduped' = deduped
             /\ emitLog' = emitLog
        ELSE /\ deduped' = deduped \cup {e}
             /\ emitLog' = Append(emitLog, e)

\* drop after exhausting attempts
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

\* Helper: no duplicates in a sequence
NoDups(seq) ==
  \A i, j \in 1..Len(seq): (i /= j) => seq[i] /= seq[j]

Inv_AtMostOnce == NoDups(emitLog)

\* If an event is in the log, it must be in deduped.
Inv_LogImpliesDeduped ==
  \A e \in Events: (\E i \in 1..Len(emitLog): emitLog[i] = e) => e \in deduped

\* Route/session stability is encoded by construction (SessionKey depends only on Route0Route and e);
\* we still assert that emitted events are compatible with that binding.
Inv_EmitsUseStableSession ==
  \A e \in Events:
    (\E i \in 1..Len(emitLog): emitLog[i] = e) => SessionKey(e)[1] = Route0Route

Spec == Init /\ [][Next]_<<pending, attempts, deduped, emitLog>>

=============================================================================
