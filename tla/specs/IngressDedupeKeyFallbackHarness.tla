------------------------------ MODULE IngressDedupeKeyFallbackHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* IngressDedupeKeyFallbackHarness.tla
*
* Roadmap R2+++++: provider nuances for idempotency when eventId is missing.
*
* Motivation:
*   Some providers (or some message types) may not supply a stable eventId.
*   Idempotency/dedupe often falls back to another correlation key (e.g. traceId
*   or a synthesized fingerprint).
*
* This harness models a safe fallback rule:
*   DedupeKey(event) = eventId if present else traceId.
*
* Scenario:
*   Two distinct external events arrive, both missing eventId but with distinct
*   traceIds. We must not accidentally treat them as duplicates.
*
* Property (modeled as an invariant with a phase variable):
*   After both deliveries have occurred, we have emitted one message per event.
******************************************************************************)

CONSTANTS
  Event1, Event2,
  EventId1, EventId2,
  TraceId1, TraceId2

ASSUME
  /\ Event1 /= Event2
  /\ EventId1 \in STRING /\ EventId2 \in STRING
  /\ TraceId1 \in STRING /\ TraceId2 \in STRING

DedupeKey(e) ==
  IF e = Event1 THEN (IF EventId1 /= "" THEN EventId1 ELSE TraceId1)
  ELSE             (IF EventId2 /= "" THEN EventId2 ELSE TraceId2)

VARIABLES seenKeys, emitted, phase
vars == << seenKeys, emitted, phase >>

Init ==
  /\ seenKeys = {}
  /\ emitted = {}
  /\ phase = 0

Deliver(e) ==
  LET k == DedupeKey(e) IN
    IF k \in seenKeys THEN
      /\ seenKeys' = seenKeys
      /\ emitted' = emitted
    ELSE
      /\ seenKeys' = seenKeys \cup {k}
      /\ emitted' = emitted \cup {e}

Next ==
  \/ /\ phase = 0
     /\ Deliver(Event1)
     /\ phase' = 1
  \/ /\ phase = 1
     /\ Deliver(Event2)
     /\ phase' = 2

Spec == Init /\ [][Next]_vars

Inv_BothDeliveredEmitted ==
  phase = 2 => (Event1 \in emitted /\ Event2 \in emitted)

=============================================================================
