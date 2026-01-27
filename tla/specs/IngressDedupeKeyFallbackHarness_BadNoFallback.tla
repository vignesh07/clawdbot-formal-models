------------------------------ MODULE IngressDedupeKeyFallbackHarness_BadNoFallback ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* IngressDedupeKeyFallbackHarness_BadNoFallback.tla
*
* "Red" variant: dedupe key uses only eventId and does NOT fall back when
* eventId is missing.
*
* If both events have empty eventId, they share the same key "" and one event
* is dropped as a duplicate.
******************************************************************************)

CONSTANTS
  Event1, Event2,
  EventId1, EventId2,
  TraceId1, TraceId2

ASSUME
  /\ Event1 /= Event2
  /\ EventId1 \in STRING /\ EventId2 \in STRING
  /\ TraceId1 \in STRING /\ TraceId2 \in STRING

\* BUG: no fallback.
DedupeKey(e) == IF e = Event1 THEN EventId1 ELSE EventId2

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
