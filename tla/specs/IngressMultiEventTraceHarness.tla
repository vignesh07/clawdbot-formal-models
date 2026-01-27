------------------------------ MODULE IngressMultiEventTraceHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* IngressMultiEventTraceHarness.tla
*
* Roadmap R2+++: multi-event / interleaving-safe trace correlation.
*
* Motivation:
*   Providers can deliver multiple external events in close succession, and the
*   gateway may expand each event into multiple internal messages. Under
*   interleavings, we must not "cross the streams": parts originating from
*   event E1 must never be stamped with E2's trace id (and vice versa).
*
* Model:
*   - Two external events (e1, e2), each with its own trace id.
*   - An ingest step can emit one part for either event, until all parts are
*     emitted.
*
* Safety property:
*   Each produced message's eventId maps to exactly the correct traceId.
******************************************************************************)

CONSTANTS
  Provider,             \* provider name/string
  Event1, Event2,       \* two external event ids
  Trace1, Trace2,       \* their trace ids
  NumParts1, NumParts2  \* number of internal parts per event

ASSUME
  /\ Provider \in STRING
  /\ Event1 \in STRING /\ Event2 \in STRING /\ Event1 /= Event2
  /\ Trace1 \in STRING /\ Trace2 \in STRING
  /\ NumParts1 \in 1..5 /\ NumParts2 \in 1..5

Msg(trace, provider, eventId, idx) ==
  [ traceId |-> trace,
    provider |-> provider,
    eventId  |-> eventId,
    partIdx  |-> idx ]

Events == {Event1, Event2}

TraceIdByEvent(e) == IF e = Event1 THEN Trace1 ELSE Trace2
NumPartsByEvent(e) == IF e = Event1 THEN NumParts1 ELSE NumParts2

VARIABLES produced, nextIdx
vars == << produced, nextIdx >>

Init ==
  /\ produced = << >>
  /\ nextIdx = [e \in Events |-> 1]

DoneFor(e) == nextIdx[e] > NumPartsByEvent(e)
AllDone == \A e \in Events: DoneFor(e)

EmitPart(e) ==
  /\ e \in Events
  /\ ~DoneFor(e)
  /\ produced' = Append(produced, Msg(TraceIdByEvent(e), Provider, e, nextIdx[e]))
  /\ nextIdx' = [nextIdx EXCEPT ![e] = @ + 1]

Next ==
  /\ ~AllDone
  /\ \E e \in Events: EmitPart(e)

Spec == Init /\ [][Next]_vars

Inv_CorrectTracePerEvent ==
  \A i \in 1..Len(produced):
    LET m == produced[i] IN
      /\ m.provider = Provider
      /\ m.traceId = TraceIdByEvent(m.eventId)

=============================================================================
