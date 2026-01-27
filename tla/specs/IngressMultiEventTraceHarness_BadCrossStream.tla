------------------------------ MODULE IngressMultiEventTraceHarness_BadCrossStream ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* IngressMultiEventTraceHarness_BadCrossStream.tla
*
* "Red" variant: bug where traceId can come from the wrong in-flight event.
*
* Specifically, when emitting a part for event e, the implementation may stamp
* it with TraceIdByEvent[otherEvent]. This should violate Inv_CorrectTracePerEvent.
******************************************************************************)

CONSTANTS
  Provider,
  Event1, Event2,
  Trace1, Trace2,
  NumParts1, NumParts2

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

OtherEvent(e) == IF e = Event1 THEN Event2 ELSE Event1

\* BUG: uses the other event's traceId when emitting.
EmitPartBug(e) ==
  /\ e \in Events
  /\ ~DoneFor(e)
  /\ produced' = Append(produced, Msg(TraceIdByEvent(OtherEvent(e)), Provider, e, nextIdx[e]))
  /\ nextIdx' = [nextIdx EXCEPT ![e] = @ + 1]

Next ==
  /\ ~AllDone
  /\ \E e \in Events: EmitPartBug(e)

Spec == Init /\ [][Next]_vars

Inv_CorrectTracePerEvent ==
  \A i \in 1..Len(produced):
    LET m == produced[i] IN
      /\ m.provider = Provider
      /\ m.traceId = TraceIdByEvent(m.eventId)

=============================================================================
