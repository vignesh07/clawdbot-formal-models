------------------------------ MODULE PairingStoreRefreshEnabledHarness_BadCapOnRefresh ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* PairingStoreRefreshEnabledHarness_BadCapOnRefresh.tla
*
* "Red" variant: refresh incorrectly reuses the *create* cap check
* (Cardinality(LivePendingAt) < MaxPending) without accounting for the fact
* that the refresh replaces an existing entry.
*
* With MaxPending=1 and an existing live request, this makes refresh disabled.
******************************************************************************)

CONSTANTS
  Threads,
  Channels,
  Senders,
  TTL,
  MaxPending,
  MaxTime,
  MaxSteps

ASSUME
  /\ Threads /= {} /\ Channels /= {} /\ Senders /= {}
  /\ TTL \in 1..MaxTime
  /\ MaxPending \in 1..5
  /\ MaxTime \in 1..20
  /\ MaxSteps \in 1..50

Req(ch, sender, createdAt) == [ch |-> ch, sender |-> sender, createdAt |-> createdAt]

VARIABLES now, pending, step
vars == << now, pending, step >>

IsExpiredAt(req, t) == (t - req.createdAt) >= TTL
LivePendingAt(ch, t) == { r \in pending : r.ch = ch /\ ~IsExpiredAt(r, t) }
LiveFor(ch, s, t) == { r \in pending : r.ch = ch /\ r.sender = s /\ ~IsExpiredAt(r, t) }

Init ==
  /\ now = 0
  /\ pending = {}
  /\ step = 0

CreatePending(tid, ch, s) ==
  /\ step < MaxSteps
  /\ tid \in Threads /\ ch \in Channels /\ s \in Senders
  /\ LiveFor(ch, s, now) = {}
  /\ Cardinality(LivePendingAt(ch, now)) < MaxPending
  /\ pending' = pending \cup { Req(ch, s, now) }
  /\ step' = step + 1
  /\ UNCHANGED now

\* BUG: applies cap check even though this is a replacement.
RefreshPending(tid, ch, s) ==
  /\ step < MaxSteps
  /\ tid \in Threads /\ ch \in Channels /\ s \in Senders
  /\ LiveFor(ch, s, now) /= {}
  /\ Cardinality(LivePendingAt(ch, now)) < MaxPending
  /\ pending' = (pending \ LiveFor(ch, s, now)) \cup { Req(ch, s, now) }
  /\ step' = step + 1
  /\ UNCHANGED now

Tick ==
  /\ step < MaxSteps
  /\ now < MaxTime
  /\ now' = now + 1
  /\ step' = step + 1
  /\ UNCHANGED pending

Next ==
  (\E tid \in Threads, ch \in Channels, s \in Senders: CreatePending(tid, ch, s))
  \/ (\E tid \in Threads, ch \in Channels, s \in Senders: RefreshPending(tid, ch, s))
  \/ Tick

Spec == Init /\ [][Next]_vars

Inv_RefreshEnabled ==
  \A ch \in Channels, s \in Senders:
    (step < MaxSteps /\ LiveFor(ch, s, now) /= {})
      => ENABLED(\E tid \in Threads: RefreshPending(tid, ch, s))

=============================================================================
