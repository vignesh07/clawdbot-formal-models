------------------------------ MODULE PairingStoreRefreshEnabledHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* PairingStoreRefreshEnabledHarness.tla
*
* Pairing-store nuance (R1+++): idempotent *refresh* must remain enabled even
* when the channel pending cap is reached.
*
* Motivation:
*   If a sender already has a live pending request, a repeated pairing command
*   should be treated as a refresh (replace/update) rather than a new allocation
*   of a pending slot. Even if the channel is at MaxPending, refresh should be
*   allowed because it doesn't increase the live count.
*
* This harness models:
*   - A pending set with per-channel MaxPending cap
*   - CreatePending: creates a new live pending request (subject to cap)
*   - RefreshPending: replaces an existing live pending request for (ch,s)
*
* Safety/availability-as-invariant:
*   If a live pending request exists for (ch,s), then RefreshPending for (ch,s)
*   is ENABLED.
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

\* New request consumes a slot (cap enforced)
CreatePending(tid, ch, s) ==
  /\ step < MaxSteps
  /\ tid \in Threads /\ ch \in Channels /\ s \in Senders
  /\ LiveFor(ch, s, now) = {}\* only create if none exists
  /\ Cardinality(LivePendingAt(ch, now)) < MaxPending
  /\ pending' = pending \cup { Req(ch, s, now) }
  /\ step' = step + 1
  /\ UNCHANGED now

\* Refresh is idempotent: replace existing live pending request (no cap check).
RefreshPending(tid, ch, s) ==
  /\ step < MaxSteps
  /\ tid \in Threads /\ ch \in Channels /\ s \in Senders
  /\ LiveFor(ch, s, now) /= {}
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

\* If a sender has a live pending request, refresh must be possible.
Inv_RefreshEnabled ==
  \A ch \in Channels, s \in Senders:
    (step < MaxSteps /\ LiveFor(ch, s, now) /= {})
      => ENABLED(\E tid \in Threads: RefreshPending(tid, ch, s))

=============================================================================
