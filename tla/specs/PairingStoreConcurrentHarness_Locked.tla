------------------------------ MODULE PairingStoreConcurrentHarness_Locked ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* PairingStoreConcurrentHarness_Locked.tla
*
* Same domain as PairingStoreConcurrentHarness, but models the "locked" / atomic
* version where the cap check and insertion are a single atomic action.
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

Init ==
  /\ now = 0
  /\ pending = {}
  /\ step = 0

AtomicRequest(t, ch, s) ==
  /\ step < MaxSteps
  /\ t \in Threads /\ ch \in Channels /\ s \in Senders
  /\ Cardinality(LivePendingAt(ch, now)) < MaxPending
  /\ pending' = pending \cup { Req(ch, s, now) }
  /\ step' = step + 1
  /\ UNCHANGED now

Tick ==
  /\ step < MaxSteps
  /\ now < MaxTime
  /\ now' = now + 1
  /\ step' = step + 1
  /\ UNCHANGED pending

Next ==
  (\E t \in Threads, ch \in Channels, s \in Senders: AtomicRequest(t, ch, s))
  \/ Tick

Spec == Init /\ [][Next]_vars

Inv_PendingCap ==
  \A ch \in Channels: Cardinality(LivePendingAt(ch, now)) <= MaxPending

=============================================================================
