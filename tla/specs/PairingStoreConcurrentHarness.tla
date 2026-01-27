------------------------------ MODULE PairingStoreConcurrentHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* PairingStoreConcurrentHarness.tla
*
* v1++: model a classic race in a pairing-store pending-cap check.
*
* Real-world motivation:
*   If RequestPair is implemented as "check cap" then "append" without a lock,
*   concurrent requests can both pass the cap check and then both write, causing
*   pending to exceed MaxPending.
*
* This harness models non-atomic requests:
*   - BeginRequest(tid, ch, s): records intent if cap check passes
*   - CommitRequest(tid): applies recorded intent WITHOUT re-checking cap
*
* Safety property:
*   live pending per channel <= MaxPending
******************************************************************************)

CONSTANTS
  Threads,     \* finite set, e.g. {1,2}
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

VARIABLES now, pending, inflight, step
vars == << now, pending, inflight, step >>

IsExpiredAt(req, t) == (t - req.createdAt) >= TTL
LivePendingAt(ch, t) == { r \in pending : r.ch = ch /\ ~IsExpiredAt(r, t) }

Init ==
  /\ now = 0
  /\ pending = {}
  /\ inflight = [t \in Threads |-> [active |-> FALSE, ch |-> CHOOSE c \in Channels: TRUE, s |-> CHOOSE s \in Senders: TRUE, createdAt |-> 0]]
  /\ step = 0

BeginRequest(t, ch, s) ==
  /\ step < MaxSteps
  /\ t \in Threads /\ ch \in Channels /\ s \in Senders
  /\ ~inflight[t].active
  /\ Cardinality(LivePendingAt(ch, now)) < MaxPending
  /\ inflight' = [inflight EXCEPT ![t] = [active |-> TRUE, ch |-> ch, s |-> s, createdAt |-> now]]
  /\ step' = step + 1
  /\ UNCHANGED << now, pending >>

CommitRequest(t) ==
  /\ step < MaxSteps
  /\ t \in Threads
  /\ inflight[t].active
  /\ pending' = pending \cup { Req(inflight[t].ch, inflight[t].s, inflight[t].createdAt) }
  /\ inflight' = [inflight EXCEPT ![t] = [@ EXCEPT !.active = FALSE]]
  /\ step' = step + 1
  /\ UNCHANGED now

Tick ==
  /\ step < MaxSteps
  /\ now < MaxTime
  /\ now' = now + 1
  /\ step' = step + 1
  /\ UNCHANGED << pending, inflight >>

Next ==
  (\E t \in Threads, ch \in Channels, s \in Senders: BeginRequest(t, ch, s))
  \/ (\E t \in Threads: CommitRequest(t))
  \/ Tick

Spec == Init /\ [][Next]_vars

Inv_PendingCap ==
  \A ch \in Channels: Cardinality(LivePendingAt(ch, now)) <= MaxPending

=============================================================================
