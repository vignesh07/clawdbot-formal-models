---------------- MODULE DiscordInteractionIdempotencyHarness_BadNoDedupe ----------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: interactions are not deduped; retries can execute multiple times.
******************************************************************************)

CONSTANTS
  Interactions,
  MaxAttempts

ASSUME
  /\ Interactions /= {}
  /\ MaxAttempts \in Nat
  /\ MaxAttempts >= 1

VARIABLES
  pending,
  executedCount,   \* [Interactions -> Nat]
  attempts

Init ==
  /\ pending = Interactions
  /\ executedCount = [i \in Interactions |-> 0]
  /\ attempts = [i \in Interactions |-> 0]

CanTry(i) == attempts[i] < MaxAttempts

Handle(i) ==
  /\ i \in pending
  /\ CanTry(i)
  /\ attempts' = [attempts EXCEPT ![i] = @ + 1]
  /\ executedCount' = [executedCount EXCEPT ![i] = @ + 1]
  /\ pending' = pending    \* BUG: stays pending, can execute again

Retry(i) ==
  /\ i \in pending
  /\ CanTry(i)
  /\ attempts' = [attempts EXCEPT ![i] = @ + 1]
  /\ executedCount' = executedCount
  /\ pending' = pending

Drop(i) ==
  /\ i \in pending
  /\ ~CanTry(i)
  /\ pending' = pending \ {i}
  /\ attempts' = attempts
  /\ executedCount' = executedCount

Stutter == UNCHANGED <<pending, executedCount, attempts>>

Next == (\E i \in Interactions: Handle(i) \/ Retry(i) \/ Drop(i)) \/ Stutter

Inv_AtMostOnce == \A i \in Interactions: executedCount[i] <= 1

Spec == Init /\ [][Next]_<<pending, executedCount, attempts>>

=============================================================================
