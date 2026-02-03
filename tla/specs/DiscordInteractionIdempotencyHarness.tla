---------------------- MODULE DiscordInteractionIdempotencyHarness ----------------------
EXTENDS Naturals

(******************************************************************************
* DiscordInteractionIdempotencyHarness.tla
*
* Reliability/security model:
* - Discord interactions (buttons/modals/slash) can be delivered/retried.
* - We must dedupe by interaction id to avoid executing the same action twice.
*
* Property: at-most-once execution per interaction id.
******************************************************************************)

CONSTANTS
  Interactions,    \* finite set of interaction ids
  MaxAttempts      \* small nat

ASSUME
  /\ Interactions /= {}
  /\ MaxAttempts \in Nat
  /\ MaxAttempts >= 1

VARIABLES
  pending,         \* SUBSET Interactions
  seen,            \* SUBSET Interactions
  executed,        \* SUBSET Interactions
  attempts         \* [Interactions -> Nat]

Init ==
  /\ pending = Interactions
  /\ seen = {}
  /\ executed = {}
  /\ attempts = [i \in Interactions |-> 0]

CanTry(i) == attempts[i] < MaxAttempts

\* Success executes at most once (deduped by seen).
Handle(i) ==
  /\ i \in pending
  /\ CanTry(i)
  /\ attempts' = [attempts EXCEPT ![i] = @ + 1]
  /\ IF i \in seen
        THEN /\ pending' = pending \ {i}
             /\ seen' = seen
             /\ executed' = executed
        ELSE /\ pending' = pending \ {i}
             /\ seen' = seen \cup {i}
             /\ executed' = executed \cup {i}

\* Retry path keeps it pending.
Retry(i) ==
  /\ i \in pending
  /\ CanTry(i)
  /\ attempts' = [attempts EXCEPT ![i] = @ + 1]
  /\ pending' = pending
  /\ seen' = seen
  /\ executed' = executed

Drop(i) ==
  /\ i \in pending
  /\ ~CanTry(i)
  /\ pending' = pending \ {i}
  /\ attempts' = attempts
  /\ seen' = seen
  /\ executed' = executed

Stutter == UNCHANGED <<pending, seen, executed, attempts>>

Next ==
  (\E i \in Interactions: Handle(i) \/ Retry(i) \/ Drop(i)) \/ Stutter

\* At-most-once: executed is a set, but we assert executed implies seen.
Inv_ExecutedImpliesSeen == executed \subseteq seen

Spec == Init /\ [][Next]_<<pending, seen, executed, attempts>>

=============================================================================
