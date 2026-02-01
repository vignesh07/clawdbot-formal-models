------------------- MODULE ConfigNormalizationIdempotencyHarness_BadToggle -------------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: normalization toggles a field back and forth (non-idempotent).
******************************************************************************)

CONSTANTS
  LegacyRoutingAllowFrom,
  LegacyDmPolicyOpenWithoutStar

ASSUME
  /\ LegacyRoutingAllowFrom \in BOOLEAN
  /\ LegacyDmPolicyOpenWithoutStar \in BOOLEAN

\* Normalize raw user config -> normalized snapshot.
NormalizeRaw(c) ==
  LET routingAllowFromPresent == FALSE
      dmPolicy == IF c.dmPolicyOpenWithoutStar THEN "pairing" ELSE "open"
      allowFromStar == IF dmPolicy = "open" THEN TRUE ELSE FALSE
  IN [ routingAllowFromPresent |-> routingAllowFromPresent,
       dmPolicy |-> dmPolicy,
       allowFromStar |-> allowFromStar ]

\* BUG: normalizing an already-normalized snapshot toggles a field.
NormalizeNorm(n) == [n EXCEPT !.routingAllowFromPresent = ~@]

Raw == [ dmPolicyOpenWithoutStar |-> LegacyDmPolicyOpenWithoutStar,
         routingAllowFromPresent |-> LegacyRoutingAllowFrom ]

Norm1 == NormalizeRaw(Raw)
Norm2 == NormalizeNorm(Norm1)

Inv_NormalizeIdempotent == Norm2 = Norm1

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
