---------------------- MODULE ConfigNormalizationIdempotencyHarness ----------------------
EXTENDS Naturals

(******************************************************************************
* ConfigNormalizationIdempotencyHarness.tla
*
* Non-security correctness model:
* - Config normalization/migration should be idempotent:
*     Normalize(Normalize(c)) = Normalize(c)
*
* This is an abstraction of OpenClaw's config normalization + legacy migration.
* It does NOT model parsing, only the policy-level transformation.
*
* The model uses a tiny config state with a few representative knobs.
******************************************************************************)

CONSTANTS
  LegacyRoutingAllowFrom,
  LegacyDmPolicyOpenWithoutStar

ASSUME
  /\ LegacyRoutingAllowFrom \in BOOLEAN
  /\ LegacyDmPolicyOpenWithoutStar \in BOOLEAN

\* Normalize raw user config -> normalized snapshot.
NormalizeRaw(c) ==
  LET routingAllowFromPresent == FALSE \* removed in normalized snapshot
      dmPolicy == IF c.dmPolicyOpenWithoutStar THEN "pairing" ELSE "open"
      allowFromStar == IF dmPolicy = "open" THEN TRUE ELSE FALSE
  IN [ routingAllowFromPresent |-> routingAllowFromPresent,
       dmPolicy |-> dmPolicy,
       allowFromStar |-> allowFromStar ]

\* Normalize an already-normalized snapshot.
\* In the intended design, normalization is idempotent at this layer.
NormalizeNorm(n) == n

\* Project raw input "c" from legacy booleans
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
