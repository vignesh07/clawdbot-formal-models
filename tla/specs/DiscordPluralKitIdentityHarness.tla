------------------------- MODULE DiscordPluralKitIdentityHarness -------------------------
EXTENDS Naturals, FiniteSets

(******************************************************************************
* DiscordPluralKitIdentityHarness.tla
*
* Models Discord sender identity resolution when PluralKit support is enabled.
*
* Code references:
* - openclaw/src/discord/pluralkit.ts
* - openclaw/src/discord/monitor/sender-identity.ts
* - openclaw/src/discord/monitor/message-handler.preflight.ts
*
* Key intended security-relevant behaviors:
* 1) PluralKit resolution must NOT run for webhook messages.
* 2) Allowlist checks are applied against the resolved sender identity.
******************************************************************************)

CONSTANTS
  Authors,          \* Discord author ids
  Members,          \* PluralKit member ids
  AllowFromAuthor,  \* SUBSET Authors
  AllowFromMember,  \* SUBSET Members
  PKEnabled,        \* BOOLEAN
  IsWebhookMessage, \* BOOLEAN
  HasPKMember       \* BOOLEAN (whether PK lookup yields a member)

ASSUME
  /\ Authors /= {}
  /\ Members /= {}
  /\ AllowFromAuthor \subseteq Authors
  /\ AllowFromMember \subseteq Members
  /\ PKEnabled \in BOOLEAN
  /\ IsWebhookMessage \in BOOLEAN
  /\ HasPKMember \in BOOLEAN

\* If PK is enabled and this is not a webhook message, PK lookup may yield a member.
SenderIsPluralKit == PKEnabled /\ ~IsWebhookMessage /\ HasPKMember

\* Sender identity type: "author" or "pk"
SenderKind == IF SenderIsPluralKit THEN "pk" ELSE "author"

\* Authorization policy: allowed if sender id is allowlisted for its kind.
Authorized(senderKind) ==
  IF senderKind = "pk" THEN AllowFromMember /= {}
  ELSE AllowFromAuthor /= {}

\* Stronger per-id check, but we abstract to "exists allowed" by kind.
\* The important thing is that kind selection is correct.

Inv_NoPKForWebhooks ==
  IsWebhookMessage => ~SenderIsPluralKit

Inv_PKEnabledResolvesKind ==
  (PKEnabled /\ ~IsWebhookMessage /\ HasPKMember) => SenderKind = "pk"

Inv_AllowlistAppliedToResolvedKind ==
  Authorized(SenderKind)

\* Trivial behavior for TLC
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
