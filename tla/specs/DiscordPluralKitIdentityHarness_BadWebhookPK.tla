------------------- MODULE DiscordPluralKitIdentityHarness_BadWebhookPK -------------------
EXTENDS Naturals, FiniteSets

(******************************************************************************
* Negative model:
* Demonstrates a bug where webhook messages can be treated as PluralKit.
******************************************************************************)

CONSTANTS
  Authors,
  Members,
  AllowFromAuthor,
  AllowFromMember,
  PKEnabled,
  IsWebhookMessage,
  HasPKMember

ASSUME
  /\ Authors /= {}
  /\ Members /= {}
  /\ AllowFromAuthor \subseteq Authors
  /\ AllowFromMember \subseteq Members
  /\ PKEnabled \in BOOLEAN
  /\ IsWebhookMessage \in BOOLEAN
  /\ HasPKMember \in BOOLEAN

\* BUG: ignores IsWebhookMessage
SenderIsPluralKit == PKEnabled /\ HasPKMember

Inv_NoPKForWebhooks ==
  IsWebhookMessage => ~SenderIsPluralKit

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
