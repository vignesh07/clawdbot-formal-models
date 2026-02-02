-------------- MODULE MessageEditSessionBindingHarness_BadEditOwnSession --------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: edit events bind to the edit event id, not the original message id.
******************************************************************************)

CONSTANTS
  ChannelId,
  MessageId,
  EditEventId

ASSUME
  /\ ChannelId \in {"c"}
  /\ MessageId \in {"m"}
  /\ EditEventId \in {"e"}

SessionKeyForMessage == <<ChannelId, MessageId>>

\* BUG: anchors to EditEventId
SessionKeyForEdit == <<ChannelId, EditEventId>>

Inv_EditBindsToMessage == SessionKeyForEdit = SessionKeyForMessage

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
