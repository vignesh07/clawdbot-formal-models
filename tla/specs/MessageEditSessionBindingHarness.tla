---------------------- MODULE MessageEditSessionBindingHarness ----------------------
EXTENDS Naturals

(******************************************************************************
* MessageEditSessionBindingHarness.tla
*
* Conformance/correctness model (tiny):
* - A message edit event must bind to the same session as the original message.
*
* This prevents edits from creating new sessions or escaping the original
* routing context.
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

\* Intended: edits anchor to the message id.
SessionKeyForEdit == <<ChannelId, MessageId>>

Inv_EditBindsToMessage == SessionKeyForEdit = SessionKeyForMessage

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
