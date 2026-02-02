------------ MODULE MessageDeleteSessionBindingHarness_BadDeleteOwnSession ------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: delete events bind to the delete event id, not the original message id.
******************************************************************************)

CONSTANTS
  ChannelId,
  MessageId,
  DeleteEventId

ASSUME
  /\ ChannelId \in {"c"}
  /\ MessageId \in {"m"}
  /\ DeleteEventId \in {"d"}

SessionKeyForMessage == <<ChannelId, MessageId>>

\* BUG: anchors to DeleteEventId
SessionKeyForDelete == <<ChannelId, DeleteEventId>>

Inv_DeleteBindsToMessage == SessionKeyForDelete = SessionKeyForMessage

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
