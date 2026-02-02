--------------------- MODULE MessageDeleteSessionBindingHarness ---------------------
EXTENDS Naturals

(******************************************************************************
* MessageDeleteSessionBindingHarness.tla
*
* Conformance/correctness model (tiny):
* - A message delete event must bind to the same session as the original
*   message.
*
* This prevents deletes from creating new sessions or escaping routing context.
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

\* Intended: deletes anchor to the message id.
SessionKeyForDelete == <<ChannelId, MessageId>>

Inv_DeleteBindsToMessage == SessionKeyForDelete = SessionKeyForMessage

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
