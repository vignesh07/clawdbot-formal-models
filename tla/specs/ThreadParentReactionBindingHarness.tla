--------------------- MODULE ThreadParentReactionBindingHarness ---------------------
EXTENDS Naturals

(******************************************************************************
* ThreadParentReactionBindingHarness.tla
*
* Combined conformance model:
* - Reaction events in a thread should bind to the parent channel session
*   (thread-parent binding) and also anchor to the message id.
******************************************************************************)

CONSTANTS
  ParentChannelId,
  ThreadChannelId,
  MessageId,
  ReactionId

ASSUME
  /\ ParentChannelId \in {"p"}
  /\ ThreadChannelId \in {"t"}
  /\ MessageId \in {"m"}
  /\ ReactionId \in {"r"}

\* Intended: thread binds to parent channel
BindChannel(isThread) == IF isThread THEN ParentChannelId ELSE ThreadChannelId

SessionKeyForThreadMessage == <<BindChannel(TRUE), MessageId>>

\* Intended: reactions use same binding + anchor to message id
SessionKeyForThreadReaction == <<BindChannel(TRUE), MessageId>>

Inv_ReactionUsesParentAndMessage == SessionKeyForThreadReaction = SessionKeyForThreadMessage

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
