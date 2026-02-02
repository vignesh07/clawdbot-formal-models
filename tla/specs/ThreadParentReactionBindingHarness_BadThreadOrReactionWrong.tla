--------- MODULE ThreadParentReactionBindingHarness_BadThreadOrReactionWrong ---------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: reaction binds to thread channel and/or reaction id.
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

\* BUG: thread binding ignored
BindChannel(isThread) == ThreadChannelId

SessionKeyForThreadMessage == <<BindChannel(TRUE), MessageId>>

\* BUG: reaction anchors to ReactionId
SessionKeyForThreadReaction == <<BindChannel(TRUE), ReactionId>>

Inv_ReactionUsesParentAndMessage == SessionKeyForThreadReaction = SessionKeyForThreadMessage

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
