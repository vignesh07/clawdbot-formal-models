------ MODULE MessageLifecycleSessionKeyStabilityHarness_BadDeleteAnchorsWrong ------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: delete events anchor to DeleteEventId rather than MessageId.
* This can create a second session for the same message lifecycle.
******************************************************************************)

CONSTANTS
  ParentChannelId,
  ThreadChannelId,
  MessageId,
  EditEventId,
  DeleteEventId,
  ReactionId

ASSUME
  /\ ParentChannelId \in {"p"}
  /\ ThreadChannelId \in {"t"}
  /\ MessageId \in {"m"}
  /\ EditEventId \in {"e"}
  /\ DeleteEventId \in {"d"}
  /\ ReactionId \in {"r"}

BindChannel(isThread) == IF isThread THEN ParentChannelId ELSE ThreadChannelId

Key_Message == <<BindChannel(TRUE), MessageId>>

Key_Create == Key_Message
Key_Edit == Key_Message
\* BUG: delete anchors to DeleteEventId
Key_Delete == <<BindChannel(TRUE), DeleteEventId>>
Key_Reaction == Key_Message

VARIABLES
  seenCreate,
  seenEdit,
  seenDelete,
  seenReaction,
  tick

Init ==
  /\ seenCreate = {}
  /\ seenEdit = {}
  /\ seenDelete = {}
  /\ seenReaction = {}
  /\ tick = 0

DoCreate ==
  /\ seenCreate' = seenCreate \cup {Key_Create}
  /\ UNCHANGED <<seenEdit, seenDelete, seenReaction>>
  /\ tick' = 1 - tick

DoEdit ==
  /\ seenEdit' = seenEdit \cup {Key_Edit}
  /\ UNCHANGED <<seenCreate, seenDelete, seenReaction>>
  /\ tick' = 1 - tick

DoDelete ==
  /\ seenDelete' = seenDelete \cup {Key_Delete}
  /\ UNCHANGED <<seenCreate, seenEdit, seenReaction>>
  /\ tick' = 1 - tick

DoReaction ==
  /\ seenReaction' = seenReaction \cup {Key_Reaction}
  /\ UNCHANGED <<seenCreate, seenEdit, seenDelete>>
  /\ tick' = 1 - tick

Stutter == UNCHANGED <<seenCreate, seenEdit, seenDelete, seenReaction, tick>>

Next == DoCreate \/ DoEdit \/ DoDelete \/ DoReaction \/ Stutter

Inv_AllLifecycleKeysStable ==
  /\ seenCreate \subseteq {Key_Message}
  /\ seenEdit \subseteq {Key_Message}
  /\ seenDelete \subseteq {Key_Message}
  /\ seenReaction \subseteq {Key_Message}

Spec == Init /\ [][Next]_<<seenCreate, seenEdit, seenDelete, seenReaction, tick>>

=============================================================================
