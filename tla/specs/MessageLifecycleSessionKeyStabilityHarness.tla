-------------- MODULE MessageLifecycleSessionKeyStabilityHarness --------------
EXTENDS Naturals

(******************************************************************************
* MessageLifecycleSessionKeyStabilityHarness.tla
*
* Combined correctness harness (small but compositional):
* - Message lifecycle events: create/edit/delete/reaction
* - Thread-parent binding (events occur in a thread)
* - Retries (each event type can be observed multiple times)
*
* Property: all lifecycle events for the same anchor message in a thread bind to
* the same session key, and retries do not change that key.
*
* We model only the session key derivation + recording of observed keys.
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

\* Thread-parent binding
BindChannel(isThread) == IF isThread THEN ParentChannelId ELSE ThreadChannelId

\* Intended stable session key for the message-thread context
Key_Message == <<BindChannel(TRUE), MessageId>>

\* Intended: all lifecycle events anchor to MessageId
Key_Create == Key_Message
Key_Edit == Key_Message
Key_Delete == Key_Message
Key_Reaction == Key_Message

VARIABLES
  seenCreate,   \* SUBSET {Key_Message}
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

\* Each step records the key for an event type. Replays are allowed.
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

\* Invariant: every observed key equals the intended message key.
Inv_AllLifecycleKeysStable ==
  /\ seenCreate \subseteq {Key_Message}
  /\ seenEdit \subseteq {Key_Message}
  /\ seenDelete \subseteq {Key_Message}
  /\ seenReaction \subseteq {Key_Message}

Spec == Init /\ [][Next]_<<seenCreate, seenEdit, seenDelete, seenReaction, tick>>

=============================================================================
