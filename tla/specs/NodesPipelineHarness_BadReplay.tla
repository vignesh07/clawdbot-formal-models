------------------------------ MODULE NodesPipelineHarness_BadReplay ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* NodesPipelineHarness_BadReplay.tla
*
* Same as NodesPipelineHarness, but with a BUG: ApprovalOk ignores rid binding.
******************************************************************************)

CONSTANTS
  Tools,
  NodesRunTool,
  RequestIds,
  SessionType,
  PolicyAllowShared,
  PolicyAllowMain,
  NodeCommands,
  NodesRunCommand,
  PlatformDefaults,
  ExtraAllow,
  Deny,
  DeclaredByNode,
  ApprovalRequired,
  MaxQueueLen,
  MaxExecLen

ASSUME
  /\ Tools /= {} /\ NodesRunTool \in Tools
  /\ RequestIds /= {}
  /\ SessionType \in {"shared", "main"}
  /\ PolicyAllowShared \subseteq Tools /\ PolicyAllowMain \subseteq Tools
  /\ NodeCommands /= {} /\ NodesRunCommand \in NodeCommands
  /\ PlatformDefaults \subseteq NodeCommands /\ ExtraAllow \subseteq NodeCommands /\ Deny \subseteq NodeCommands
  /\ DeclaredByNode \subseteq NodeCommands
  /\ ApprovalRequired \in BOOLEAN
  /\ MaxQueueLen \in 0..5 /\ MaxExecLen \in 0..5

ApprovalStates == {"none", "pending", "approved", "denied", "expired"}
Req(t, rid) == [tool |-> t, rid |-> rid]

VARIABLES inbox, executed, approvalState, approvedRid
vars == << inbox, executed, approvalState, approvedRid >>

EffectiveAllowlist == (PlatformDefaults \cup ExtraAllow) \ Deny
NodeCommandAllowlisted == NodesRunCommand \in EffectiveAllowlist
NodeCommandDeclared == NodesRunCommand \in DeclaredByNode
AllowedByPolicy(t) == IF SessionType = "shared" THEN t \in PolicyAllowShared ELSE t \in PolicyAllowMain

\* BUG: approval ignores rid binding
ApprovalOk(_req) == IF ~ApprovalRequired THEN TRUE ELSE approvalState = "approved"

MayExecute(req) ==
  LET isNodesRun == req.tool = NodesRunTool
      policyOk == AllowedByPolicy(req.tool)
      nodesOk == IF isNodesRun THEN (NodeCommandAllowlisted /\ NodeCommandDeclared) ELSE TRUE
      approvalOk == IF isNodesRun THEN ApprovalOk(req) ELSE TRUE
  IN  policyOk /\ nodesOk /\ approvalOk

Init ==
  /\ inbox = << >>
  /\ executed = << >>
  /\ approvalState = "approved"
  /\ approvedRid = "r1"

AttackerSend(t, rid) ==
  /\ t \in Tools
  /\ rid \in RequestIds
  /\ Len(inbox) < MaxQueueLen
  /\ inbox' = Append(inbox, Req(t, rid))
  /\ UNCHANGED << executed, approvalState, approvedRid >>

AgentStep ==
  /\ Len(inbox) > 0
  /\ LET req == Head(inbox)
         approvedNow == (approvalState = "approved" /\ approvedRid = req.rid)
     IN  /\ inbox' = Tail(inbox)
         /\ executed' =
              IF MayExecute(req) /\ Len(executed) < MaxExecLen
                THEN Append(executed, [tool |-> req.tool, rid |-> req.rid, approved |-> approvedNow])
                ELSE executed
  /\ UNCHANGED << approvalState, approvedRid >>

Next == (\E t \in Tools, rid \in RequestIds: AttackerSend(t, rid)) \/ AgentStep
Spec == Init /\ [][Next]_vars

Inv_SharedNodesRunSafe ==
  SessionType = "shared" =>
    \A i \in 1..Len(executed):
      executed[i].tool = NodesRunTool => executed[i].approved = TRUE

=============================================================================
