------------------------------ MODULE NodesPipelineHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* NodesPipelineHarness.tla
*
* Composed end-to-end harness for the highest-risk path: nodes.run.
*
* Includes:
*  - shared-channel attacker producing requests (tool, rid)
*  - gateway node-command allow/deny composition (platform defaults ∪ allow \ deny)
*  - node declaredCommands gating
*  - tokenized approvals bound to a request id (rid)
*  - execution trace with per-step approved flag
*
* Primary security property:
*  In shared sessions, executing nodes.run must only occur when:
*    - nodes.run is allowed by policy, AND
*    - system.run is allowlisted by gateway (after deny), AND
*    - node declares system.run, AND
*    - (if approvals required) the rid matches the approved rid and approvalState=approved
******************************************************************************)

CONSTANTS
  \* Tool surface
  Tools,
  NodesRunTool,

  \* Request ids
  RequestIds,

  \* Session context (kept minimal for now)
  SessionType,               \* "shared" or "main"

  \* High-level tool policy
  PolicyAllowShared,
  PolicyAllowMain,

  \* Node command policy
  NodeCommands,
  NodesRunCommand,           \* "system.run"
  PlatformDefaults,
  ExtraAllow,
  Deny,
  DeclaredByNode,

  \* Approval policy
  ApprovalRequired,

  \* Bounds
  MaxQueueLen,
  MaxExecLen

ASSUME
  /\ Tools /= {} /\ NodesRunTool \in Tools
  /\ RequestIds /= {}
  /\ SessionType \in {"shared", "main"}

  /\ PolicyAllowShared \subseteq Tools
  /\ PolicyAllowMain \subseteq Tools

  /\ NodeCommands /= {}
  /\ NodesRunCommand \in NodeCommands
  /\ PlatformDefaults \subseteq NodeCommands
  /\ ExtraAllow \subseteq NodeCommands
  /\ Deny \subseteq NodeCommands
  /\ DeclaredByNode \subseteq NodeCommands

  /\ ApprovalRequired \in BOOLEAN

  /\ MaxQueueLen \in 0..5
  /\ MaxExecLen \in 0..5

ApprovalStates == {"none", "pending", "approved", "denied", "expired"}

Req(t, rid) == [tool |-> t, rid |-> rid]

VARIABLES inbox, executed, approvalState, approvedRid
vars == << inbox, executed, approvalState, approvedRid >>

EffectiveAllowlist == (PlatformDefaults \cup ExtraAllow) \ Deny
NodeCommandAllowlisted == NodesRunCommand \in EffectiveAllowlist
NodeCommandDeclared == NodesRunCommand \in DeclaredByNode

AllowedByPolicy(t) == IF SessionType = "shared" THEN t \in PolicyAllowShared ELSE t \in PolicyAllowMain

ApprovalOk(req) ==
  IF ~ApprovalRequired THEN TRUE
  ELSE approvalState = "approved" /\ approvedRid = req.rid

MayExecute(req) ==
  LET isNodesRun == req.tool = NodesRunTool
      policyOk == AllowedByPolicy(req.tool)
      nodesOk == IF isNodesRun THEN (NodeCommandAllowlisted /\ NodeCommandDeclared) ELSE TRUE
      approvalOk == IF isNodesRun THEN ApprovalOk(req) ELSE TRUE
  IN  policyOk /\ nodesOk /\ approvalOk

Init ==
  /\ inbox = << >>
  /\ executed = << >>
  /\ approvalState = "none"
  /\ approvedRid = CHOOSE r \in RequestIds: TRUE

AttackerSend(t, rid) ==
  /\ t \in Tools
  /\ rid \in RequestIds
  /\ Len(inbox) < MaxQueueLen
  /\ inbox' = Append(inbox, Req(t, rid))
  /\ UNCHANGED << executed, approvalState, approvedRid >>

RequestApproval(rid) ==
  /\ rid \in RequestIds
  /\ approvalState \in {"none", "denied", "expired"}
  /\ approvalState' = "pending"
  /\ approvedRid' = rid
  /\ UNCHANGED << inbox, executed >>

HumanApprove ==
  /\ approvalState = "pending"
  /\ approvalState' = "approved"
  /\ UNCHANGED << inbox, executed, approvedRid >>

ExpireApproval ==
  /\ approvalState = "approved"
  /\ approvalState' = "expired"
  /\ UNCHANGED << inbox, executed, approvedRid >>

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

Next ==
  (\E t \in Tools, rid \in RequestIds: AttackerSend(t, rid))
  \/ (\E rid \in RequestIds: RequestApproval(rid))
  \/ HumanApprove
  \/ ExpireApproval
  \/ AgentStep

Spec == Init /\ [][Next]_vars

\* Non-tautological, trace-based property:
Inv_SharedNodesRunSafe ==
  SessionType = "shared" =>
    \A i \in 1..Len(executed):
      executed[i].tool = NodesRunTool => executed[i].approved = TRUE

=============================================================================
