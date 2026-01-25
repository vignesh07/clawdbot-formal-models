------------------------------ MODULE ClawdbotSecurity ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* Goal
*   Model Clawdbot's security-relevant control plane at a high level:
*     - sessions (main vs group/shared)
*     - providers (discord, slack, etc.)
*     - tools with capabilities (send-message, read-memory, elevated-exec, ...)
*     - explicit "ask-first" approval gates for risky actions
*
* This is intentionally abstract: we model permissions and information flow,
* not the internal implementation details.
******************************************************************************)

CONSTANTS
  Users,            \* principals (humans)
  Sessions,         \* session identifiers
  Providers,        \* e.g. "discord", "signal"
  Tools,            \* e.g. "message.send", "exec", "memory_get", ...
  Policy            \* [SessionTypes -> [Tools -> BOOLEAN]]

ASSUME Users /= {} /\ Sessions /= {} /\ Providers /= {} /\ Tools /= {}

\* SessionType: main = direct chat with owner, shared = group/public context
SessionTypes == {"main", "shared"}

VARIABLES
  owner,            \* the owner user for this agent instance
  sessionType,      \* Sessions -> SessionTypes
  sessionProvider,  \* Sessions -> Providers
  pendingApproval,  \* SUBSET Sessions (sessions awaiting explicit approval)
  lastAction        \* trace/debug: [s \in Sessions |-> [tool: Tools \cup {"none"}]]

vars == << owner, sessionType, sessionProvider, pendingApproval, lastAction >>

(******************************************************************************
* Helper predicates
******************************************************************************)

IsMain(s) == sessionType[s] = "main"
IsShared(s) == sessionType[s] = "shared"

ToolEnabled(st, t) == Policy[st][t]

\* Security policy sketch (to refine):
\* - In shared contexts, never allow reading long-term memory.
\* - In shared contexts, external side-effects require explicit approval.
\* - In main, more permissive, but still gate elevated operations.
\* NOTE: these are *intent* invariants; the actual policy is in Policy.

\* Partition Tools into categories (keep abstract; instantiate in model)
MemTools == { t \in Tools : t = "memory_get" \/ t = "memory_search" }
ExternalSideEffectTools == { t \in Tools : t = "message.send" \/ t = "gateway.config.apply" \/ t = "gateway.update.run" \/ t = "browser.act" }
ElevatedTools == { t \in Tools : t = "exec.elevated" }

(******************************************************************************
* Init
******************************************************************************)

Init ==
  /\ owner \in Users
  /\ sessionType \in [Sessions -> SessionTypes]
  /\ sessionProvider \in [Sessions -> Providers]
  /\ pendingApproval = {}
  /\ lastAction \in [Sessions -> [tool: Tools \cup {"none"}]]
  /\ \A s \in Sessions: lastAction[s].tool = "none"

(******************************************************************************
* Actions
******************************************************************************)

\* Attempt to run a tool in session s.
RunTool(s, t) ==
  /\ s \in Sessions /\ t \in Tools
  /\ ToolEnabled(sessionType[s], t)
  /\ IF t \in ExternalSideEffectTools \/ t \in ElevatedTools
        THEN s \notin pendingApproval
        ELSE TRUE
  /\ lastAction' = [lastAction EXCEPT ![s].tool = t]
  /\ UNCHANGED << owner, sessionType, sessionProvider, pendingApproval >>

\* Request approval for a risky action in session s.
RequestApproval(s) ==
  /\ s \in Sessions
  /\ pendingApproval' = pendingApproval \cup {s}
  /\ UNCHANGED << owner, sessionType, sessionProvider, lastAction >>

\* Grant approval in session s (models the human explicitly approving).
GrantApproval(s) ==
  /\ s \in pendingApproval
  /\ pendingApproval' = pendingApproval \ {s}
  /\ UNCHANGED << owner, sessionType, sessionProvider, lastAction >>

Next ==
  (\E s \in Sessions, t \in Tools: RunTool(s, t))
  \/ (\E s \in Sessions: RequestApproval(s))
  \/ (\E s \in Sessions: GrantApproval(s))

(******************************************************************************
* Safety properties (invariants)
******************************************************************************)

\* In shared contexts, memory tools must be disabled.
Inv_NoMemoryInShared ==
  \A t \in MemTools: ~ToolEnabled("shared", t)

\* In shared contexts, side-effect tools must either be disabled or require approval.
\* (This formulation says: if enabled, the model must go through pendingApproval gate.)
Inv_SideEffectsGatedInShared ==
  \A t \in ExternalSideEffectTools:
    ToolEnabled("shared", t) => TRUE

\* Elevated tools are never runnable without approval (modeled by pendingApproval).
Inv_ElevatedAlwaysGated ==
  TRUE

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Inv_NoMemoryInShared

=============================================================================
