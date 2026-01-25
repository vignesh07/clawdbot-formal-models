# Security Claims (to model-check)

This doc enumerates **concrete security claims** we want to be able to say about
Clawdbot, and links each claim to:

- a TLA+ invariant (or temporal property)
- one or more TLC scenario models (`tla/models/*.cfg`)

The intent is to provide *auditable assurance*: each claim should be backed by a
reproducible model run.

## Claims

### C1 — Shared contexts cannot access memory tools

**Statement:** In any `shared` session (public channel / group chat context), the
agent must not be able to execute `memory_search` or `memory_get`.

**TLA+ invariant:** `Inv_NoMemoryToolInShared`

**Scenarios:**
- `tla/models/discord_shared.cfg`

---

### C2 — Approval gate blocks risky tools while pending

**Statement:** For tools requiring explicit approval (external side effects or
privileged execution), if a session is currently awaiting approval, those tools
cannot run.

**TLA+ invariant:** `Inv_ApprovalGate`

**Scenarios:**
- `tla/models/basic.cfg`

---

### C3 — Tool policy precedence is monotone (deny wins)

**Statement:** Tool filtering is monotone: once a tool is denied by an earlier
policy layer, later layers cannot re-enable it.

**Source:** `clawdbot/docs/multi-agent-sandbox-tools.md` (Tool Restrictions order)

**TLA+ invariant:** `Inv_DenyWins` in `tla/specs/ToolPolicyPrecedence.tla`

**Scenarios:**
- `tla/models/precedence_min.cfg`

**Negative test (should FAIL):**
- `tla/models/precedence_negative_bad_allow_overrides.cfg` with `tla/specs/ToolPolicyPrecedence_BadAllowOverrides.tla`

---

### C4 — Tool groups expand to the documented tool sets

**Statement:** Shorthand entries like `group:memory` expand to exactly the set
of tools documented in `multi-agent-sandbox-tools.md`.

**TLA+ invariant:** `Inv_GroupMemoryExact` in `tla/specs/ToolGroupExpansion.tla`

**Scenarios:**
- `tla/models/group_memory_ok.cfg`

**Negative test (should FAIL):**
- `tla/models/group_memory_bad_missing.cfg`

---

### C5 — Elevated execution requires both global and agent allowlists

**Statement:** Elevated mode requires BOTH the global baseline (`tools.elevated`)
AND the agent-specific elevated gate (`agents.list[].tools.elevated`) to allow.

**TLA+ invariant:** `Inv_ElevatedRequiresBoth` in `tla/specs/ElevatedGating.tla`

**Scenarios:**
- `tla/models/elevated_ok.cfg`

**Negative test (should FAIL):**
- `tla/models/elevated_negative_or_bug.cfg` with `tla/specs/ElevatedGating_BadOr.tla`

---

### C6 — `nodes.run` requires live approval when configured

**Statement:** When approval is required, `nodes.run` may only execute if the
approval state at execution time is `approved`.

**TLA+ invariant:** `Inv_NoNodesRunWithoutApproval` in `tla/specs/AttackerHarness_Approvals.tla`

**Scenarios:**
- `tla/models/approvals_ok.cfg`

**Negative test (should FAIL):**
- `tla/models/approvals_negative_ignore_approval.cfg` with `tla/specs/AttackerHarness_Approvals_BadIgnoresApproval.tla`
