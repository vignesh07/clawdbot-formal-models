TLC=./bin/tlc
MODEL?=tla/models/basic.cfg

.PHONY: tlc precedence precedence-negative groups groups-negative elevated elevated-negative nodes-policy nodes-policy-negative attacker attacker-negative attacker-nodes-negative attacker-nodes-allowlist attacker-nodes-allowlist-negative approvals approvals-negative approvals-token approvals-token-negative nodes-pipeline nodes-pipeline-negative

# Run TLC with a pinned, in-repo model config

tlc:
	$(TLC) -workers auto -deadlock -config $(MODEL) tla/specs/ClawdbotSecurity.tla

# Prove monotonic "deny wins" for tool policy precedence
precedence:
	$(TLC) -workers auto -config tla/models/precedence_min.cfg tla/specs/ToolPolicyPrecedence.tla

# Negative test: demonstrate TLC catches a precedence bug where allow overrides deny
precedence-negative:
	$(TLC) -workers auto -config tla/models/precedence_negative_bad_allow_overrides.cfg tla/specs/ToolPolicyPrecedence_BadAllowOverrides.tla

# Tool group expansion checks

groups:
	$(TLC) -workers auto -config tla/models/group_memory_ok.cfg tla/specs/ToolGroupExpansion.tla

groups-negative:
	$(TLC) -workers auto -config tla/models/group_memory_bad_missing.cfg tla/specs/ToolGroupExpansion.tla

# Elevated gating checks

elevated:
	$(TLC) -workers auto -config tla/models/elevated_ok.cfg tla/specs/ElevatedGating.tla

elevated-negative:
	$(TLC) -workers auto -config tla/models/elevated_negative_or_bug.cfg tla/specs/ElevatedGating_BadOr.tla

# Nodes gateway command policy checks

nodes-policy:
	$(TLC) -workers auto -config tla/models/nodes_policy_ok.cfg tla/specs/NodesCommandPolicy.tla

nodes-policy-negative:
	$(TLC) -workers auto -config tla/models/nodes_policy_negative_bad_impl_allows_undeclared.cfg tla/specs/NodesCommandPolicy_BadNoDeclareCheck.tla

# Attacker harness (shared-channel adversary)

attacker:
	$(TLC) -workers auto -deadlock -config tla/models/attacker_ok.cfg tla/specs/AttackerHarness.tla

attacker-negative:
	$(TLC) -workers auto -deadlock -config tla/models/attacker_negative_policy_allows_memory.cfg tla/specs/AttackerHarness.tla

# Nodes extension: declaredCommands must gate nodes.run
attacker-nodes-negative:
	$(TLC) -workers auto -deadlock -config tla/models/attacker_negative_nodes_declared_missing.cfg tla/specs/AttackerHarness_BadIgnoresNodeDeclare.tla

# Attacker harness with derived node-command allowlist
attacker-nodes-allowlist:
	$(TLC) -workers auto -deadlock -config tla/models/attacker_nodes_allowlist_ok.cfg tla/specs/AttackerHarness_NodesAllowlist.tla

attacker-nodes-allowlist-negative:
	$(TLC) -workers auto -deadlock -config tla/models/attacker_nodes_allowlist_negative.cfg tla/specs/AttackerHarness_NodesAllowlist.tla

# Approvals lifecycle (nodes.run)
approvals:
	$(TLC) -workers auto -deadlock -config tla/models/approvals_ok.cfg tla/specs/AttackerHarness_Approvals.tla

approvals-negative:
	$(TLC) -workers auto -deadlock -config tla/models/approvals_negative_ignore_approval.cfg tla/specs/AttackerHarness_Approvals_BadIgnoresApproval.tla

# Tokenized per-request approvals (prevents replay)
approvals-token:
	$(TLC) -workers auto -deadlock -config tla/models/approvals_token_ok.cfg tla/specs/AttackerHarness_ApprovalsToken.tla

approvals-token-negative:
	$(TLC) -workers auto -deadlock -config tla/models/approvals_token_negative_replay.cfg tla/specs/AttackerHarness_ApprovalsToken_BadReplay.tla

# Composed nodes.run pipeline harness (allowlist + declared + tokenized approval)
nodes-pipeline:
	$(TLC) -workers auto -deadlock -config tla/models/nodes_pipeline_ok.cfg tla/specs/NodesPipelineHarness.tla

nodes-pipeline-negative:
	$(TLC) -workers auto -deadlock -config tla/models/nodes_pipeline_negative_replay.cfg tla/specs/NodesPipelineHarness_BadReplay.tla
