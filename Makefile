TLC=./bin/tlc
MODEL?=tla/models/basic.cfg

.PHONY: tlc precedence precedence-negative groups groups-negative elevated elevated-negative nodes-policy nodes-policy-negative

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
