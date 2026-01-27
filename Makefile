TLC=./bin/tlc
MODEL?=tla/models/basic.cfg

.PHONY: tlc precedence precedence-negative groups groups-negative elevated elevated-negative nodes-policy nodes-policy-negative attacker attacker-negative attacker-nodes-negative attacker-nodes-allowlist attacker-nodes-allowlist-negative approvals approvals-negative approvals-token approvals-token-negative nodes-pipeline nodes-pipeline-negative gateway-exposure gateway-exposure-negative gateway-exposure-v2 gateway-exposure-v2-negative gateway-exposure-v2-protected gateway-exposure-v2-protected-negative gateway-exposure-v2-unsafe-custom gateway-exposure-v2-unsafe-tailnet gateway-exposure-v2-protected-custom gateway-exposure-v2-protected-tailnet gateway-exposure-v2-protected-password gateway-exposure-v2-unsafe-auto gateway-exposure-v2-protected-auto gateway-auth-conformance gateway-auth-conformance-negative gateway-auth-tailscale gateway-auth-tailscale-negative gateway-auth-proxy gateway-auth-proxy-negative pairing pairing-negative pairing-cap pairing-cap-negative pairing-idempotency pairing-idempotency-negative pairing-refresh pairing-refresh-negative pairing-refresh-race pairing-refresh-race-negative ingress-gating ingress-gating-negative ingress-idempotency ingress-idempotency-negative ingress-dedupe-fallback ingress-dedupe-fallback-negative ingress-trace ingress-trace-negative ingress-trace2 ingress-trace2-negative routing-isolation routing-isolation-negative routing-precedence routing-precedence-negative pairing-race pairing-race-negative routing-identitylinks routing-identitylinks-negative

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

# Gateway exposure / no-auth beyond loopback

gateway-exposure:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_exposure_safe.cfg tla/specs/GatewayExposureHarness.tla

gateway-exposure-negative:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_exposure_unsafe.cfg tla/specs/GatewayExposureHarness.tla

# Refined gateway exposure model (real bind modes + auth auto)
gateway-exposure-v2:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_exposure_v2_safe_loopback.cfg tla/specs/GatewayExposureHarnessV2.tla

gateway-exposure-v2-negative:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_exposure_v2_unsafe_lan_noauth.cfg tla/specs/GatewayExposureHarnessV2.tla

# Protected: non-loopback with token/password configured blocks unauth attacker

gateway-exposure-v2-protected:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_exposure_v2_protected_lan_token_no_creds.cfg tla/specs/GatewayExposureHarnessV2.tla

# Credentialed attacker can still connect (expected reachability)
gateway-exposure-v2-protected-negative:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_exposure_v2_protected_lan_token_with_creds.cfg tla/specs/GatewayExposureHarnessV2.tla

# More gateway exposure v2 cases

gateway-exposure-v2-unsafe-custom:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_exposure_v2_unsafe_custom_noauth.cfg tla/specs/GatewayExposureHarnessV2.tla

gateway-exposure-v2-unsafe-tailnet:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_exposure_v2_unsafe_tailnet_noauth.cfg tla/specs/GatewayExposureHarnessV2.tla

gateway-exposure-v2-protected-custom:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_exposure_v2_protected_custom_token_no_creds.cfg tla/specs/GatewayExposureHarnessV2.tla

gateway-exposure-v2-protected-tailnet:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_exposure_v2_protected_tailnet_token_no_creds.cfg tla/specs/GatewayExposureHarnessV2.tla

gateway-exposure-v2-protected-password:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_exposure_v2_protected_lan_password_no_creds.cfg tla/specs/GatewayExposureHarnessV2.tla

gateway-exposure-v2-unsafe-auto:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_exposure_v2_unsafe_auto_noauth.cfg tla/specs/GatewayExposureHarnessV2.tla

gateway-exposure-v2-protected-auto:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_exposure_v2_protected_auto_token_no_creds.cfg tla/specs/GatewayExposureHarnessV2.tla

# Gateway auth conformance harness (code-shaped)

gateway-auth-conformance:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_auth_conformance_safe.cfg tla/specs/GatewayAuthConformanceHarness.tla

gateway-auth-conformance-negative:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_auth_conformance_unsafe.cfg tla/specs/GatewayAuthConformanceHarness.tla

# Gateway auth tailscale spoof harness

gateway-auth-tailscale:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_auth_tailscale_green.cfg tla/specs/GatewayAuthTailscaleHarness.tla

gateway-auth-tailscale-negative:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_auth_tailscale_red.cfg tla/specs/GatewayAuthTailscaleHarness_BadSpoof.tla

# Gateway auth trusted-proxy / forwarded-header spoof harness

gateway-auth-proxy:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_auth_proxy_green.cfg tla/specs/GatewayAuthTrustedProxyHarness.tla

gateway-auth-proxy-negative:
	$(TLC) -workers auto -deadlock -config tla/models/gateway_auth_proxy_red.cfg tla/specs/GatewayAuthTrustedProxyHarness_BadSpoof.tla

# Pairing store harness (R1)

pairing:
	$(TLC) -workers 1 -deadlock -config tla/models/pairing_v2_ok.cfg tla/specs/PairingStoreHarnessV2.tla

pairing-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/pairing_v2_negative_badexpiry.cfg tla/specs/PairingStoreHarnessV2_BadExpiry.tla

# Pairing cap harness (MaxPending)

pairing-cap:
	$(TLC) -workers 1 -deadlock -config tla/models/pairing_v2_cap_ok.cfg tla/specs/PairingStoreHarnessV2.tla

pairing-cap-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/pairing_v2_cap_negative.cfg tla/specs/PairingStoreHarnessV2_BadNoCap.tla

# Pairing idempotency harness (R1++)

pairing-idempotency:
	$(TLC) -workers 1 -deadlock -config tla/models/pairing_idempotency_ok.cfg tla/specs/PairingStoreIdempotencyHarness.tla

pairing-idempotency-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/pairing_idempotency_negative.cfg tla/specs/PairingStoreIdempotencyHarness_BadDuplicates.tla

# Pairing refresh enablement harness (R1+++)

pairing-refresh:
	$(TLC) -workers 1 -deadlock -config tla/models/pairing_refresh_enabled_ok.cfg tla/specs/PairingStoreRefreshEnabledHarness.tla

pairing-refresh-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/pairing_refresh_enabled_negative.cfg tla/specs/PairingStoreRefreshEnabledHarness_BadCapOnRefresh.tla

# Pairing refresh race harness (R1++++)

pairing-refresh-race:
	$(TLC) -workers 1 -deadlock -config tla/models/pairing_refresh_race_ok.cfg tla/specs/PairingStoreRefreshRaceHarness.tla

pairing-refresh-race-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/pairing_refresh_race_negative.cfg tla/specs/PairingStoreRefreshRaceHarness_BadNonAtomic.tla

# Ingress gating harness (R2)

ingress-gating:
	$(TLC) -workers 1 -deadlock -config tla/models/ingress_gating_ok.cfg tla/specs/IngressGatingHarness.tla

ingress-gating-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/ingress_gating_negative.cfg tla/specs/IngressGatingHarness_BadBypass.tla

# Ingress provider event idempotency/de-dupe (R2++++)

ingress-idempotency:
	$(TLC) -workers 1 -deadlock -config tla/models/ingress_idempotency_ok.cfg tla/specs/IngressEventIdempotencyHarness.tla

ingress-idempotency-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/ingress_idempotency_negative.cfg tla/specs/IngressEventIdempotencyHarness_BadNoDedupe.tla

# Ingress dedupe key fallback when eventId is missing (R2+++++)

ingress-dedupe-fallback:
	$(TLC) -workers 1 -deadlock -config tla/models/ingress_dedupe_fallback_ok.cfg tla/specs/IngressDedupeKeyFallbackHarness.tla

ingress-dedupe-fallback-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/ingress_dedupe_fallback_negative.cfg tla/specs/IngressDedupeKeyFallbackHarness_BadNoFallback.tla

# Ingress multi-message trace correlation harness (R2++)

ingress-trace:
	$(TLC) -workers 1 -deadlock -config tla/models/ingress_multimsg_trace_ok.cfg tla/specs/IngressMultiMessageTraceHarness.tla

ingress-trace-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/ingress_multimsg_trace_negative.cfg tla/specs/IngressMultiMessageTraceHarness_BadMissingTrace.tla

# Ingress multi-event trace correlation harness (R2+++)

ingress-trace2:
	$(TLC) -workers 1 -deadlock -config tla/models/ingress_multievent_trace_ok.cfg tla/specs/IngressMultiEventTraceHarness.tla

ingress-trace2-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/ingress_multievent_trace_negative.cfg tla/specs/IngressMultiEventTraceHarness_BadCrossStream.tla

# Routing/session-key isolation harness (R3)

routing-isolation:
	$(TLC) -workers 1 -deadlock -config tla/models/routing_isolation_ok.cfg tla/specs/RoutingIsolationHarness.tla

routing-isolation-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/routing_isolation_negative.cfg tla/specs/RoutingIsolationHarness_BadAlwaysMain.tla

# Routing precedence harness (R3++)

routing-precedence:
	$(TLC) -workers 1 -deadlock -config tla/models/routing_precedence_ok.cfg tla/specs/RoutingPrecedenceHarness.tla

routing-precedence-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/routing_precedence_negative.cfg tla/specs/RoutingPrecedenceHarness_BadIgnoresChannelOverride.tla

# Pairing store concurrency/race harness (v1++)

pairing-race:
	$(TLC) -workers 1 -deadlock -config tla/models/pairing_concurrent_ok.cfg tla/specs/PairingStoreConcurrentHarness_Locked.tla

pairing-race-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/pairing_concurrent_negative.cfg tla/specs/PairingStoreConcurrentHarness.tla

# Routing identityLinks harness (R3++)

routing-identitylinks:
	$(TLC) -workers 1 -deadlock -config tla/models/routing_identitylinks_ok.cfg tla/specs/RoutingIdentityLinksHarness.tla

routing-identitylinks-negative:
	$(TLC) -workers 1 -deadlock -config tla/models/routing_identitylinks_negative.cfg tla/specs/RoutingIdentityLinksHarness_BadCanonical.tla
