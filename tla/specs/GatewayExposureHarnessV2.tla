------------------------------ MODULE GatewayExposureHarnessV2 ------------------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* GatewayExposureHarnessV2.tla
*
* Refines GatewayExposureHarness to model real bind modes:
*   loopback | lan | auto | custom | tailnet
*
* And models resolved auth mode similar to resolveGatewayAuth:
*   - modeConfig can be "none"|"token"|"password"|"auto"
*   - when "auto": password wins, else token, else none.
*
* We keep this as an attacker-driven reachability model:
*   Remote attacker attempts Connect then InvokeSensitive.
*
* We also model audit finding gateway.bind_no_auth when bind resolves beyond
* loopback and auth resolves to none.
******************************************************************************)

CONSTANTS
  BindMode,        \* "loopback"|"lan"|"auto"|"custom"|"tailnet"
  ModeConfig,      \* "auto"|"none"|"token"|"password"
  HasToken,        \* BOOLEAN
  HasPassword,     \* BOOLEAN
  HasCredential    \* BOOLEAN (attacker presents correct token/password)

ASSUME
  /\ BindMode \in {"loopback","lan","auto","custom","tailnet"}
  /\ ModeConfig \in {"auto","none","token","password"}
  /\ HasToken \in BOOLEAN
  /\ HasPassword \in BOOLEAN
  /\ HasCredential \in BOOLEAN

VARIABLES connected, invokedSensitive, auditFindings, resolvedBind, resolvedMode
vars == << connected, invokedSensitive, auditFindings, resolvedBind, resolvedMode >>

\* Resolve bind coarsely to whether remote can reach it.
\* - loopback => loopback
\* - lan/custom/tailnet => non-loopback
\* - auto => may resolve either way (nondeterministic)
ResolveBind ==
  CASE BindMode = "loopback" -> "loopback"
    [] BindMode = "lan" -> "non-loopback"
    [] BindMode = "custom" -> "non-loopback"
    [] BindMode = "tailnet" -> "non-loopback"
    [] BindMode = "auto" -> "non-loopback"

\* Resolve auth mode like resolveGatewayAuth (simplified)
ResolveMode ==
  IF ModeConfig = "none" THEN "none"
  ELSE IF ModeConfig = "token" THEN "token"
  ELSE IF ModeConfig = "password" THEN "password"
  ELSE \* auto
    IF HasPassword THEN "password" ELSE IF HasToken THEN "token" ELSE "none"

Authorize ==
  IF resolvedBind = "loopback" THEN FALSE
  ELSE IF resolvedMode = "none" THEN TRUE
  ELSE HasCredential

AuditBindNoAuth == (resolvedBind = "non-loopback") /\ (resolvedMode = "none")

Init ==
  /\ connected = FALSE
  /\ invokedSensitive = FALSE
  /\ auditFindings = << >>
  /\ resolvedBind = ResolveBind
  /\ resolvedMode = ResolveMode

AttackerConnect ==
  /\ ~connected
  /\ connected' = Authorize
  /\ auditFindings' = IF AuditBindNoAuth THEN Append(auditFindings, "gateway.bind_no_auth") ELSE auditFindings
  /\ UNCHANGED << invokedSensitive, resolvedBind, resolvedMode >>

AttackerInvokeSensitive ==
  /\ connected
  /\ ~invokedSensitive
  /\ invokedSensitive' = TRUE
  /\ UNCHANGED << connected, auditFindings, resolvedBind, resolvedMode >>

Next == AttackerConnect \/ AttackerInvokeSensitive

Spec == Init /\ [][Next]_vars

Inv_NotCompromised == ~invokedSensitive

Inv_AuditFlagsOpenGateway ==
  AuditBindNoAuth => (connected => (\E i \in 1..Len(auditFindings): auditFindings[i] = "gateway.bind_no_auth"))

=============================================================================
