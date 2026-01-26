------------------------------ MODULE GatewayAuthTailscaleHarness ------------------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* GatewayAuthTailscaleHarness.tla
*
* Bounded micro-harness for the tailscale proxy authorization path.
*
* Intent (from src/gateway/auth.ts):
* - If allowTailscale is enabled and the request is NOT localDirect,
*   then a request with auth.mode=none must present:
*     (a) tailscale user identity headers, AND
*     (b) tailscale proxy headers (x-forwarded-for/proto/host)
*   otherwise reject.
*
* We model only what we need for this property.
******************************************************************************)

CONSTANTS
  BindResolved,          \* "loopback"|"non-loopback"
  AuthMode,              \* "none"|"token"|"password"
  AllowTailscale,        \* BOOLEAN

  LocalDirect,           \* BOOLEAN
  HasTailscaleUser,      \* BOOLEAN
  HasTailscaleProxyHdrs, \* BOOLEAN

  HasCredential           \* BOOLEAN

ASSUME
  /\ BindResolved \in {"loopback","non-loopback"}
  /\ AuthMode \in {"none","token","password"}
  /\ AllowTailscale \in BOOLEAN
  /\ LocalDirect \in BOOLEAN
  /\ HasTailscaleUser \in BOOLEAN
  /\ HasTailscaleProxyHdrs \in BOOLEAN
  /\ HasCredential \in BOOLEAN

VARIABLES connected, invoked
vars == << connected, invoked >>

TailscaleOk == HasTailscaleUser /\ HasTailscaleProxyHdrs

Authorize ==
  IF BindResolved = "loopback" THEN FALSE
  ELSE IF AuthMode = "token" \/ AuthMode = "password" THEN HasCredential
  ELSE \* AuthMode = none
    IF AllowTailscale /\ ~LocalDirect THEN TailscaleOk ELSE TRUE

Init == /\ connected = FALSE /\ invoked = FALSE

Connect ==
  /\ ~connected
  /\ connected' = Authorize
  /\ UNCHANGED invoked

InvokeSensitive ==
  /\ connected
  /\ ~invoked
  /\ invoked' = TRUE
  /\ UNCHANGED connected

Next == Connect \/ InvokeSensitive
Spec == Init /\ [][Next]_vars

Inv_NotInvoked == ~invoked

=============================================================================
