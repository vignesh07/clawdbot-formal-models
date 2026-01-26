------------------------------ MODULE GatewayAuthTailscaleHarness_BadSpoof ------------------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* BUG: accepts tailscale user header without requiring proxy headers.
******************************************************************************)

CONSTANTS
  BindResolved, AuthMode, AllowTailscale, LocalDirect,
  HasTailscaleUser, HasTailscaleProxyHdrs, HasCredential

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

\* BUG: ignores HasTailscaleProxyHdrs
TailscaleOk == HasTailscaleUser

Authorize ==
  IF BindResolved = "loopback" THEN FALSE
  ELSE IF AuthMode = "token" \/ AuthMode = "password" THEN HasCredential
  ELSE IF AllowTailscale /\ ~LocalDirect THEN TailscaleOk ELSE TRUE

Init == /\ connected = FALSE /\ invoked = FALSE
Connect == /\ ~connected /\ connected' = Authorize /\ UNCHANGED invoked
InvokeSensitive == /\ connected /\ ~invoked /\ invoked' = TRUE /\ UNCHANGED connected
Next == Connect \/ InvokeSensitive
Spec == Init /\ [][Next]_vars
Inv_NotInvoked == ~invoked

=============================================================================
