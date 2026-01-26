# Gateway Exposure Matrix (formal models)

This doc summarizes the runnable TLC cases for the “gateway exposed with zero auth”
incident class.

Run all commands from the repo root with Java on PATH:

```bash
export PATH="/opt/homebrew/opt/openjdk@21/bin:$PATH"
```

## Unsafe (expected to FAIL with counterexample)

These represent configurations where a remote attacker can connect and invoke a
sensitive tool.

- `make gateway-exposure-v2-negative` (lan + auth none)
- `make gateway-exposure-v2-unsafe-custom` (custom + auth none)
- `make gateway-exposure-v2-unsafe-tailnet` (tailnet + auth none)
- `make gateway-exposure-v2-unsafe-auto` (auto + auth none; modeled as non-loopback)

## Protected (expected to PASS for unauth attacker)

- `make gateway-exposure-v2-protected` (lan + token, attacker has no creds)
- `make gateway-exposure-v2-protected-custom` (custom + token, no creds)
- `make gateway-exposure-v2-protected-tailnet` (tailnet + token, no creds)
- `make gateway-exposure-v2-protected-password` (lan + password, no creds)
- `make gateway-exposure-v2-protected-auto` (auto + token, no creds)

## Credentialed attacker (expected to FAIL)

These show that if an attacker has valid credentials, they can connect.
This is expected and helps distinguish “exposed” vs “open.”

- `make gateway-exposure-v2-protected-negative` (lan + token, attacker has creds)
