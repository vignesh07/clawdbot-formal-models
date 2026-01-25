# clawdbot-formal-models

Formal models of **Clawdbot security protocols**, with a focus on:

- tool-gating (what actions are allowed from which channels/providers)
- memory isolation (what can be read/written in which session types)
- external side-effects (messaging, browser control, gateway config/update)
- approval / escalation paths ("ask-first" boundaries, elevated execution)

This repo currently contains a **TLA+** model-checking setup (CLI TLC via `tla2tools.jar`).

## Quickstart (TLA+)

Prereqs:
- Java 11+ (Java 21 works)

Run TLC:

```bash
./bin/tlc -workers auto -deadlock tla/specs/ClawdbotSecurity.tla
```

## Structure

- `tla/specs/` — TLA+ specs
- `tla/models/` — TLC model configs / notes
- `tools/tla/` — pinned TLA+ tool jar (`tla2tools.jar`)
- `bin/tlc` — convenience wrapper around TLC
- `docs/` — design notes and threat-models

## Next steps

1. Encode a minimal security state machine (sessions, providers, tools).
2. Add invariants for non-leakage + tool gating.
3. Add liveness where it matters (e.g., approvals eventually resolve).
4. Iterate with counterexamples until the invariants match intent.
