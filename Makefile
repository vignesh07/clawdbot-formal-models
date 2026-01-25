TLC=./bin/tlc

.PHONY: tlc

# Run the base spec (no TLC config yet)

tlc:
	$(TLC) -workers auto -deadlock -config tla/models/default.cfg tla/specs/ClawdbotSecurity.tla
