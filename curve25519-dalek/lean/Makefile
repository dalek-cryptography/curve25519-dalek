.PHONY: all gen build check lint axioms definitions coverage shake translate

all: build

# Regenerate the per-configuration copies from the x86_64-tables templates.
gen:
	python3 scripts/gen-config-specs.py

# Build everything, including the axiom, definition and coverage checks.
build: gen
	lake exe cache get
	lake build Aeneas
	lake build --wfail

# What CI runs.
check:
	python3 scripts/gen-config-specs.py --check
	lake exe cache get
	lake build Aeneas
	lake build --wfail
	lake exe runLinter ForHumans
	lake exe runLinter Proofs

lint:
	lake exe runLinter ForHumans
	lake exe runLinter Proofs

# One check at a time; silent when it passes.
axioms: gen
	lake env lean ForHumans/Theorems/Axioms.lean
definitions: gen
	lake env lean ForHumans/Theorems/Definitions.lean
coverage: gen
	lake env lean ForHumans/Theorems/Coverage.lean

shake:
	lake shake ForHumans

translate:
	scripts/aeneas-install.sh
	scripts/aeneas-translate.sh
