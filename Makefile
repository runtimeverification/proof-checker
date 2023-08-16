all: check test-unit test-system test-zk
.PHONY: all
FORCE:


# Syntax and formatting checks
# ============================

check: check-cargo check-python
check-cargo:
	cargo fmt --check
check-python:
	make -C generation check
	make -C generation pyupgrade

.PHONY: check check-cargo check-python

format: format-cargo format-python
format-cargo:
	cargo fmt
format-python:
	make -C generation format

.PHONY: format format-cargo format-python


# Unit testing
# ============

test-unit: test-unit-python test-unit-cargo
test-unit-cargo:
	cargo test
test-unit-python:
	make -C generation test-unit

.PHONY: test-unit test-unit-cargo test-unit-python


# System testing
# ==============

test-system: test-proof-gen test-proof-verify
.PHONY: test-proof-gen test-proof-verify test-risc0

PROOFS=$(wildcard proofs/*.ml-proof)


# Proof generation
# ----------------

PROOF_GEN_TARGETS=$(addsuffix .gen,${PROOFS})
.build/proofs/%.ml-proof: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m "proof_generation.proofs.$*"  ".build/proofs/$*.ml-claim" "$@"

CHECK_PROOF=./bin/proof-diff
proofs/%.ml-proof.gen: .build/proofs/%.ml-proof FORCE
	${CHECK_PROOF} ".build/proofs/$*.ml-claim" "proofs/$*.ml-claim"
	${CHECK_PROOF} ".build/proofs/$*.ml-proof" "proofs/$*.ml-proof"


test-proof-gen: ${PROOF_GEN_TARGETS}

# Proof checking
# ----------------

PROOF_VERIFY_TARGETS=$(addsuffix .verify,${PROOFS})
proofs/%.ml-proof.verify: proofs/%.ml-proof
	cargo run --bin checker $< proofs/$*.ml-claim

test-proof-verify: ${PROOF_VERIFY_TARGETS}

PROOF_VERIFY_BUILD_TARGETS=$(addsuffix .verify,.build/${PROOFS})
.build/proofs/%.ml-proof.verify: .build/proofs/%.ml-proof FORCE
	cargo run --bin checker $< .build/proofs/$*.ml-claim

proof-verify: ${PROOF_VERIFY_BUILD_TARGETS}

# Risc0
# -----

PROOF_ZK_TARGETS=$(addsuffix .zk,${PROOFS})
proofs/%.ml-proof.zk: proofs/%.ml-proof
	cargo run --bin host $^ proofs/$*.ml-claim

test-zk: ${PROOF_ZK_TARGETS}
