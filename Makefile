all:    check test-unit test-system
.PHONY: all
FORCE:


# Syntax and formatting checks
# ============================

check: check-cargo check-python
check-cargo:
	cargo fmt --check
check-python:
	make -C generation check

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

test-system: test-proof-gen test-zk
.PHONY: test-proof-gen test-proof-check test-risc0

PROOFS=$(wildcard proofs/*.ml-proof)


# Proof generation
# ----------------

PROOF_GEN_TARGETS=$(addsuffix .gen,${PROOFS})

.build/proofs/%.ml-proof: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m proof_generation.proofs.$* "$@"

CHECK_PROOF=./bin/proof-diff
proofs/%.ml-proof.gen: .build/proofs/%.ml-proof proofs/%.ml-proof
	${CHECK_PROOF} $^

test-proof-gen: ${PROOF_GEN_TARGETS}

# Risc0
# -----

PROOF_ZK_TARGETS=$(addsuffix .zk,${PROOFS})

proofs/%.ml-proof.zk: proofs/%.ml-proof
	cargo run --bin host  $^

test-zk: ${PROOF_ZK_TARGETS}

