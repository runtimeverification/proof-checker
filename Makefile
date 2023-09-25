all: check test-unit test-system test-zk
.PHONY: all
.SECONDARY:
FORCE:

clean-proofs:
	rm -rf .build/proofs

update-snapshots:
	cp -rT .build/proofs proofs

.PHONY: clean-proofs update-snapshots

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

test-system: test-proof-gen test-proof-verify test-proof-translate
.PHONY: test-system test-proof-gen test-proof-verify test-zk

PROOFS=$(wildcard proofs/*.ml-proof)
TRANSLATED_PROOFS=$(wildcard translated-proofs/*.ml-proof)


# Proof generation
# ----------------

.build/proofs/%.ml-proof: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m "proof_generation.proofs.$*" binary proof $@

.build/proofs/%.ml-claim: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m "proof_generation.proofs.$*" binary claim $@

.build/proofs/%.ml-gamma: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m "proof_generation.proofs.$*" binary gamma $@

.build/proofs/%.pretty-proof: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m "proof_generation.proofs.$*" pretty proof $@

.build/proofs/%.pretty-claim: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m "proof_generation.proofs.$*" pretty claim $@

.build/proofs/%.pretty-gamma: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m "proof_generation.proofs.$*" pretty gamma $@

PROOF_GEN_TARGETS=$(addsuffix .gen,${PROOFS})
BIN_DIFF=./bin/proof-diff
DIFF=colordiff -U3
proofs/%.ml-proof.gen: .build/proofs/%.ml-proof .build/proofs/%.ml-claim .build/proofs/%.ml-gamma .build/proofs/%.pretty-proof .build/proofs/%.pretty-claim .build/proofs/%.pretty-gamma
	${DIFF} --label expected "proofs/$*.pretty-claim" --label actual ".build/proofs/$*.pretty-claim"
	${DIFF} --label expected "proofs/$*.pretty-proof" --label actual ".build/proofs/$*.pretty-proof"
	${DIFF} --label expected "proofs/$*.pretty-gamma" --label actual ".build/proofs/$*.pretty-gamma"
	${BIN_DIFF} "proofs/$*.ml-claim" ".build/proofs/$*.ml-claim"
	${BIN_DIFF} "proofs/$*.ml-proof" ".build/proofs/$*.ml-proof"
	${BIN_DIFF} "proofs/$*.ml-gamma" ".build/proofs/$*.ml-gamma"

test-proof-gen: ${PROOF_GEN_TARGETS}


# Proof translation
# -----------------
.build/translated-proofs/%.ml-proof: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m "mm_transfer.transfer" generation/mm-benchmarks/$*.mm .build/translated-proofs/$* goal

PROOF_TRANSLATION_TARGETS=$(addsuffix .translate,${TRANSLATED_PROOFS})
translated-proofs/%.ml-proof.translate: .build/translated-proofs/%.ml-proof
	${BIN_DIFF} "translated-proofs/$*.ml-claim" ".build/translated-proofs/$*/$*.ml-claim"
	${BIN_DIFF} "translated-proofs/$*.ml-proof" ".build/translated-proofs/$*/$*.ml-proof"
	${BIN_DIFF} "translated-proofs/$*.ml-gamma" ".build/translated-proofs/$*/$*.ml-gamma"

test-proof-translate: ${PROOF_TRANSLATION_TARGETS}

# Proof checking
# ----------------

PROOF_VERIFY_SNAPSHOT_TARGETS=$(addsuffix .verify,${PROOFS})
proofs/%.ml-proof.verify: proofs/%.ml-proof
	cargo run --bin checker proofs/$*.ml-gamma proofs/$*.ml-claim $<

TRANSLATED_PROOF_VERIFY_SNAPSHOT_TARGETS=$(addsuffix .verify,${TRANSLATED_PROOFS})
translated-proofs/%.ml-proof.verify: translated-proofs/%.ml-proof
	cargo run --bin checker translated-proofs/$*.ml-gamma translated-proofs/$*.ml-claim $<

test-proof-verify: ${PROOF_VERIFY_SNAPSHOT_TARGETS} ${TRANSLATED_PROOF_VERIFY_SNAPSHOT_TARGETS}

PROOF_VERIFY_BUILD_TARGETS=$(addsuffix .verify-generated,${PROOFS})
proofs/%.ml-proof.verify-generated: .build/proofs/%.ml-gamma .build/proofs/%.ml-claim .build/proofs/%.ml-proof
	cargo run --bin checker .build/proofs/$*.ml-gamma .build/proofs/$*.ml-claim .build/proofs/$*.ml-proof

verify-generated: clean-proofs ${PROOF_VERIFY_BUILD_TARGETS}
.PHONY: verify-generated

# Proof conversion checking
# -------------------------

CONV_DIR=.build/proofs/conv

#TODO: Add all examples
#SLICES=$(wildcard generation/mm-benchmarks/*.mm)
SLICES=generation/mm-benchmarks/impreflex.mm
SLICE_CONV_TARGETS=$(addsuffix .conv,${SLICES})

${CONV_DIR}/%/%.ml-proof: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m "mm_transfer.transfer" generation/mm-benchmarks/$*.mm $(dir $@) > /dev/null

generation/mm-benchmarks/%.mm.conv: ${CONV_DIR}/%/%.ml-proof
	cargo run --release --bin checker ${CONV_DIR}/$*/$*.ml-gamma ${CONV_DIR}/$*/$*.ml-claim ${CONV_DIR}/$*/$*.ml-proof

test-mm-conv: ${SLICE_CONV_TARGETS}


# Risc0
# -----

PROOF_ZK_TARGETS=$(addsuffix .zk,${PROOFS})
proofs/%.ml-proof.zk: proofs/%.ml-proof
	cargo run --release --bin host proofs/$*.ml-gamma proofs/$*.ml-claim $^

test-zk: ${PROOF_ZK_TARGETS}
