all: check test-unit test-system test-zk
.PHONY: all
.SECONDARY:
FORCE:

clean-proofs:
	rm -rf .build/proofs

clean-translated-proofs:
	rm -rf .build/proofs/translated

update-snapshots:
	cp -rT .build/proofs proofs

.PHONY: clean-proofs update-snapshots clean-translated-proofs

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

test-system: test-proof-gen test-proof-translate test-proof-verify
.PHONY: test-system test-proof-gen test-proof-verify test-zk

PROOFS_FILES := $(wildcard proofs/*)
PROOFS := $(filter %.ml-proof,$(PROOFS_FILES))
TRANSLATED_PROOFS=$(wildcard proofs/translated/*.ml-proof)


# Proof conversion checking
# -------------------------

.build/proofs/translated/%.ml-proof: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m "mm_transfer.transfer" generation/mm-benchmarks/$*.mm .build/proofs/translated/$* goal

PROOF_TRANSLATION_TARGETS=$(addsuffix .translate,${TRANSLATED_PROOFS})
proofs/translated/%.ml-proof.translate: .build/proofs/translated/%.ml-proof
	${BIN_DIFF} "proofs/translated/$*.ml-gamma" ".build/proofs/translated/$*/$*.ml-gamma"
	${BIN_DIFF} "proofs/translated/$*.ml-claim" ".build/proofs/translated/$*/$*.ml-claim"
	${BIN_DIFF} "proofs/translated/$*.ml-proof" ".build/proofs/translated/$*/$*.ml-proof"

test-proof-translate: ${PROOF_TRANSLATION_TARGETS}


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


# Proof checking
# ----------------

PROOF_VERIFY_SNAPSHOT_TARGETS=$(addsuffix .verify,${PROOFS})
proofs/%.ml-proof.verify: proofs/%.ml-proof
	cargo run --release --bin checker proofs/$*.ml-gamma proofs/$*.ml-claim $<

TRANSLATED_PROOF_VERIFY_SNAPSHOT_TARGETS=$(addsuffix .verify,${TRANSLATED_PROOFS})
proofs/translated/%.ml-proof.verify: proofs/translated/%.ml-proof
	cargo run --bin checker proofs/translated/$*.ml-gamma proofs/translated/$*.ml-claim $<

test-proof-verify-translated: ${TRANSLATED_PROOF_VERIFY_SNAPSHOT_TARGETS}
.PHONY: test-proof-verify-translated

test-proof-verify: ${PROOF_VERIFY_SNAPSHOT_TARGETS} ${TRANSLATED_PROOF_VERIFY_SNAPSHOT_TARGETS}

PROOF_VERIFY_BUILD_TARGETS=$(addsuffix .verify-generated,${PROOFS})
proofs/%.ml-proof.verify-generated: .build/proofs/%.ml-gamma .build/proofs/%.ml-claim .build/proofs/%.ml-proof
	cargo run --release --bin checker .build/proofs/$*.ml-gamma .build/proofs/$*.ml-claim .build/proofs/$*.ml-proof

verify-generated: clean-proofs ${PROOF_VERIFY_BUILD_TARGETS}
.PHONY: verify-generated


# Profiling
# ---------

PROFILING_TARGETS=$(addsuffix .profile,${PROOFS})
proofs/%.ml-proof.profile: .build/proofs/%.ml-gamma .build/proofs/%.ml-claim .build/proofs/%.ml-proof
	cargo build --release --bin profiler
	flamegraph -- .build/target/release/profiler .build/proofs/$*.ml-gamma .build/proofs/$*.ml-claim .build/proofs/$*.ml-proof
	cp flamegraph.svg $*.svg
	rm flamegraph.svg
	rm perf.data

profile: ${PROFILING_TARGETS}

# Risc0
# -----

PROOF_ZK_TARGETS=$(addsuffix .zk,${PROOFS})
proofs/%.ml-proof.zk: proofs/%.ml-proof
	cargo run --release --bin host proofs/$*.ml-gamma proofs/$*.ml-claim $^

test-zk: ${PROOF_ZK_TARGETS}

# Run checker on converted files in the ZK mode
TRANSLATED_PROOF_ZK_TARGETS=$(addsuffix .zk-translated,${TRANSLATED_PROOFS})
proofs/translated/%.ml-proof.zk-translated: proofs/translated/%.ml-proof
	cargo run --release --bin host proofs/translated/$*.ml-gamma proofs/translated/$*.ml-claim $<

test-translated-zk: ${TRANSLATED_PROOF_ZK_TARGETS}

# Clean translated proofs, translate them, then run checker and then run the ZK checker
test-translated-zk-all: clean-translated-proofs test-proof-verify-translated test-translated-zk

# Output file for one-liner
OUTPUT_FILE=zk-report.txt

# Reset the output file
reset-output:
	@rm -f $(OUTPUT_FILE)
	@touch $(OUTPUT_FILE)

# Run host and collect the output
proofs/translated/%.ml-proof.zk-translated-ol: proofs/translated/%.ml-proof reset-output
	@echo "Processing: $*.ml-proof" >> $(OUTPUT_FILE)
	@{ \
	output=$$(cargo run --release --bin host proofs/translated/$*.ml-gamma proofs/translated/$*.ml-claim $<) ; \
	echo "$$output" | grep -E "Reading files:|Verifying the theorem:|Overall \(environment setup, reading files, and verification\):|Running execution \+ ZK certficate generation \+ verification took" >> $(OUTPUT_FILE) ; \
	echo "$* .ml-gamma proofs/translated/$* .ml-claim $<" >> $(OUTPUT_FILE) ; \
	echo "$$output" | grep -E "Reading files:|Verifying the theorem:|Overall \(environment setup, reading files, and verification\):|Running execution \+ ZK certficate generation \+ verification took" ; \
	echo "" >> $(OUTPUT_FILE) ; \
	} ; true

TRANSLATED_PROOF_ZK_TARGETS_OL=$(addsuffix .zk-translated-ol,${TRANSLATED_PROOFS})
test-translated-zk-all-ol: ${TRANSLATED_PROOF_ZK_TARGETS_OL}
	@cat $(OUTPUT_FILE)

# New combined target
test-translated-report: clean-translated-proofs test-proof-verify-translated test-translated-zk-all-ol
