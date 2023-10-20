all: check test-unit test-system test-zk
.PHONY: all
.SECONDARY:
FORCE:

clean-proofs:
	rm -rf .build/proofs

clean-translated-proofs:
	rm -rf .build/proofs/translated

clean-kgenerated-proofs:
	rm -rf .build/proofs/generated-from-k

update-snapshots:
	rsync -u $(wildcard .build/proofs/*.*) proofs
	rsync -u $(wildcard .build/proofs/translated/*/*.ml*) proofs/translated

.PHONY: clean-proofs update-snapshots clean-translated-proofs clean-kgenerated-proofs

# Installation and setup
# ======================

build-checker:
	cargo build --manifest-path=checker/Cargo.toml

build-risc0:
	cargo build --manifest-path=risc0/Cargo.toml

generation-install:
	make -C generation poetry-install

install-kup:
	@if ! command -v kup &> /dev/null; then \
		echo "kup is not installed, installing..."; \
		curl https://kframework.org/install | bash; \
	else \
		echo "kup is already installed, skipping installation."; \
	fi

k-version-output := $(shell make -C generation k-version)
install-k-kup:
	@if ! command -v kompile &> /dev/null; then \
		echo "K is not installed, installing..."; \
		kup install k --version v$(k-version-output); \
	else \
		echo "K is already installed, skipping installation."; \
	fi

build: build-checker build-risc0 generation-install

install-k: install-kup install-k-kup

.PHONY: build-checker build-risc0 generation-install install-kup install-k install-k-kup build

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


# Setup
# =====

ARCH := $(shell uname -m)
ifeq ($(ARCH),arm64)
    CARGO := cargo +nightly-2023-03-06-aarch64-apple-darwin
else
    CARGO := cargo
endif


# Unit testing
# ============

test-unit: test-unit-python test-unit-cargo
test-unit-cargo:
	$(CARGO) test
test-unit-python:
	make -C generation test-unit

.PHONY: test-unit test-unit-cargo test-unit-python


# System testing
# ==============

test-system: test-integration test-proof-gen test-proof-translate test-proof-kgen test-proof-verify
.PHONY: test-system test-integration test-proof-gen test-proof-verify test-zk

test-integration:
	make -C generation generate-hints
	make -C generation test-integration

PROOFS_FILES := $(wildcard proofs/*)
PROOFS := $(filter %.ml-proof,$(PROOFS_FILES))
TRANSLATED_PROOFS=$(wildcard proofs/translated/*.ml-proof)
TRANSLATED_FROM_K=$(wildcard proofs/generated-from-k/*.ml-proof)


# Proof conversion checking
# -------------------------

.build/proofs/translated/%.ml-proof: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m "mm_translate.translate" generation/mm-benchmarks/$*.mm .build/proofs/translated/$* goal

PROOF_TRANSLATION_TARGETS=$(addsuffix .translate,${TRANSLATED_PROOFS})
proofs/translated/%.ml-proof.translate: .build/proofs/translated/%.ml-proof
	${BIN_DIFF} "proofs/translated/$*.ml-gamma" ".build/proofs/translated/$*/$*.ml-gamma"
	${BIN_DIFF} "proofs/translated/$*.ml-claim" ".build/proofs/translated/$*/$*.ml-claim"
	${BIN_DIFF} "proofs/translated/$*.ml-proof" ".build/proofs/translated/$*/$*.ml-proof"

test-proof-translate: ${PROOF_TRANSLATION_TARGETS}

# Regenerate proofs from K
# -------------------------

KGEN_PROOF_TRANSLATION_TARGETS=$(addsuffix .kgenerate,${TRANSLATED_FROM_K})
proofs/generated-from-k/%.ml-proof.kgenerate: proofs/generated-from-k/%.ml-proof
	poetry -C generation run python -m "kore_transfer.proof_gen" generation/k-benchmarks/$*/$*.k generation/proof-hints/$*/foo-a.$*.hints .build/kompiled-definitions/$*-kompiled --clean --proof-dir proofs/generated-from-k/

update-k-proofs: ${KGEN_PROOF_TRANSLATION_TARGETS}

.PHONY: update-k-proofs


# Checking proof generation for K
# -------------------------------

.build/proofs/generated-from-k/%.ml-proof: FORCE
	poetry -C generation run python -m "kore_transfer.proof_gen" generation/k-benchmarks/$*/$*.k generation/proof-hints/$*/foo-a.$*.hints .build/kompiled-definitions/$*-kompiled --proof-dir .build/proofs/generated-from-k/

KPROOF_TRANSLATION_TARGETS=$(addsuffix .kgen,${TRANSLATED_FROM_K})
proofs/generated-from-k/%.ml-proof.kgen: .build/proofs/generated-from-k/%.ml-proof
	${BIN_DIFF} "proofs/generated-from-k/$*.ml-gamma" ".build/proofs/generated-from-k/$*.ml-gamma"
	${BIN_DIFF} "proofs/generated-from-k/$*.ml-claim" ".build/proofs/generated-from-k/$*.ml-claim"
	${BIN_DIFF} "proofs/generated-from-k/$*.ml-proof" ".build/proofs/generated-from-k/$*.ml-proof"

test-proof-kgen: ${KPROOF_TRANSLATION_TARGETS}

.PHONY: test-proof-kgen


# Proof generation
# ----------------

.build/proofs/%.ml-proof: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m "proof_generation.proofs.$*" memo $(dir $@) $*

.build/proofs/%.pretty-proof: FORCE
	@mkdir -p $(dir $@)
	poetry -C generation run python -m "proof_generation.proofs.$*" pretty $(dir $@) $*

PROOF_GEN_TARGETS=$(addsuffix .gen,${PROOFS})
BIN_DIFF=./bin/proof-diff
DIFF=colordiff -U3
proofs/%.ml-proof.gen: .build/proofs/%.ml-proof .build/proofs/%.pretty-proof
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
	$(CARGO) run --release --bin checker proofs/$*.ml-gamma proofs/$*.ml-claim $<

TRANSLATED_PROOF_VERIFY_SNAPSHOT_TARGETS=$(addsuffix .verify,${TRANSLATED_PROOFS})
proofs/translated/%.ml-proof.verify: proofs/translated/%.ml-proof
	$(CARGO) run --release --bin checker proofs/translated/$*.ml-gamma proofs/translated/$*.ml-claim $<

test-proof-verify-translated: ${TRANSLATED_PROOF_VERIFY_SNAPSHOT_TARGETS}
.PHONY: test-proof-verify-translated

KTRANSLATED_PROOF_VERIFY_SNAPSHOT_TARGETS=$(addsuffix .kverify,${TRANSLATED_FROM_K})
proofs/generated-from-k/%.ml-proof.kverify: proofs/generated-from-k/%.ml-proof
	$(CARGO) run --release --bin checker proofs/generated-from-k/$*.ml-gamma proofs/generated-from-k/$*.ml-claim $<

test-proof-verify: ${PROOF_VERIFY_SNAPSHOT_TARGETS} ${TRANSLATED_PROOF_VERIFY_SNAPSHOT_TARGETS} ${KTRANSLATED_PROOF_VERIFY_SNAPSHOT_TARGETS}

TRANSLATED_PROOF_VERIFY_BUILD_TARGETS=$(addsuffix .verify-translated,${TRANSLATED_PROOFS})
proofs/translated/%.ml-proof.verify-translated: .build/proofs/translated/%.ml-proof
	$(CARGO) run --release --bin checker .build/proofs/translated/$*/$*.ml-gamma .build/proofs/translated/$*/$*.ml-claim .build/proofs/translated/$*/$*.ml-proof

verify-translated: clean-translated-proofs ${TRANSLATED_PROOF_VERIFY_BUILD_TARGETS}
.PHONY: verify-translated

PROOF_VERIFY_BUILD_TARGETS=$(addsuffix .verify-generated,${PROOFS})
proofs/%.ml-proof.verify-generated: .build/proofs/%.ml-proof
	$(CARGO) run --release --bin checker .build/proofs/$*.ml-gamma .build/proofs/$*.ml-claim .build/proofs/$*.ml-proof

verify-generated: clean-proofs ${PROOF_VERIFY_BUILD_TARGETS}
.PHONY: verify-generated

PROOF_VERIFY_KBUILD_TARGETS=$(addsuffix .verify-kgenerated,${TRANSLATED_FROM_K})
proofs/generated-from-k/%.ml-proof.verify-kgenerated: .build/proofs/generated-from-k/%.ml-proof
	$(CARGO) run --release --bin checker .build/proofs/generated-from-k/$*.ml-gamma .build/proofs/generated-from-k/$*.ml-claim .build/proofs/generated-from-k/$*.ml-proof

verify-kgenerated: clean-kgenerated-proofs ${PROOF_VERIFY_KBUILD_TARGETS}
.PHONY: verify-kgenerated

# Profiling
# ---------

PROFILING_TARGETS=$(addsuffix .profile,${PROOFS})
proofs/%.ml-proof.profile: .build/proofs/%.ml-proof
	$(CARGO)  build --release --bin profiler
	flamegraph -- .build/target/release/profiler .build/proofs/$*.ml-gamma .build/proofs/$*.ml-claim .build/proofs/$*.ml-proof
	mv flamegraph.svg $*.svg
	rm perf.data

PROFILING_TRANSLATED_TARGETS=$(addsuffix .profile,${TRANSLATED_PROOFS})
proofs/translated/%.ml-proof.profile: .build/proofs/translated/%.ml-proof
	$(CARGO) build --release --bin profiler
	flamegraph -- .build/target/release/profiler .build/proofs/translated/$*/$*.ml-gamma .build/proofs/translated/$*/$*.ml-claim .build/proofs/translated/$*/$*.ml-proof
	mv flamegraph.svg $*.svg
	rm perf.data

profile: ${PROFILING_TARGETS} ${PROFILING_TRANSLATED_TARGETS}

# Risc0
# -----

PROOF_ZK_TARGETS=$(addsuffix .zk,${PROOFS})
proofs/%.ml-proof.zk: proofs/%.ml-proof
	$(CARGO) run --release --bin host proofs/$*.ml-gamma proofs/$*.ml-claim $^

test-zk: ${PROOF_ZK_TARGETS}

# Run checker on converted files in the ZK mode
TRANSLATED_PROOF_ZK_TARGETS=$(addsuffix .zk-translated,${TRANSLATED_PROOFS})
proofs/translated/%.ml-proof.zk-translated: proofs/translated/%.ml-proof
	$(CARGO) run --release --bin host proofs/translated/$*.ml-gamma proofs/translated/$*.ml-claim $<

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
	output=$$($(CARGO) run --release --bin host proofs/translated/$*.ml-gamma proofs/translated/$*.ml-claim $<) ; \
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
