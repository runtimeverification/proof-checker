POETRY     := poetry -C generation
POETRY_RUN := $(POETRY) run

default: check test-unit
all: check test-unit test-system test-zk
.PHONY: all default
.SECONDARY:
FORCE:


clean-proofs:
	rm -rf .build/proofs

clean-translated-proofs:
	rm -rf .build/proofs/translated

clean-kgenerated-proofs:
	rm -rf .build/proofs/generated-from-k

clean-python:
	rm -rf generation/dist generation/.coverage generation/cov-* generation/.mypy_cache generation/.pytest_cache
	find . -type d -name __pycache__ -prune -exec rm -rf {} \;

update-snapshots:
	rsync -u $(wildcard .build/proofs/*.*) proofs
	rsync -u $(wildcard .build/proofs/translated/*/*.ml*) proofs/translated
	rsync -u $(wildcard .build/proofs/generated-from-k/*/*.*) proofs/generated-from-k
	rsync -u -R $(wildcard .build/./proof-hints/*/*.pretty) proofs/

.PHONY: clean-proofs update-snapshots clean-translated-proofs clean-kgenerated-proofs clean-python

# Python set up
# =============

build-poetry:
	# See: https://github.com/python-poetry/poetry/issues/8699
	(cd generation; poetry build)

poetry-install:
	$(POETRY) install

.PHONY: poetry-install build-poetry

# Installation and setup
# ======================

build-rust:
	cargo build --manifest-path=rust/Cargo.toml

build-risc0:
	cargo build --manifest-path=risc0/pi2/Cargo.toml

install-kup:
	@if ! command -v kup &> /dev/null; then \
		echo "kup is not installed, installing..."; \
		curl https://kframework.org/install | bash; \
	else \
		echo "kup is already installed, skipping installation."; \
	fi

install-k-kup:
	kup install k --version v$(shell $(POETRY_RUN) python3 -c "import pyk; print(pyk.K_VERSION)"); \

build: build-poetry build-rust build-risc0 poetry-install

install-k: install-kup install-k-kup

.PHONY: build-rust build-risc0 poetry-install install-kup install-k install-k-kup build

# Syntax and formatting checks
# ============================

check: check-cargo check-python
check-cargo:
	cargo fmt --check

.PHONY: check check-cargo check-python

format: format-cargo format-python
format-cargo:
	cargo fmt

.PHONY: format format-cargo format-python


# Setup
# =====

ARCH := $(shell uname -m)
ifeq ($(ARCH),arm64)
    CARGO := cargo +nightly-2023-03-06-aarch64-apple-darwin
else
    CARGO := cargo
endif


# Testing
# =======

test-most: test-unit test-system test-integration
test: test-most test-zk

# Unit testing
# ============

test-unit: test-unit-python test-unit-cargo
test-unit-cargo:
	$(CARGO) test

.PHONY: test-unit test-unit-cargo test-unit-python

# Python checks and tests
# =======================

TEST_ARGS :=

test-python: poetry-install
	$(POETRY_RUN) pytest generation/src/tests --maxfail=1 --verbose --durations=0 --numprocesses=4 --dist=worksteal $(TEST_ARGS)

test-unit-python: poetry-install
	$(POETRY_RUN) pytest generation/src/tests/unit --maxfail=1 --verbose $(TEST_ARGS)

test-integration-python: poetry-install test-hints
	$(POETRY_RUN) pytest generation/src/tests/integration --maxfail=1 --verbose --durations=0 --numprocesses=4 --dist=worksteal $(TEST_ARGS)

# Coverage

COV_ARGS :=

cov: cov-all

cov-%: TEST_ARGS += --cov=proof_generation --no-cov-on-fail --cov-branch --cov-report=term

cov-all: TEST_ARGS += --cov-report=html:cov-all-html $(COV_ARGS)
cov-all: test-python

cov-unit: TEST_ARGS += --cov-report=html:cov-unit-html $(COV_ARGS)
cov-unit: test-unit-python

cov-integration: TEST_ARGS += --cov-report=html:cov-integration-html $(COV_ARGS)
cov-integration: test-integration-python


# Checks and formatting

format-python: autoflake isort black
check-python: check-flake8 check-mypy check-autoflake check-isort check-black pyupgrade

check-flake8: poetry-install
	$(POETRY_RUN) flake8 generation/src

check-mypy: poetry-install
	$(POETRY_RUN) mypy generation/src --strict-equality

autoflake: poetry-install
	$(POETRY_RUN) autoflake --quiet --in-place generation/src

check-autoflake: poetry-install
	$(POETRY_RUN) autoflake --quiet --check generation/src

isort: poetry-install
	$(POETRY_RUN) isort generation/src

check-isort: poetry-install
	$(POETRY_RUN) isort --check generation/src

black: poetry-install
	$(POETRY_RUN) black generation/src

check-black: poetry-install
	$(POETRY_RUN) black --check generation/src

# Optional tools

PYTHON_FILES := $(shell find generation/src -type f -name '*.py')

pyupgrade: poetry-install
	$(POETRY_RUN) pyupgrade --py310-plus $(PYTHON_FILES)

# Proof Hints
# ===========

ALL_K_FILES=$(wildcard generation/k-benchmarks/*/*)
K_DEFS=$(wildcard generation/k-benchmarks/*/*.k)
K_BENCHMARKS=$(filter-out ${K_DEFS}, ${ALL_K_FILES})

# Filter out currently unsupported examples
UNSUPPORTED_K_BENCHMARKS=$(wildcard generation/k-benchmarks/imp/*) \
                         generation/k-benchmarks/imp5/transfer.imp5
SUPPORTED_K_BENCHMARKS=$(filter-out ${UNSUPPORTED_K_BENCHMARKS}, ${K_BENCHMARKS})

# Proof Hint Generation from LLVM
# -------------------------------

EXECUTION_HINTS=$(addsuffix .hints, $(patsubst generation/k-benchmarks%,.build/proof-hints%,${SUPPORTED_K_BENCHMARKS}))

.SECONDEXPANSION:
module=$(patsubst %/,%, $(dir $*))
.build/proof-hints/%.hints: generation/k-benchmarks/% .build/kompiled-definitions/$$(module)-kompiled/timestamp
	mkdir -p .build/proof-hints/$(dir $*)
	./generation/scripts/gen-execution-proof-hints.sh \
		generation/k-benchmarks/$(dir $*)$(module).k \
		generation/k-benchmarks/$* \
		.build/proof-hints/$*.hints

generate-hints: $(EXECUTION_HINTS)

# Proof Hint pretty printing
# --------------------------

HINTS_PRETTY_PRINTED=$(addsuffix .pretty, ${EXECUTION_HINTS})

.SECONDEXPANSION:
module=$(patsubst %/,%, $(dir $*))
.build/proof-hints/%.hints.pretty: .build/kompiled-definitions/$$(module)-kompiled/timestamp .build/proof-hints/%.hints
	${POETRY_RUN} python -m "proof_generation.llvm_proof_hint_printer" \
	    .build/proof-hints/$*.hints \
		.build/kompiled-definitions/$(module)-kompiled \
		--output .build/proof-hints/$*.hints.pretty

pretty-print-hints: $(HINTS_PRETTY_PRINTED)

# Checking generated hints
# ------------------------

EXECUTION_HINTS_TARGETS=$(addsuffix .hints_gen,${EXECUTION_HINTS})

.build/proof-hints/%.hints.hints_gen: .build/proof-hints/%.hints.pretty
	${DIFF} --label expected "proofs/proof-hints/$*.hints.pretty" --label actual ".build/proof-hints/$*.hints.pretty"

test-hints: ${EXECUTION_HINTS_TARGETS}

# Removing generated hints (binary and pretty-printed)
# ----------------------------------------------------

clean-hints:
	rm -rf .build/proof-hints/*


.PHONY: generate-hints pretty-print-hints test-hints clean-hints


# System testing
# ==============

test-system: test-integration test-proof-gen test-proof-translate test-proof-kgen test-proof-verify
.PHONY: test-system test-integration test-proof-gen test-proof-verify test-zk

test-integration: test-integration-python

PROOFS_FILES := $(wildcard proofs/*)
PROOFS := $(filter %.ml-proof,$(PROOFS_FILES))
TRANSLATED_PROOFS=$(wildcard proofs/translated/*.ml-proof)
TRANSLATED_FROM_K=$(wildcard proofs/generated-from-k/*/*.ml-proof)


# Proof conversion checking
# -------------------------

.build/proofs/translated/%.ml-proof: FORCE
	@mkdir -p $(dir $@)
	$(POETRY_RUN) python -m "proof_generation.metamath.translate" generation/mm-benchmarks/$*.mm .build/proofs/translated/$* goal

PROOF_TRANSLATION_TARGETS=$(addsuffix .translate,${TRANSLATED_PROOFS})
proofs/translated/%.ml-proof.translate: .build/proofs/translated/%.ml-proof
	${BIN_DIFF} "proofs/translated/$*.ml-gamma" ".build/proofs/translated/$*/$*.ml-gamma"
	${BIN_DIFF} "proofs/translated/$*.ml-claim" ".build/proofs/translated/$*/$*.ml-claim"
	${BIN_DIFF} "proofs/translated/$*.ml-proof" ".build/proofs/translated/$*/$*.ml-proof"

test-proof-translate: ${PROOF_TRANSLATION_TARGETS}

# Kompiling Definitions
# ---------------------

.SECONDEXPANSION:
.build/kompiled-definitions/%-kompiled/timestamp: generation/k-benchmarks/$$*/$$*.k
	mkdir -p .build/kompiled-definitions/
	kompile --backend llvm --llvm-proof-hint-instrumentation --output-definition $(dir $@) $<

# Regenerate proofs from K
# ------------------------

KGEN_PROOF_TRANSLATION_TARGETS=$(addsuffix .kgenerate,${TRANSLATED_FROM_K})

.SECONDEXPANSION:
module=$(patsubst %/,%, $(dir $*))
proofs/generated-from-k/%.ml-proof.kgenerate: .build/kompiled-definitions/$$(module)-kompiled/timestamp .build/proof-hints/%.hints proofs/generated-from-k/%.ml-proof
	$(POETRY_RUN) python -m "proof_generation.k.proof_gen" \
	              $(module) \
				  .build/proof-hints/$*.hints \
				  .build/kompiled-definitions/$(module)-kompiled \
				  --proof-dir proofs/generated-from-k/$(dir $*)
	$(POETRY_RUN) python -m "proof_generation.k.proof_gen" \
	              $(module) \
				  .build/proof-hints/$*.hints \
				  .build/kompiled-definitions/$(module)-kompiled \
				  --proof-dir proofs/generated-from-k/$(dir $*) \
				  --pretty

update-k-proofs: ${KGEN_PROOF_TRANSLATION_TARGETS}

.PHONY: update-k-proofs


# Checking proof generation for K
# -------------------------------
.SECONDEXPANSION:
module=$(patsubst %/,%, $(dir $*))
.build/proofs/generated-from-k/%.ml-proof: FORCE .build/kompiled-definitions/$$(module)-kompiled/timestamp .build/proof-hints/%.hints
	$(POETRY_RUN) python -m "proof_generation.k.proof_gen" \
	              $(module) \
				  .build/proof-hints/$*.hints \
				  .build/kompiled-definitions/$(module)-kompiled \
				  --proof-dir .build/proofs/generated-from-k/$(dir $*)

.build/proofs/generated-from-k/%.pretty-proof: FORCE .build/kompiled-definitions/$$(module)-kompiled/timestamp .build/proof-hints/%.hints
	$(POETRY_RUN) python -m "proof_generation.k.proof_gen" \
	              $(module) \
				  .build/proof-hints/$*.hints \
				  .build/kompiled-definitions/$(module)-kompiled \
				  --proof-dir .build/proofs/generated-from-k/$(dir $*) \
				  --pretty

KPROOF_TRANSLATION_TARGETS=$(addsuffix .kgen,${TRANSLATED_FROM_K})
proofs/generated-from-k/%.ml-proof.kgen: .build/proofs/generated-from-k/%.ml-proof .build/proofs/generated-from-k/%.pretty-proof
	${DIFF} --label expected "proofs/generated-from-k/$*.pretty-claim" --label actual ".build/proofs/generated-from-k/$*.pretty-claim"
	${DIFF} --label expected "proofs/generated-from-k/$*.pretty-proof" --label actual ".build/proofs/generated-from-k/$*.pretty-proof"
	${DIFF} --label expected "proofs/generated-from-k/$*.pretty-gamma" --label actual ".build/proofs/generated-from-k/$*.pretty-gamma"
	${BIN_DIFF} "proofs/generated-from-k/$*.ml-gamma" ".build/proofs/generated-from-k/$*.ml-gamma"
	${BIN_DIFF} "proofs/generated-from-k/$*.ml-claim" ".build/proofs/generated-from-k/$*.ml-claim"
	${BIN_DIFF} "proofs/generated-from-k/$*.ml-proof" ".build/proofs/generated-from-k/$*.ml-proof"

test-proof-kgen: ${KPROOF_TRANSLATION_TARGETS}

.PHONY: test-proof-kgen


# Proof generation
# ----------------

.build/proofs/%.ml-proof: FORCE generation/src/proof_generation/proofs/%.py
	@mkdir -p $(dir $@)
	$(POETRY_RUN) python -m "proof_generation.proofs.$*" binary $(dir $@) $* --optimize

.build/proofs/%.pretty-proof: FORCE generation/src/proof_generation/proofs/%.py
	@mkdir -p $(dir $@)
	$(POETRY_RUN) python -m "proof_generation.proofs.$*" pretty-no-stack $(dir $@) $* --optimize

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
