POETRY     := poetry
POETRY_RUN := $(POETRY) run


default: check test-unit

all: check cov

.PHONY: clean
clean:
	rm -rf dist .coverage cov-* .mypy_cache .pytest_cache
	find -type d -name __pycache__ -prune -exec rm -rf {} \;

.PHONY: build
build:
	$(POETRY) build

.PHONY: poetry-install
poetry-install:
	$(POETRY) install

# Print the K version required by pyk

k-version:
	@echo $(shell $(POETRY_RUN) python3 -c "import pyk; print(pyk.K_VERSION)")

.PHONY: k-version

# Generate Proof hints

# Target only this specific subset of programs that are currently supported:
PROOF_HINTS=proof-hints/peano/mul_3_5.peano.hints \
			proof-hints/single-rewrite/foo-a.single-rewrite.hints \
			proof-hints/double-rewrite/foo-a.double-rewrite.hints \
			proof-hints/trivial/0_rewrites.trivial.hints \
			proof-hints/trivial/1_rewrite.trivial.hints \
			proof-hints/trivial/2_rewrites.trivial.hints \
			proof-hints/imp5/empty.imp5.hints \
			proof-hints/imp5-rw-succ/transfer.imp5-rw-succ.hints \
			proof-hints/imp5-rw-literal/transfer.imp5-rw-literal.hints \
			proof-hints/simple/input.simple.hints

# Eventually, we want to support all input programs using something like the following:
# ALL_K_FILES=$(wildcard k-benchmarks/*/*)
# K_DEFS=$(wildcard k-benchmarks/*/*.k)
# INPUT_PROGRAMS=$(filter-out ${K_DEFS}, ${ALL_K_FILES})
# PROOF_HINTS=$(addsuffix .hints, $(patsubst k-benchmarks%,proof-hints%,${INPUT_PROGRAMS}))

proof-hints/%.hints: k-benchmarks/%
	mkdir -p proof-hints/$(dir $*)
	./scripts/gen-execution-proof-hints.sh \
		k-benchmarks/$(dir $*)$(patsubst %/,%, $(dir $*)).k \
		k-benchmarks/$* \
		proof-hints/$*.hints

generate-hints: $(PROOF_HINTS)

clean-hints:
	rm -f $(PROOF_HINTS)

.PHONY: generate-hints clean-hints


# Tests

TEST_ARGS :=

test: test-all

test-all: poetry-install
	$(POETRY_RUN) pytest src/tests --maxfail=1 --verbose --durations=0 --numprocesses=4 --dist=worksteal $(TEST_ARGS)

test-unit: poetry-install
	$(POETRY_RUN) pytest src/tests/unit --maxfail=1 --verbose $(TEST_ARGS)

test-integration: poetry-install generate-hints
	$(POETRY_RUN) pytest src/tests/integration --maxfail=1 --verbose --durations=0 --numprocesses=4 --dist=worksteal $(TEST_ARGS)


# Coverage

COV_ARGS :=

cov: cov-all

cov-%: TEST_ARGS += --cov=proof_generation --no-cov-on-fail --cov-branch --cov-report=term

cov-all: TEST_ARGS += --cov-report=html:cov-all-html $(COV_ARGS)
cov-all: test-all

cov-unit: TEST_ARGS += --cov-report=html:cov-unit-html $(COV_ARGS)
cov-unit: test-unit

cov-integration: TEST_ARGS += --cov-report=html:cov-integration-html $(COV_ARGS)
cov-integration: test-integration


# Checks and formatting

format: autoflake isort black
check: check-flake8 check-mypy check-autoflake check-isort check-black pyupgrade

check-flake8: poetry-install
	$(POETRY_RUN) flake8 src

check-mypy: poetry-install
	$(POETRY_RUN) mypy src --strict-equality

autoflake: poetry-install
	$(POETRY_RUN) autoflake --quiet --in-place src

check-autoflake: poetry-install
	$(POETRY_RUN) autoflake --quiet --check src

isort: poetry-install
	$(POETRY_RUN) isort src

check-isort: poetry-install
	$(POETRY_RUN) isort --check src

black: poetry-install
	$(POETRY_RUN) black src

check-black: poetry-install
	$(POETRY_RUN) black --check src


# Optional tools

SRC_FILES := $(shell find src -type f -name '*.py')

pyupgrade: poetry-install
	$(POETRY_RUN) pyupgrade --py310-plus $(SRC_FILES)
