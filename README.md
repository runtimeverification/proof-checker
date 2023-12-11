Matching Logic Checker
======================

This repository implements a matching-logic proof checker for the binary format
described in [docs/proof-language.md](docs/proof-language.md).

*   The core logic of the checker is being implemented in the package under [checker/](checker/).
*   We use Risc0 to provide a ZKed implementation of the above, under [risc0/](risc0/).
*   We are porting proofs from [the Metamath-based project](https://github.com/runtimeverification/proof-generation) in the directory [generation/](generation/).
    * See [this issue](https://github.com/runtimeverification/proof-checker/issues/16) for detailed instructions on how to port a proof.
*   You can find some example proofs in [proofs/](proofs/).

Dependencies
=============
Apart from Rust and Python, you will likely need to:

`sudo apt-get install colordiff`

For installing Rust, you need to install Cargo, the Rust package manager. You can do this by following the instructions [here](https://www.rust-lang.org/tools/install).

For managing Python dependencies, we use [poetry](https://python-poetry.org/). You can install it by following the instructions [here](https://python-poetry.org/docs/#installation).

Everything except the K framework can be installed with `make build` command.

Install the K framework with `make install-k`.

Basic commands
=============

To generate proofs from scratch and verify them using the (non-zk) checker, run:
```
make verify-generated
```

To translate proofs from scratch and verify them using the (non-zk) checker, run:
```
make verify-translated
```

These two commands bypass regression testing.
In effect, one can use this to verify their changes proof-check without needing
to update the respective snapshots in `proofs`.

To run the zk checker on pre-translated proofs, run:
```
make test-translated-zk
```

To run all tests, run `make`.
You may also use specific targets to run a subset of tests:

-   `test-unit`: Run all unit-tests
    -   `test-unit-python`: Run python unit-tests. These include tests for proof
        generation.
    -   `test-unit-cargo`: Run cargo tests. These include tests for the proof
        checker.
-   `test-system`: Run tests for generating proofs and verifying them.
    -   `test-integration`: Generate proof hints for `k-benchmarks` (if needed) and check that they pass the tests
    -   `test-proof-gen`: Generate proofs from the python DSL, and check that
        they are what we expect (given by snapshots in `proofs`).
        To generate and check a single proof, we may run `make proofs/<name>.ml-proof.gen`.
    -   `test-proof-translate`: Generate proofs from translating MM proofs, and check that
        they are what we expect (given by snapshots in `proofs/translated`).
        To generate and check a single proof, we may run `make proofs/translated/<name>.ml-proof.gen`.
    -   `test-proof-verify`: Run the verifier against both `proofs` and `proofs/translated`. An individual
        proof may be checked by running `make proofs/<name>.ml-proof.verify` (or `make proofs/translated/<name>.ml-proof.verify`)
-   `test-zk`: Same as `test-proof-verify` against `proofs` (not `proofs/translated`), but also generate a ZK cerificate.
    An individual proof may be checked by running
    `make proofs/<name>.ml-proof.zk`

You can inspect the [Makefile](Makefile) to explore more granular commands. For example, examining `test-proof-verify` reveals that you can use

`cargo run --release --bin checker <ML-GAMMA> <ML-CLAIM> <ML-PROOF>`

to run the checker on arbitrary proofs/claims.

For running translation from Metamath, one needs to `cd` the `generation` folder, activate Poetry
```
poetry install
poetry shell
```
and then run
```
python -m src.mm_transfer.transfer {MM_FILE} {OUTPUT_FOLDER} {LEMMA_NAME}
```

Profiling
=========

We use [flamegraph-rs](https://github.com/flamegraph-rs/flamegraph/tree/main) for profiling. Run these commands to set it up:

```
sudo apt install linux-tools-common linux-tools-generic linux-tools-`uname -r`
cargo install flamegraph
```

To run the tool without root, you may need to configure `perf_event_paranoid` to a lower value. See details [here](https://github.com/flamegraph-rs/flamegraph/tree/main#enabling-perf-for-use-by-unprivileged-users).

You should now be able to run `make profile`. This should produce several flamegraph files (such as `propositional.svg`), which can be visualized in a browser.

Currently we only profile normal execution of the checker (as opposed to `Risc0` execution). Furthermore, because normal execution on the existing proofs is too fast to lend itself to meaningful profiling, the `profiler.rs` binary actually runs the checker `100 000` times for each proof.

**Warning**: `flamegraph`'s default sampling frequency (`-F 997`) can lead to huge `perf.data` files when you run it on longer executions. For example, running it on our host binary can output several GBs. If you want to profile long executions, consider reducing the sampling frequency accordingly.

Generating Proof Hints
======================

We provide [this script](scripts/gen-execution-proof-hints.sh) to
generate proof hints for a concrete execution of a given program. The script
expects as arguments: (1) a K definition, (2) a program to execute using that
definition, and (3) the output file name where the generated proof hints are
stored.

An example invocation of the script is shown below:
```
./scripts/gen-execution-proof-hints.sh \
   k-benchmarks/single-rewrite/single-rewrite.k \
   k-benchmarks/single-rewrite/foo-a.single-rewrite \
   proof-hints/foo-a.single-rewrite.hints
```

Note that the script assumes that the project is compiled, with a recent-enough
version of K that was installed by `make install-k`.
