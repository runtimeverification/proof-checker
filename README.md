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

Usage 
=============

You will need to activate the project's `poetry` environment:
```
poetry install
poetry shell
```

To run all tests, run `make`.
You may also use specific targets to run a subset of tests:

-   `test-unit`: Run all unit-tests
    -   `test-unit-python`: Run python unit-tests. These include tests for proof
        generation.
    -   `test-unit-cargo`: Run cargo tests. These include tests for the proof
        checker.
-   `test-system`: Run tests for generating proofs and verifying them.
    -   `test-proof-gen`: Generate proofs from the python DSL, and check that
        they are what we expect. To generate and check a single proof, we may
        run `make proofs/<name>.ml-proof.gen`. You can also regenerate proofs by
        adding the parameeter `CHECK_PROOF=cp` to `make`.
    -   `test-proof-verify`: Run the verifier against proofs. An individual
        proof may be checked by running `make proofs/<name>.ml-proof.verify`
-   `test-zk`: Same as `test-proof-verify`, but also generate a ZK cerificate.
    An individual proof may be checked by running
    `make proofs/<name>.ml-proof.zk`

You can inspect the [Makefile](Makefile) to explore more granular commands. For example, examining `test-system` reveals that you can use

`cargo run --bin checker <ML-PROOF> <ML-CLAIM>` 

to run the checker on arbitrary proofs/claims.

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