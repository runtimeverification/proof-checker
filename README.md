This repository implements a matching-logic proof checker for the binary format
described in [proof-language.md].

*   The core logic of the checker is being implement in the package under [checker/].
*   We use Risc0 to provide a ZKed implementation of the above, under [risc0/].
*   We are porting metamath proofs from [https://github.com/runtimeverification/proof-generation]
    in the directory [generation/].
*   The directory, [proofs/] contains some example proofs.

Running Tests
=============

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

