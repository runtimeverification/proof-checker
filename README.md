This repository implements a matching-logic proof checker for the binary format
described in [proof-language.md].

*   The core logic of the checker is being implement in the package under [checker/].
*   We use Risc0 to provide a ZKed implementation of the above, under [risc0/].
*   We are porting metamath proofs from [https://github.com/runtimeverification/proof-generation]
    in the directory [generation/].
