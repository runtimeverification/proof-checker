# Experiments and Evaluation of ZK Backends

We present our experiments and evaluation of several ZK backends.

## Benchmark Set Description

We use two benchmark sets for our evaluation:
Direct Implementation and Proofs of Proofs.

### Direct Implementation

In this category, we consider four simple programs in the areas of blockchain and AI
and use several ZK backends to directly generate their ZK proofs.
These programs are:
- `transfer`: a simplified version of the ERC20 transfer function;
- `batch-transfer`: a while loop that executes `transfer` for 5000 times;
- `perceptron`: a single-layer [perceptron](https://en.wikipedia.org/wiki/Perceptron).
- `svm`: a [support vector machine (SVM)](https://en.wikipedia.org/wiki/Support_vector_machine)
  model.

The reference pseudocode of these examples are available at the end
of this document.

Given a ZK backend, we directly implement these programs in the
programming language to the backend and generate ZK proof
of their execution traces.

### Proofs of Proofs

In this category, we combine ZK proofs and logical/mathematical proofs.
For a program `Pgm` in a programming language `PL`, we use the
[K framework](https://kframework.org) to generate
a logical proof `PI(Pgm, PL)` that shows the correctness of an execution
trace of `Pgm` using directly a formal semantics of `PL`.
Such a logical proof can be automatically checked by a logical proof checker
`proof_check(PI(Pgm, PL))`.
Then, we generate a ZK proof that shows the correctness of
an execution trace of `proof_check`.
In other words, we generate a ZK proof that shows the correctness
of a logical proof that shows the correctness of `Pgm` written in language `PL`.
Thus, we call this benchmark set Proofs of Proofs, as we generate
(ZK) proofs of (logical) proofs.

### ZK Backends

We consider the following ZK backends:
- [Cairo](https://www.cairo-lang.org/)
- [Lurk](https://lurk-lang.org/)
- [RISC Zero](https://www.risczero.com/)
- [zkLLVM](https://github.com/NilFoundation/zkLLVM)

## Performance Tables

- machine spec: AMD Ryzen 9 7950X(16 cores/32 threads/128GB), 4090RTX
- memory swap: 108GB
- performance time measured in seconds
- besides RISC Zero, all other implementations were executed using the diff between
  the timestamps of the start and end of each possible execution phase.
- RISC Zero has its own performance counter, so we use it to measure the execution time and cycles.
- "CPU" prefix = without GPU acceleration
- "GPU" prefix = with GPU acceleration
- last update date: Dec 19th, 2023.

### Direct Implementation

#### Cairo Zero (v0.13.0) with Lambdaworks Cairo Platinum Prover (v0.3.0)
Last Update: Dec 22th, 2023
|                                                             Examples                                                             | CPU Exec Time | CPU Prove Time | CPU Verify Time | CPU Total Time |
|:---------------------------------------------------------------------------------------------------------------------------------|:-------------:|:--------------:|:---------------:|:--------------:|
| [transfer](https://github.com/runtimeverification/proof-checker/blob/main/cairo/csl-examples/cairo0/transfer.cairo)              |         0.440 |          0.195 |           0.008 |          0.643 |
| [batch-transfer](https://github.com/runtimeverification/proof-checker/blob/main/cairo/csl-examples/cairo0/batch_transfer.cairo)* |         6.825 |         30.196 |           0.869 |         37.890 |
| [perceptron](https://github.com/runtimeverification/proof-checker/blob/main/cairo/csl-examples/cairo0/perceptron.cairo)          |         0.448 |          0.166 |           0.008 |          0.662 |
| [svm](https://github.com/runtimeverification/proof-checker/blob/main/cairo/csl-examples/cairo0/svm.cairo)                        |         0.443 |          0.176 |           0.008 |          0.627 |


#### Lurk
Last Update: Dec 19th, 2023
|                                                       Examples                                                          | Iterations | CPU Prove Time | CPU Verify Time | CPU Total Time | GPU Prove Time | GPU Verify Time | GPU Total Time |
|:-----------------------------------------------------------------------------------------------------------------------:|:----------:|:--------------:|:---------------:|:--------------:|:--------------:|:---------------:|:--------------:|
| [transfer](https://github.com/runtimeverification/proof-checker/blob/main/lurk/csl-examples/transfer.lurk)              |         34 |          2.393 |           0.554 |          2.947 |          2.313 |           0.618 |          2.931 |
| [batch-transfer](https://github.com/runtimeverification/proof-checker/blob/main/lurk/csl-examples/batch_transfer.lurk)* |     505037 |       3681.819 |           9.845 |       3691.664 |       1193.355 |           6.571 |       1199.926 |
| [perceptron](https://github.com/runtimeverification/proof-checker/blob/main/lurk/csl-examples/perceptron.lurk)          |         11 |          3.501 |           0.541 |          4.042 |          0.830 |           0.579 |          1.409 |
| [svm](https://github.com/runtimeverification/proof-checker/blob/main/lurk/csl-examples/svm5.lurk)                       |          9 |          1.832 |           0.538 |          2.370 |          0.820 |           0.598 |          1.418 |

\* Using `lurk --rc 400 batch_transfer.lurk`, other tests doesn't use `--rc`


#### RISC Zero (v0.16.1)
|                                                         Examples                                                              |  Cycles | CPU Exec Time | GPU Exec Time | CPU Prove Time | GPU Prove Time | CPU Verify Time | GPU Verify Time | CPU Total Time | GPU Total Time |
|:-----------------------------------------------------------------------------------------------------------------------------:|:-------:|:-------------:|:-------------:|:--------------:|:--------------:|:---------------:|:---------------:|:--------------:|:--------------:|
| [transfer](https://github.com/runtimeverification/proof-checker/blob/main/risc0/csl-examples/guest/src/transfer.rs)           |  21156  |     0.029     |     0.017     |      2.336     |      0.571     |      0.002      |      0.001      |      2.367     |      0.589     |
| [batch-transfer](https://github.com/runtimeverification/proof-checker/blob/main/risc0/csl-examples/guest/src/transfer5000.rs) | 754199  |     0.057     |     0.041     |     37.970     |      7.670     |      0.001      |      0.001      |     38.028     |      7.712     |
| [perceptron](https://github.com/runtimeverification/proof-checker/blob/main/risc0/csl-examples/guest/src/perceptron.rs)       |  21156  |     0.029     |     0.017     |      2.316     |      0.639     |      0.001      |      0.001      |      2.346     |      0.657     |
| [svm](https://github.com/runtimeverification/proof-checker/blob/main/risc0/csl-examples/guest/src/svm5.rs)                    |  21156  |     0.028     |     0.028     |      2.323     |      0.599     |      0.002      |      0.001      |      2.353     |      0.628     |


#### zkLLVM (v0.1.11-48)
Last Update: Dec 21th, 2023
|                                                  Examples                                                         | CPU Circuit Gen Time | CPU Prove+Verify Time |
|:-----------------------------------------------------------------------------------------------------------------:|:--------------------:|:---------------------:|
| [transfer](https://github.com/runtimeverification/proof-checker/tree/main/zkllvm/csl-zkllvm/transfer)             |                0.780 |                 0.135 |
| [batch-transfer](https://github.com/runtimeverification/proof-checker/tree/main/zkllvm/csl-zkllvm/batch_transfer) |                1.361 |               146.690 |
| [perceptron](https://github.com/runtimeverification/proof-checker/tree/main/zkllvm/csl-zkllvm/perceptron)         |                0.980 |                 0.131 |
| [svm](https://github.com/runtimeverification/proof-checker/tree/main/zkllvm/csl-zkllvm/svm)                       |                0.950 |                 0.134 |

### Proofs of Proofs

#### Lurk
Last Update: Dec 19th, 2023
|                                                            Examples                                                      | Cycles | GPU Prove Time | GPU Verify Time | GPU Total Time | GPU Prove Time | GPU Verify Time | GPU Total Time |
|:------------------------------------------------------------------------------------------------------------------------:|:------:|:--------------:|:---------------:|:--------------:|:--------------:|:---------------:|:--------------:|
| [impreflex](https://github.com/runtimeverification/proof-checker/blob/main/lurk/test_impreflex.lurk)*                    |   55651|        217.268 |           5.800 |        223.068 |        107.558 |           3.967 |        111.525 |
| [transfer-goal](https://github.com/runtimeverification/proof-checker/blob/main/lurk/test_transfer_goal.lurk)             | 3202986|             ∞  |              ∞  |             ∞  |              ∞ |               ∞ |              ∞ |
| [batch-transfer-goal](https://github.com/runtimeverification/proof-checker/blob/main/lurk/test_batch_transfer_goal.lurk) |30122047|             ∞  |              ∞  |             ∞  |              ∞ |               ∞ |              ∞ |
| [perceptron-goal](https://github.com/runtimeverification/proof-checker/blob/main/lurk/test_perceptron_goal.lurk)         | 6404208|             ∞  |              ∞  |             ∞  |              ∞ |               ∞ |              ∞ |
| [svm-goal](https://github.com/runtimeverification/proof-checker/blob/main/lurk/test_svm_goal.lurk)                       | 6404208|             ∞  |              ∞  |             ∞  |              ∞ |               ∞ |              ∞ |


\* Using `lurk --rc 400 ...`


#### RISC Zero (v0.16.1)
|      Examples*      |  Cycles | CPU Exec Time | GPU Exec Time | CPU Prove Time | GPU Prove Time | CPU Verify Time | GPU Verify Time | CPU Total Time | GPU Total Time |
|:-------------------:|:-------:|:-------------:|:-------------:|:--------------:|:--------------:|:---------------:|:---------------:|:--------------:|:--------------:|
| impreflex           |   67460 |     0.031     |     0.031     |       4.705    |      1.097     |      0.001      |      0.002      |       4.737    |      1.130     |
| transfer-goal       | 1142529 |     0.056     |     0.052     |      48.921    |     10.606     |      0.002      |      0.003      |      48.979    |     10.661     |
| batch-transfer-goal | 6722986 |     0.112     |     0.129     |     274.692    |     58.901     |      0.011      |      0.011      |     274.815    |     59.041     |
| perceptron-goal     | 3212385 |     0.071     |     0.066     |     128.392    |     28.829     |      0.006      |      0.006      |     128.469    |     28.901     |
| svm-goal            | 3212385 |     0.050     |     0.050     |     128.013    |     28.520     |      0.006      |      0.006      |     128.069    |     28.576     |

\* For the RISC Zero $PI^2$ implementation, we have the main implementation defined
[here](https://github.com/runtimeverification/proof-checker/tree/main/risc0/pi2)
and the inputs defined [here](https://github.com/runtimeverification/proof-checker/tree/main/proofs/translated).
The inputs are split into three files: `*-gamma`, `*-claim`, and `*-proof`.
Ultimately, we expect that all $PI^2$ implementations will support an unique
binary input format, and therefore, all implementations will share these same
inputs and have only one main implementation.

#### zkLLVM
|       Examples      |CPU Circuit Gen Time | CPU Prove+Verify Time |
|:-------------------:|:-------------------:|:---------------------:|
| impreflex           |               5.798 |                372.76 |
| transfer-goal       |              91.160 |              7188.792 |
| batch-transfer-goal |                   ∞ |                     ∞ |
| perceptron-goal     |             359.743 |                     ∞ |
| svm-goal            |             359.371 |                     ∞ |

\* For the zkLLVM $PI^2$ implementation, we have the main implementation defined
[here](https://github.com/runtimeverification/proof-checker/tree/main/zkllvm/src)
and the inputs defined [here](https://github.com/runtimeverification/proof-checker/tree/main/zkllvm/inputs).
The inputs are split and encoded into three arrays on a file for each file to
match the input requirements of the zkLLVM implementation.

## Implementation Details

### Lurk Implementation Details
Lurk is a interpreted programming language, that said, when we execute an
example in Lurk, we are actually executing the interpreter that will execute the
program. This means that the execution time required for the interpreter to load
(interpret) every function and definition is also counted in the execution time
of the program, and therefore, we can't measure the compilation time of the
program itself.

To execute large Lurk examples requires an increased swap memory, resulting in
slower execution times compared to other implementations. Due to this limitation,
it is difficult to accurately measure and compare execution times between Lurk
and other implementations. Even though we have 128GB of RAM + 108Gb of swap
memory, we still couldn't execute most of $PI^2$ examples in Lurk, that what
the `∞` means on the performance tables.

The Lurk's examples were executed within the following version:

```bash
commit: 2023-12-18 0c0e1849884c8016d1f001cf17e8d692dbe98dbd
lurk 0.2.0
```

To execute the examples using GPU this setup was used to compile the Lurk binary:

```bash
export EC_GPU_CUDA_NVCC_ARGS='--fatbin --gpu-architecture=sm_89 --generate-code=arch=compute_89,code=sm_89'
export CUDA_ARCH=89
export NVIDIA_VISIBLE_DEVICES=all
export NVIDIA_DRIVER_CAPABILITITES=compute,utility
export EC_GPU_FRAMEWORK=cuda
cargo install --path . --features=cuda
```

To execute the examples using only CPU this setup was used to compile the Lurk
binary:

```bash
export CUDA_PATH=
export NVCC=off
export EC_GPU_FRAMEWORK=none
cargo install --path . --force
```

### zkLLVM Implementation Details

zkLLVM doesn't support GPU acceleration in any phase, therefore, we don't have
GPU results for these experiments.

The proof and verification on zkLLVM were genereted using
`transpiler -m gen-test-proof`.

The version of the individual tools used to execute the examples were:

```bash
$ clang-17 --version
clang version 17.0.4 (http://www.github.com/NilFoundation/zkllvm-circifier.git 4c393658e71bed430b996cff8555a548fbe8bbda)

$ assigner --version
0.1.11-48

$ transpiler --version
0.1.11-48
```