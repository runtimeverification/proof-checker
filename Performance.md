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
- performance time measured in seconds
- "CPU" prefix = without GPU acceleration
- "GPU" prefix = with GPU acceleration
- last update date: Dec 6th, 2023. 

### Direct Implementation

#### CairoZero (v0.12.3)
|                                                             Examples                                                           | CPU Exec Time | CPU Prove Time | CPU Verify Time | CPU Total Time |
|:-------------------------------------------------------------------------------------------------------------------------------|:-------------:|:--------------:|:---------------:|:--------------:|
| [transfer](https://github.com/runtimeverification/proof-checker/blob/main/cairo/csl-examples/cairo0/transfer.cairo)            |         0.441 |          0.185 |           0.008 |          0.634 |
| [batch-transfer](https://github.com/runtimeverification/proof-checker/blob/main/cairo/csl-examples/cairo0/transfer5000.cairo)* |         6.799 |         26.311 |           0.867 |         33.977 |
| [perceptron](https://github.com/runtimeverification/proof-checker/blob/main/cairo/csl-examples/cairo0/perceptron.cairo)        |         0.438 |          0.149 |           0.007 |          0.594 |
| [svm](https://github.com/runtimeverification/proof-checker/blob/main/cairo/csl-examples/cairo0/svm5.cairo)                     |         0.442 |          0.175 |           0.007 |          0.624 |


#### Lurk
|                                                       Examples                                                        |  Cycles | CPU Time** | GPU Prove Time | GPU Verify Time | GPU Total Time |
|:---------------------------------------------------------------------------------------------------------------------:|:-------:|:----------:|:--------------:|:---------------:|:--------------:|
| [transfer](https://github.com/runtimeverification/proof-checker/blob/main/lurk/csl-examples/transfer.lurk)            |    34   |            |          2.205 |           0.595 |          2.800 |
| [batch-transfer](https://github.com/runtimeverification/proof-checker/blob/main/lurk/csl-examples/transfer5000.lurk)* |  505037 |            |              ∞ |               ∞ |              ∞ |
| [perceptron](https://github.com/runtimeverification/proof-checker/blob/main/lurk/csl-examples/perceptron.lurk)        |    11   |            |          0.840 |           0.597 |          1.437 |
| [svm](https://github.com/runtimeverification/proof-checker/blob/main/lurk/csl-examples/svm5.lurk)                     |    9    |            |          0.820 |           0.607 |          1.427 |

\* Using `lurk --rc 400 transfer5000.lurk`, other tests doesn't use `--rc`


#### RISC Zero (v0.16.1)
|                                                         Examples                                                              |  Cycles | CPU Exec Time | GPU Exec Time | CPU Prove Time | GPU Prove Time | CPU Verify Time | GPU Verify Time | CPU Total Time | GPU Total Time |
|:-----------------------------------------------------------------------------------------------------------------------------:|:-------:|:-------------:|:-------------:|:--------------:|:--------------:|:---------------:|:---------------:|:--------------:|:--------------:|
| [transfer](https://github.com/runtimeverification/proof-checker/blob/main/risc0/csl-examples/guest/src/transfer.rs)           |  21156  |     0.029     |     0.017     |      2.336     |      0.571     |      0.002      |      0.001      |      2.367     |      0.589     |
| [batch-transfer](https://github.com/runtimeverification/proof-checker/blob/main/risc0/csl-examples/guest/src/transfer5000.rs) | 754199  |     0.057     |     0.041     |     37.970     |      7.670     |      0.001      |      0.001      |     38.028     |      7.712     |
| [perceptron](https://github.com/runtimeverification/proof-checker/blob/main/risc0/csl-examples/guest/src/perceptron.rs)       |  21156  |     0.029     |     0.017     |      2.316     |      0.639     |      0.001      |      0.001      |      2.346     |      0.657     |
| [svm](https://github.com/runtimeverification/proof-checker/blob/main/risc0/csl-examples/guest/src/svm5.rs)                    |  21156  |     0.028     |     0.028     |      2.323     |      0.599     |      0.002      |      0.001      |      2.353     |      0.628     |


#### zkLLVM
|                                                  Examples                                                       | CPU Circuit Gen Time | CPU Prove+Verify Time | GPU Time |
|:---------------------------------------------------------------------------------------------------------------:|:--------------------:|:---------------------:|:--------:|
| [transfer](https://github.com/runtimeverification/proof-checker/tree/main/zkllvm/csl-zkllvm/transfer)           |                0.440 |                 0.630 |          |
| [batch-transfer](https://github.com/runtimeverification/proof-checker/tree/main/zkllvm/csl-zkllvm/transfer5000) |                0.823 |                38.842 |          |
| [perceptron](https://github.com/runtimeverification/proof-checker/tree/main/zkllvm/csl-zkllvm/perceptron)       |                0.450 |                 0.650 |          |
| [svm](https://github.com/runtimeverification/proof-checker/tree/main/zkllvm/csl-zkllvm/svm5)                    |                0.450 |                 0.630 |          |

### Proofs of Proofs

#### Lurk
|                                                            Examples                                                            | Cycles | CPU Time** | GPU Prove Time | GPU Verify Time | GPU Total Time |
|:------------------------------------------------------------------------------------------------------------------------------:|:------:|:----------:|:--------------:|:---------------:|:--------------:|
| [impreflex](https://github.com/runtimeverification/proof-checker/blob/main/lurk/test_impreflex_compressed_goal.lurk)*          | 55651  |            |        108.962 |           4.209 |        113.171 |
| [transfer-goal](https://github.com/runtimeverification/proof-checker/blob/main/lurk/test_transfer_simple_compressed_goal.lurk) | 3202986|            |              ∞ |               ∞ |        ∞       |
| [batch-transfer-goal](https://github.com/runtimeverification/proof-checker/blob/main/lurk/test_transfer_batch_1k_goal.lurk)    |30122047|            |              ∞ |               ∞ |        ∞       |
| [perceptron-goal](https://github.com/runtimeverification/proof-checker/blob/main/lurk/test_perceptron_goal.lurk)               | 6404208|            |              ∞ |               ∞ |        ∞       |
| [svm-goal](https://github.com/runtimeverification/proof-checker/blob/main/lurk/test_svm5_goal.lurk)                            | 6404208|            |              ∞ |               ∞ |        ∞       |


\* Using `lurk --rc 400 ...`

\** CPU time is outdated as we can't get only CPU execution due to a bug on Lurk's
own implementation


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
|       Examples      |CPU Circuit Gen Time | CPU Prove+Verify Time | GPU Time |
|:-------------------:|:-------------------:|:---------------------:|:--------:|
| impreflex           |               5.798 |                372.76 |          |
| transfer-goal       |              91.160 |              7188.792 |          |
| batch-transfer-goal |                ∞    |                     ∞ |          |
| perceptron-goal     |             359.743 |                     ∞ |          |
| svm-goal            |             359.371 |                     ∞ |          |

\* For the zkLLVM $PI^2$ implementation, we have the main implementation defined
[here](https://github.com/runtimeverification/proof-checker/tree/main/zkllvm/src)
and the inputs defined [here](https://github.com/runtimeverification/proof-checker/tree/main/zkllvm/inputs).
The inputs are split and encoded into three arrays on a file for each file to
match the input requirements of the zkLLVM implementation. 

## Lurk Implementation Details
Lurk is a interpreted programming language, that said, when we execute an 
example in Lurk, we are actually executing the interpreter that will execute the 
program. This means that the execution time required for the interpreter to load
(interpret) every function and definition is also counted in the execution time
of the program, and therefore, we can't measure the computation time of the
program itself.