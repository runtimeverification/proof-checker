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
- `batch-transfer-5k`: a while loop that executes `transfer` for 5000 times; 
- `perceptron-5`: a single-layer [perceptron](https://en.wikipedia.org/wiki/Perceptron) 
  with an input vector of length 5
- `svm-5`: a [support vector machine (SVM)](https://en.wikipedia.org/wiki/Support_vector_machine)
  model that classifies data points in a 5-dimensional space. 

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

### Direct Implementation

#### Risc 0: v0.16.1
|   Examples   |  Cycles | CPU Exec Time | GPU Exec Time | CPU Prove Time | GPU Prove Time | CPU Verify Time | GPU Verify Time | CPU Total Time | GPU Total Time |
|:------------:|:-------:|:-------------:|:-------------:|:--------------:|:--------------:|:---------------:|:---------------:|:--------------:|:--------------:|
| perceptron   |  21156  |     0.028     |     0.027     |      2.397     |      0.605     |      0.029      |      0.028      |      2.426     |      0.633     |
| svm5         |  21156  |     0.017     |     0.017     |      2.417     |      0.688     |      0.018      |      0.018      |      2.435     |      0.706     |
| transfer5000 | 724258  |     0.058     |     0.056     |     38.344     |      7.787     |      0.059      |      0.057      |     38.403     |      7.844     |
| transfer     |  21156  |     0.028     |     0.028     |      2.429     |      0.593     |      0.030      |      0.030      |      2.459     |      0.623     |


#### zkLLVM
|     Examples     | CPU Circuit Gen Time | CPU Prove+Verify Time | GPU Time |
|:----------------:|:--------------------:|:---------------------:|:--------:|
| perceptron       |                 0.95 |                 0.135 |          |
| svm5             |                 0.96 |                 0.135 |          |
| transfer         |                 0.97 |                 0.133 |          |
| transfer-batch   |                0.797 |                 40.34 |          |


#### Lurk
|     Examples     |  Cycles | CPU Time** | GPU Prove Time | GPU Verify Time | GPU Total Time |
|:----------------:|:-------:|:----------:|:--------------:|:---------------:|:--------------:|
| perceptron       |    11   |            |           0.84 |           0.597 |          1.437 |
| svm5             |    9    |            |           0.82 |           0.607 |          1.427 |
| transfer         |    34   |            |          2.205 |           0.595 |          2.800 |
| transfer5000*    |  330387 |            |        487.322 |           4.899 |        492.221 |

* Using `lurk --rc 400 transfer5000.lurk`, other tests doesn't use `--rc`


#### Cairo0
|     Examples     | CPU Exec Time | CPU Prove Time | CPU Verify Time | CPU Total Time |
|:-----------------|:-------------:|:--------------:|:---------------:|:---------------|
| perceptron       |         0.438 |          0.149 |           0.007 |          0.594 |
| svm5             |         0.442 |          0.175 |           0.007 |          0.624 |
| transfer         |         0.441 |          0.185 |           0.008 |          0.634 |
| transfer5000*    |         6.799 |         26.311 |           0.867 |         33.977 |


### Proofs of Proofs

#### Risc 0: v0.16.1
|             Examples            |  Cycles | CPU Exec Time | GPU Exec Time | CPU Prove Time | GPU Prove Time | CPU Verify Time | GPU Verify Time | CPU Total Time | GPU Total Time |
|:-------------------------------:|:-------:|:-------------:|:-------------:|:--------------:|:--------------:|:---------------:|:---------------:|:--------------:|:--------------:|
| perceptron-goal                 | 3207528 |       50      |     0.079     |     124.330    |     29.055     |        56       |      0.086      |     122.839    |     29.141     |
| svm5-goal                       | 3207528 |       68      |     0.084     |     124.485    |     29.113     |        74       |      0.090      |     123.670    |     29.203     |
| transfer-batch-1k-goal          | 6722986 |      130      |     0.140     |     275.887    |     60.424     |       142       |      0.151      |     273.092    |     60.575     |
| transfer-simple-compressed-goal | 1139247 |       52      |     0.034     |      48.981    |     10.891     |        55       |      0.037      |      48.555    |     10.928     |
| transfer-task-specific          |   88225 |       27      |     0.032     |       4.909    |      1.172     |        28       |      0.033      |       4.804    |      1.205     |
| impreflex-compressed-goal       |   66366 |       17      |     0.019     |       4.915    |      1.112     |        18       |      0.020      |       4.740    |      1.132     |


#### zkLLVM
|             Examples            |CPU Circuit Gen Time | CPU Prove+Verify Time | GPU Time |
|:-------------------------------:|:-------------------:|:---------------------:|:--------:|
| impreflex-compressed-goal       |               5.798 |                372.76 |          |
| perceptron-goal                 |             359.743 |                     ∞ |          |
| svm5-goal                       |             359.371 |                     ∞ |          |
| transfer-task-specific          |              11.678 |                784.11 |          |
| transfer-simple-compressed-goal |              91.160 |              7188.792 |          |
| transfer-batch-1k-goal          |                ∞    |                     ∞ |          |


#### Lurk
|             Examples            | Cycles | CPU Time** | GPU Prove Time | GPU Verify Time | GPU Total Time |
|:-------------------------------:|:------:|:----------:|:--------------:|:---------------:|:--------------:|
| transfer-task-specific*         | 148870 |    861.443 |        193.836 |           4.199 |        198.035 |
| impreflex-compressed-goal*      | 55651  |    341.466 |        108.962 |           4.209 |        113.171 |
| perceptron-goal                 | 6404208|            |              ∞ |               ∞ |                |
| svm5-goal                       | 6404208|            |              ∞ |               ∞ |                |
| transfer-batch-1k-goal          |30122047|            |              ∞ |               ∞ |                |
| transfer-simple-compressed-goal | 3202986|            |              ∞ |               ∞ |                |

* Using `lurk --rc 400 ...`
** CPU time is outdated as we can't get only CPU execution due to a bug on Lurk's
own implementation
