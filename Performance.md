# CSL Examples

## Risc 0
|   Examples   |  Cycles | CPU Exec Time | GPU Exec Time | CPU Prove Time | GPU Prove Time | CPU Verify Time | GPU Verify Time | CPU Total Time | GPU Total Time |
|:------------:|:-------:|:-------------:|:-------------:|:--------------:|:--------------:|:---------------:|:---------------:|:--------------:|:--------------:|
| perceptron   |  21156  |     0.028     |     0.027     |      2.322     |      0.595     |      0.029      |      0.028      |      2.351     |      0.624     |
| svm5         |  21156  |     0.029     |     0.017     |      2.326     |      0.673     |      0.031      |      0.018      |      2.357     |      0.691     |
| transfer5000 | 754199  |     0.057     |     0.056     |     37.791     |      7.725     |      0.041      |      0.059      |     37.832     |      7.784     |
| transfer     |  21156  |     0.017     |     0.028     |      2.333     |      0.579     |      0.018      |      0.019      |      2.351     |      0.598     |


## zkLLVM
|     Examples     | CPU Circuit Gen Time | CPU Prove+Verify Time | GPU Time |
|:----------------:|:--------------------:|:---------------------:|:--------:|
| perceptron       |                 0.95 |                 0.135 |          |
| svm5             |                 0.96 |                 0.135 |          |
| transfer         |                 0.97 |                 0.133 |          |
| transfer-batch   |                0.797 |                 40.34 |          |


## Lurk
|     Examples     |  Cycles | CPU Time** | GPU Prove Time | GPU Verify Time | GPU Total Time |
|:----------------:|:-------:|:----------:|:--------------:|:---------------:|:--------------:|
| perceptron       |    11   |            |           0.84 |           0.597 |          1.437 |
| svm5             |    9    |            |           0.82 |           0.607 |          1.427 |
| transfer         |    34   |            |          2.205 |           0.595 |          2.800 |
| transfer5000*    |  330387 |            |        487.322 |           4.899 |        492.221 |

* Using `lurk --rc 400 transfer5000.lurk`, other tests doesn't use `--rc`


## Cairo0
|     Examples     | CPU Exec Time | CPU Prove Time | CPU Verify Time | CPU Total Time |
|:-----------------|:-------------:|:--------------:|:---------------:|:---------------|
| perceptron       |         0.438 |          0.149 |           0.007 |          0.594 |
| svm5             |         0.442 |          0.175 |           0.007 |          0.624 |
| transfer         |         0.441 |          0.185 |           0.008 |          0.634 |
| transfer5000*    |         6.799 |         26.311 |           0.867 |         33.977 |


# Proof Checker

## Risc 0
|             Examples            |  Cycles | CPU Exec Time | GPU Exec Time | CPU Prove Time | GPU Prove Time | CPU Verify Time | GPU Verify Time | CPU Total Time | GPU Total Time |
|:-------------------------------:|:-------:|:-------------:|:-------------:|:--------------:|:--------------:|:---------------:|:---------------:|:--------------:|:--------------:|
| perceptron-goal                 | 3207528 |       50      |     0.079     |     124.330    |     29.055     |        56       |      0.086      |     122.839    |     29.141     |
| svm5-goal                       | 3207528 |       68      |     0.084     |     124.485    |     29.113     |        74       |      0.090      |     123.670    |     29.203     |
| transfer-batch-1k-goal          | 6722986 |      130      |     0.140     |     275.887    |     60.424     |       142       |      0.151      |     273.092    |     60.575     |
| transfer-simple-compressed-goal | 1139247 |       52      |     0.034     |      48.981    |     10.891     |        55       |      0.037      |      48.555    |     10.928     |
| transfer-task-specific          |   88225 |       27      |     0.032     |       4.909    |      1.172     |        28       |      0.033      |       4.804    |      1.205     |
| impreflex-compressed-goal       |   66366 |       17      |     0.019     |       4.915    |      1.112     |        18       |      0.020      |       4.740    |      1.132     |


## zkLLVM
|             Examples            |CPU Circuit Gen Time | CPU Prove+Verify Time | GPU Time |
|:-------------------------------:|:-------------------:|:---------------------:|:--------:|
| impreflex-compressed-goal       |               5.798 |                372.76 |          |
| perceptron-goal                 |             359.743 |                     ∞ |          |
| svm5-goal                       |             359.371 |                     ∞ |          |
| transfer-task-specific          |              11.678 |                784.11 |          |
| transfer-simple-compressed-goal |              91.160 |              7188.792 |          |
| transfer-batch-1k-goal          |                ∞    |                     ∞ |          |


## Lurk
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
