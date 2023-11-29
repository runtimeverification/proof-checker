# CSL Examples

## Risc 0
|     Examples     |  Cycles | CPU Time | GPU Time |
|:----------------:|:-------:|:--------:|:--------:|
| perceptron       |  23583  |     4    |          |
| svm5             |  22489  |     4    |          |
| transfer5000     | 1401989 |   104    |          |
| transfer         |  22489  |     4    |          |

## zkLLVM
|     Examples     | CPU Time | GPU Time |
|:----------------:|:--------:|:--------:|
| perceptron       |   0.198  |          |
| svm5             |   0.197  |          |
| transfer5000     |  43.994  |          |
| transfer         |   0.198  |          |


## Lurk
|     Examples     |  Cycles | CPU Time | GPU Time |
|:----------------:|:-------:|:--------:|:--------:|
| perceptron       |    11   |   3.979  |          |
| svm5             |    9    |   2.263  |          |
| transfer5000*    |  330387 | 1766.207 |          |
| transfer         |    34   |   2.522  |          |


* Using `lurk --rc 400 transfer5000.lurk`, other tests doesn't use `--rc`

# Proof Checker

## Risc 0
|             Examples            |  Cycles | CPU Time | GPU Time |
|:-------------------------------:|:-------:|:--------:|:--------:|
| perceptron-goal                 | 3198648 |      124 |          |
| svm5-goal                       | 3198648 |      123 |          |
| transfer-batch-1k-goal          | 6721800 |      275 |          |
| transfer-simple-compressed-goal | 1120651 |       49 |          |
| transfer-task-specific          |   88227 |        4 |          |
| impreflex-compressed-goal       |   67461 |        4 |          |

## zkLLVM
|             Examples            | CPU Time | GPU Time |
|:-------------------------------:|:--------:|:--------:|
| perceptron-goal                 |     ∞    |          |
| svm5-goal                       |     ∞    |          |
| transfer-batch-1k-goal          |     ∞    |          |
| transfer-simple-compressed-goal | 8066.663 |          |
| transfer-task-specific          |  878.184 |          |
| impreflex-compressed-goal       |  417.277 |          |

## Lurk
|             Examples            | Cycles | CPU Time | GPU Time |
|:-------------------------------:|:------:|:--------:|:--------:|
| perceptron-goal                 | 6404208|     ∞    |          |
| svm5-goal                       | 6404208|     ∞    |          |
| transfer-batch-1k-goal          |30122047|     ∞    |          |
| transfer-simple-compressed-goal | 3202986|     ∞    |          |
| transfer-task-specific*         | 148870 |  861.443 |          |
| impreflex-compressed-goal*      | 55651  |  341.466 |          |

* Using `lurk --rc 400 ...`
