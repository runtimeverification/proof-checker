# CSL Examples

## Risc 0
|     Examples     |  Cycles | CPU Time | GPU Time |
|:----------------:|:-------:|:--------:|:--------:|
| perceptron       |         |          |          |
| svm5             |         |          |          |
| transfer5000     |         |          |          |
| transfer         |         |          |          |


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
| perceptron       |    11   |   1.41   |          |
| svm5             |    9    |   0.714  |          |
| transfer5000     |  330387 |          |          |
| transfer         |    34   |          |          |




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
| perceptron-goal                 |        |          |          |
| svm5-goal                       |        |          |          |
| transfer-batch-1k-goal          |        |          |          |
| transfer-simple-compressed-goal |        |          |          |
| transfer-task-specific          |        |          |          |
| impreflex-compressed-goal       |        |          |          |