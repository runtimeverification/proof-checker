# CSL Examples

## Risc 0
|     Examples     |  Cycles | CPU Execution Time | CPU Prove Time | CPU Verify Time | CPU Total Time | GPU Time |
|:----------------:|:-------:|:------------------:|:--------------:|:---------------:|:--------------:|:--------:|
| perceptron       |  21156  |         28         |      2.397     |        29       |      2.426     |   0.621  |
| svm5             |  21156  |         17         |      2.417     |        18       |      2.435     |   0.622  |
| transfer5000     | 724258  |         58         |     38.344     |        59       |     38.403     |   7.586  |
| transfer         |  21156  |         28         |      2.429     |        30       |      2.459     |   0.597  |
                                        

## zkLLVM
|     Examples     | CPU Time | GPU Time |
|:----------------:|:--------:|:--------:|
| perceptron       |   0.198  |          |
| svm5             |   0.197  |          |
| transfer5000     |  43.994  |          |
| transfer         |   0.198  |          |


## Lurk
|     Examples     |  Cycles | CPU Time** | GPU Time |
|:----------------:|:-------:|:--------:|:--------:|
| perceptron       |    11   |   3.979  |   2.328  |
| svm5             |    9    |   2.263  |   2.278  |
| transfer5000*    |  330387 | 1766.207 | 481.500  |
| transfer         |    34   |   2.522  |   2.441  |


* Using `lurk --rc 400 transfer5000.lurk`, other tests doesn't use `--rc`

# Proof Checker

## Risc 0
|             Examples            |  Cycles | CPU Execution Time | CPU Prove Time | CPU Verify Time | CPU Total Time | GPU Time |
|:-------------------------------:|:-------:|:------------------:|:--------------:|:---------------:|:--------------:|:--------:|
| perceptron-goal                 | 3196173 |         50         |     124.330    |        56       |     122.839    |  28.088  |
| svm5-goal                       | 3196173 |         68         |     124.485    |        74       |     123.670    |  27.998  |
| transfer-batch-1k-goal          | 6724225 |        130         |     275.887    |       142       |     273.092    |  60.219  |
| transfer-simple-compressed-goal | 1123933 |         52         |      48.981    |        55       |      48.555    |  10.742  |
| transfer-task-specific          |   89321 |         27         |       4.909    |        28       |       4.804    |   1.177  |
| impreflex-compressed-goal       |   68555 |         17         |       4.915    |        18       |       4.740    |   1.156  |

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
|             Examples            | Cycles | CPU Time** | GPU Time |
|:-------------------------------:|:------:|:--------:|:--------:|
| perceptron-goal                 | 6404208|     ∞    |          |
| svm5-goal                       | 6404208|     ∞    |          |
| transfer-batch-1k-goal          |30122047|     ∞    |          |
| transfer-simple-compressed-goal | 3202986|     ∞    |          |
| transfer-task-specific*         | 148870 |  861.443 |  237.319 |
| impreflex-compressed-goal*      | 55651  |  341.466 |  220.180 |

* Using `lurk --rc 400 ...`
** CPU time is outdated as we can't get only CPU execution due to a bug on Lurk's
own implementation