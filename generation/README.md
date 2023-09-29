# Matching Logic Proof Generation


## Installation

Prerequsites: `python >= 3.10`, `pip >= 20.0.2`, `poetry >= 1.3.2`.

```bash
make build
pip install dist/*.whl
```


## For Developers

Use `make` to run common tasks (see the [Makefile](Makefile) for a complete list of available targets).

* `make build`: Build wheel
* `make check`: Check code style
* `make format`: Format code
* `make test-unit`: Run unit tests

For interactive use, spawn a shell with `poetry shell` (after `poetry install`), then run an interpreter.

## Generating Transfer-Batch Proofs

For larger examples, like `transfer-batch`, proof generation may be accomplished through a staged process,
which is documented in the bash script `scripts/gen-transfer-batch-mm-proof.sh`.

Proof generation artifacts for the `transfer-batch` example in particular, which were produced using the
script above can be found in this [RV shared directory](https://drive.google.com/drive/folders/1ZV-vcvs8KYVEifdxM5U2VyoAi6OXajBM).
