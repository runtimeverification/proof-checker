#!/bin/bash
# Usage: ./bench.sh <output_file>


# To get the cairo1-run binary, you need to:
# 1. Clone `cairo-vm` in a seperate directory
# 2. Go to `cairo-vm/cairo1-run` directory and run:
#   2.1. `make deps`
#   2.2. `cargo build --release`
#   2.3. `cargo install --locked --path .`
# 3. Now you can use `cairo1-run` binary to execute cairo programs if Cairo's
#    corelib is in the same directory where you're calling the `cairo1-run
#    binary.

# Getting the dependencie necessary to execute `cairo1-run`
if [ ! -d "corelib" ]; then
    git clone https://github.com/starkware-libs/cairo.git \
    && cd cairo \
    && git checkout v2.3.1 \
    && cd .. \
    && mv cairo/corelib/ . \
    && rm -rf cairo/
fi

declare -a arr=("perceptron.cairo"     \
                "svm5.cairo"           \
                "transfer.cairo"       \
                "batch_transfer.cairo" \
               )
BUILDDIR=./.build

if [[ ! -d "${BUILDDIR}" ]]; then
  mkdir "${BUILDDIR}"
else
  rm -r "${BUILDDIR:?}/"
  mkdir "${BUILDDIR}"
fi

PWD=$(pwd);

for f in "${arr[@]}"; do
    echo "$f";
    filename=${f%%.*}
    mkdir "${BUILDDIR}/${filename}"
    echo "$f" >> "${PWD}/$1"

    # Execute
    START=$(date +%s%3N);
    cairo1-run ${filename}.cairo --trace_file "${BUILDDIR}/${filename}/${filename}.trace" --memory_file "${BUILDDIR}/${filename}/${filename}.memory" --layout all_cairo > /dev/null;
    END=$(date +%s%3N);
    TOTAL=$(("$END" - "$START"))
    echo "Execution time" ".." $(("$TOTAL" / 1000)).$(("$TOTAL" % 1000)) "s" >> "$PWD/$1"

    # Prove
    echo "Prove .."  >> "$PWD/$1"
    platinum-prover prove "${BUILDDIR}/${filename}/${filename}.trace" "${BUILDDIR}/${filename}/${filename}.memory" "${BUILDDIR}/${filename}/${filename}.proof" | grep -E "Time spent in proving:" >> "$PWD/$1"

    # Verify
    echo "Verify .." >> "$PWD/$1"
    platinum-prover verify "${BUILDDIR}/${filename}/${filename}.proof" | grep -E "Time spent in verifying:" >> "$PWD/$1"

    echo -e "\n" >> "$PWD/$1";
done;
