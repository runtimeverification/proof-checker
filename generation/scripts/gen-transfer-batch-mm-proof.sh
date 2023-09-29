#! /bin/bash

###############################################################################
# This script generates a proof object for the last proof hint fragment for the
# transfer batch example in IMP5.
#
# Usage:
# This script is meant to be run on the k-proof-generation repo here:
# https://github.com/fiedlr/k-proof-generation. Therefore, to use this script:
#
# 1. Clone the repo and follow the instructions in the README. Make sure you
#    are able to generate proofs as per the instructions without issues.
# 2. In the project's root directory, create a new directory
#    "mm-proof-transfer-batch".
# 3. Copy this script over to the newly created directory
# 4. Configure the parameters below as needed, and then run the script.
#
##############################################################################

directory="kompiled"
depth=1000
output="output-proof-object"

if [ ! -d "${directory}" ]; then
    echo "kompiling IMP5"
    kompile \
         --backend haskell \
         --directory ${directory} \
         --main-module IMP5 \
         --debug \
         ../examples/csl23/imp5.k
fi

echo "Generating the initial configuration ..."
krun  \
     --directory ${directory} \
     --depth 0 \
     --output kore \
     --output-file config-0.kore \
     ../examples/csl23/blockchain/transfer-batch.imp5

echo "Generating proof hints in stages ..."
i=1
while true; do
    last=$((i - 1))
    echo "Stage $i (config-${last} ~>* config-${i}) ..."
    krun \
         --directory ${directory} \
         --depth ${depth} \
         --output kore \
         --output-file config-${i}.kore \
         --term \
         --parser cat \
         --haskell-backend-command "kore-exec --trace-rewrites proof-hint-${i}.yaml" \
         config-${last}.kore
    if cmp -s "proof-hint-${i}.yaml" "proof-hint-${last}.yaml"; then
        break
    fi
    ((i++))
done

last=$((last - 1))
echo "Generating the proof object for the task proof-hint-${last}.yaml"
pushd $(pwd)/..
python3 -m ml.rewrite.__main__ \
    -o ./mm-proof-transfer-batch/${output} \
    --prelude theory/prelude.mm \
    --task ./mm-proof-transfer-batch/proof-hint-${last}.yaml \
    --standalone \
    ./mm-proof-transfer-batch/${directory}/imp5-kompiled/definition.kore \
    IMP5
popd


