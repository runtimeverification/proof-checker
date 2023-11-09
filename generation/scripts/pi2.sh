#!/bin/bash
###############################################################################
# This script
# 1) generates a matching logic proof for a concrete execution of a program
# 2) generates a ZK certificate for this proof
#
# Note: It assumes an installed, recent-enough version of K that is capable of
# producing proof hints, and running from the generation folder.
#
##############################################################################

./scripts/gen-execution-proof-hints.sh $1 $2 $3/proof-hint.bin

if [[ "$4" == "--pretty" ]]; then
  OPTS="--pretty"
else
  OPTS=""
fi

poetry -C generation run python -m "kore_transfer.proof_gen" $1 $3/proof-hint.bin $3 --reuse --proof-dir ./ $OPTS
