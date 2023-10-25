#!/bin/bash
###############################################################################
# This script
# 1) generates a matching logic proof for a concrete execution of a program
# 2) generates a ZK certificate for this proof
#
#
# Note: It assumes an installed, recent-enough version of K that is capable of
# producing proof hints
#
##############################################################################

./gen-execution-proof-hints.sh $1 $2 $3

poetry -C generation run python -m "kore_transfer.proof_gen" $1 $3 .build/kompiled-definitions/$1-kompiled --clean --proof-dir ./
