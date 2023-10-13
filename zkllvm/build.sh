#!/bin/bash

if [[ "$#" -lt 2 ]]; then
  echo "Usage ./build <program> <input> [ll/bc] (default: ll)"
  exit 1
fi

# Check if ZKLLVM_ROOT is set
if [[ -z "${ZKLLVM_ROOT}" ]]; then
  echo "ZKLLVM_ROOT is not set"
  exit 1
fi

#set -x

FILE=$(basename "${1}")
FILEPATH=$(dirname "$(realpath "${1}")")
FILENAME=${FILE%%.*}
OUTPUTDIR="output"
EXT=${FILE##*.}
INPUT=$2

LLVM_EXT=
LLVM_OUT=
if [[ ! -d "${OUTPUTDIR}" ]]; then
  mkdir "${OUTPUTDIR}"
fi

if [[ "$#" -eq 4 ]]; then
  LLVM_EXT=$4
else
  LLVM_EXT=ll
fi

if [[ "$LLVM_EXT" == "ll" ]]; then
  LLVM_OUT=-S
else
  LLVM_OUT=-c
fi

CRYPTO3_LIB_DIR="${ZKLLVM_ROOT}"/libs/crypto3
CLANG_EXE="${ZKLLVM_ROOT}"/build/libs/circifier/llvm/bin/clang-16
LLVM_LINK="${ZKLLVM_ROOT}"/build/libs/circifier/llvm/bin/llvm-link
LIB_C="${ZKLLVM_ROOT}/build/libs/stdlib/libc"
ASSIGNER="${ZKLLVM_ROOT}"/build/bin/assigner/assigner
TRANSPILER="${ZKLLVM_ROOT}"/build/bin/transpiler/transpiler

# Intermediary outputs:
OUTPUT_CLANG="${OUTPUTDIR}/${FILENAME}_${EXT}_example_no_stdlib_${FILENAME}.${EXT}.${LLVM_EXT}"
OUTPUT_LLVM_LINK_1="${OUTPUTDIR}/${FILENAME}_${EXT}_example_no_stdlib.${LLVM_EXT}"
OUTPUT_LLVM_LINK_2="${OUTPUTDIR}/${FILENAME}_${EXT}_example.${LLVM_EXT}"

# Final outputs:
OUTPUT_CIRCUIT="${OUTPUTDIR}/circuit.crct"
OUTPUT_TABLE="${OUTPUTDIR}/assignment_table.tbl"

${CLANG_EXE} -target assigner -D__ZKLLVM__ \
-I "${CRYPTO3_LIB_DIR}"/libs/algebra/include \
-I "${ZKLLVM_ROOT}"/build/include \
-I "${CRYPTO3_LIB_DIR}"/libs/block/include \
-I  /usr/include \
-I "${ZKLLVM_ROOT}"/libs/blueprint/include \
-I "${CRYPTO3_LIB_DIR}"/libs/codec/include \
-I "${CRYPTO3_LIB_DIR}"/libs/containers/include \
-I "${CRYPTO3_LIB_DIR}"/libs/hash/include \
-I "${CRYPTO3_LIB_DIR}"/libs/kdf/include \
-I "${CRYPTO3_LIB_DIR}"/libs/mac/include \
-I "${CRYPTO3_LIB_DIR}"/libs/marshalling/core/include \
-I "${CRYPTO3_LIB_DIR}"/libs/marshalling/algebra/include \
-I "${CRYPTO3_LIB_DIR}"/libs/marshalling/multiprecision/include \
-I "${CRYPTO3_LIB_DIR}"/libs/marshalling/zk/include \
-I "${CRYPTO3_LIB_DIR}"/libs/math/include \
-I "${CRYPTO3_LIB_DIR}"/libs/modes/include \
-I "${CRYPTO3_LIB_DIR}"/libs/multiprecision/include \
-I "${CRYPTO3_LIB_DIR}"/libs/passhash/include \
-I "${CRYPTO3_LIB_DIR}"/libs/pbkdf/include \
-I "${CRYPTO3_LIB_DIR}"/libs/threshold/include \
-I "${CRYPTO3_LIB_DIR}"/libs/pkpad/include \
-I "${CRYPTO3_LIB_DIR}"/libs/pubkey/include \
-I "${CRYPTO3_LIB_DIR}"/libs/random/include \
-I "${CRYPTO3_LIB_DIR}"/libs/stream/include \
-I "${CRYPTO3_LIB_DIR}"/libs/vdf/include \
-I "${CRYPTO3_LIB_DIR}"/libs/zk/include \
-I "${ZKLLVM_ROOT}"/libs/stdlib/libcpp \
-I "${ZKLLVM_ROOT}"/libs/stdlib/libc/include \
-emit-llvm -O1 "${LLVM_OUT}" "${FILEPATH}/${FILE}" -o "${OUTPUT_CLANG}"

${LLVM_LINK} "${LLVM_OUT}" "${OUTPUT_CLANG}" -o "${OUTPUT_LLVM_LINK_1}"
${LLVM_LINK} "${LLVM_OUT}" "${OUTPUT_LLVM_LINK_1}" "${LIB_C}/zkllvm-libc.${LLVM_EXT}" -o "${OUTPUT_LLVM_LINK_2}"
echo "Circuit Function output: "
${ASSIGNER} -b "${OUTPUT_LLVM_LINK_2}" -i "${INPUT}" -c "${OUTPUT_CIRCUIT}" -t "${OUTPUT_TABLE}" -e pallas --print_circuit_output --check
${TRANSPILER} -m gen-test-proof -i "${INPUT}" -c "${OUTPUT_CIRCUIT}" -t "${OUTPUT_TABLE}" -o "${OUTPUTDIR}"
