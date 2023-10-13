#!/bin/bash
###############################################################################
# This script generates proof hints for a concrete execution of a program. Use
# --help for usage instructions.
#
# Note: It assumes an installed, recent-enough version of K that is capable of
# producing proof hints
#
##############################################################################

set -e
set -o pipefail
set -u
#set -x

PHGEN=$(basename "$0")

print_usage () {
cat <<HERE
Usage:
  $PHGEN <K-DEFINITION> <PROGRAM> <OUTPUT>
  $PHGEN [-h|--help]
Kompile <K-DEFINITION> and generate proof hints for the concrete execution of
<PROGRAM> and save them to <OUTPUT>. All argument are mandatory.
HERE
}

# Check if the script is invoked with the --help (or -h) flag
if [ "$#" -eq 1 ]; then
  if [[ "$1" == "--help"  || "$1" == "-h" ]]; then
    print_usage
    exit 0
  fi
fi

# Check the number of arguments
if [ "$#" -ne 3 ]; then
  echo "Error: The script requires exactly three positional arguments."
  print_usage
  exit 1
fi

DEF="$1"
PGM="$2"
OUT="$3"

# Check that the input files exist
if [[ ! -f "$DEF" || ! -f "$PGM" ]]; then
  echo "Error: The specified arguments ${DEF} or ${PGM} do not exist."
  print_usage
  exit 1
fi

# Check if required K tools exist
if ! command -v kompile &>/dev/null || ! command -v kparse &>/dev/null || ! command -v llvm-krun &>/dev/null; then
  echo "Error: One or more required tools (kompile, kparse, llvm-krun) does not exist. Make sure you have K installed and that the K binaries are in the current shell's PATH."
  exit 1
fi

# Create a temporary directory for the kompiled semantics
temp_kompiled_dir=$(mktemp -d)

# Kompile the K definition
echo "Compiling $DEF..."
if kompile --backend llvm --output-definition "$temp_kompiled_dir" "$DEF"; then
  echo "Compilation successful."
else
  echo "Error: Compilation of $DEF failed."
  rm -Rf "$temp_kompiled_dir"
  exit 1
fi

# Create a temporary file for intermediate results
temp_file=$(mktemp)

# Parse the program into kore
if ! kparse "$PGM" --definition "$temp_kompiled_dir" > "$temp_file"; then
  echo "Error: kparse command failed."
  rm -f "$temp_file"
  rm -Rf "$temp_kompiled_dir"
  exit 1
else
  echo "Input program parsed successfully."
fi

# Construct the initial configuration's kore term
if ! llvm-krun -c PGM "$temp_file" KItem korefile --directory "$temp_kompiled_dir" --dry-run -nm -o "$temp_file"; then
  echo "Error: llvm-krun command failed."
  rm -f "$temp_file"
  rm -Rf "$temp_kompiled_dir"
  exit 1
else
  echo "Input configuration kore term genereated successfully."
fi

# Execute the interpreter and generate proof hints
if ! ${temp_kompiled_dir}/interpreter "$temp_file" -1 "$OUT" --proof-output; then
  echo "Error: Interpreter command failed."
  rm -f "$temp_file"
  rm -Rf "$temp_kompiled_dir"
  exit 1
else
  echo "Proof hints generated successfully."
fi

# Clean up the temporary files/directories
rm -f "$temp_file"
rm -Rf "$temp_kompiled_dir"
