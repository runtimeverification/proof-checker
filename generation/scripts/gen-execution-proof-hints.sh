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

remove_files() {
  local files=("$@")

  for file in "${files[@]}"; do
    rm -r "$file"
  done
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

filename=$(basename -- "$DEF")
MOD="${filename%.*}"

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

# Keep track of temp files/dirs created
all_temps=()

# Check if a kompiled definition already exists at .build/kompiled-definitions
if [[ ! -d ".build/kompiled-definitions/${MOD}-kompiled/" ]]; then
  # Create a temporary directory for the kompiled semantics
  kompiled_dir=$(mktemp -d)
  all_temps+=(${kompiled_dir})
  # Kompile the K definition
  echo "Compiling $DEF..."
  if kompile --backend llvm --llvm-proof-hint-instrumentation --output-definition "$kompiled_dir" "$DEF"; then
    echo "Compilation successful."
  else
    echo "Error: Compilation of $DEF failed."
    remove_files "${all_temps[@]}"
    exit 1
  fi
else
  kompiled_dir=".build/kompiled-definitions/${MOD}-kompiled"
  echo "kompiled definition exists: $kompiled_dir"
fi

# Create a temporary file for intermediate results
temp_file=$(mktemp)
all_temps+=(${temp_file})

# Parse the program into kore
if ! kparse "$PGM" --definition "$kompiled_dir" > "$temp_file"; then
  echo "Error: kparse command failed."
  remove_files "${all_temps[@]}"
  exit 1
else
  echo "Input program parsed successfully."
fi

# Execute the interpreter and generate proof hints
if ! llvm-krun --proof-hints --directory "$kompiled_dir" -c PGM "$temp_file" KItem korefile -o "$OUT"; then
  echo "Error: llvm-krun command failed."
  remove_files "${all_temps[@]}"
  exit 1
else
  echo "Proof hints generated successfully."
fi

# Clean up the temporary files/directories
remove_files "${all_temps[@]}"
