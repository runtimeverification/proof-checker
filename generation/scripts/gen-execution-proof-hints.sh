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

# Get the definition's name (without the .k extension)
DEF_NAME="${DEF%.*}"

# Check if the K definition was already kompiled (in the current directory)
if [ ! -d "${DEF_NAME}-kompiled" ]; then
  echo "Compiling $DEF..."
  if kompile "$DEF"; then
    echo "Compilation successful."
  else
    echo "Error: Compilation of $DEF failed."
    exit 1
  fi
else
  echo "Directory ${DEF_NAME}-kompiled already exists. Skipping compilation."
fi

tempFile=$(mktemp)

# Parse the program into kore
if ! kparse "$PGM" --definition "${DEF_NAME}-kompiled" > "$tempFile"; then
  echo "Error: kparse command failed."
  rm -f "$tempFile"
  exit 1
else
  echo "Input program parsed successfully."
fi

# Construct the initial configuration's kore term
if ! llvm-krun -c PGM "$tempFile" KItem korefile --directory "${DEF_NAME}-kompiled" --dry-run -nm -o "$tempFile"; then
  echo "Error: llvm-krun command failed."
  rm -f "$tempFile"
  exit 1
else
  echo "Input configuration kore term genereated successfully."
fi

# Execute the interpreter and generate proof hints
if ! "${DEF_NAME}-kompiled/interpreter" "$tempFile" -1 "$OUT" --proof-output; then
  echo "Error: Interpreter command failed."
  rm -f "$tempFile"
  exit 1
else
  echo "Proof hints generated successfully."
fi

# Clean up the temporary file
rm -f "$tempFile"


