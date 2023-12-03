#!/bin/bash
# Usage: bench.sh <output file>


cd csl-examples

for file in methods/guest/src/*.rs; do
    echo $file
    cp "$file" methods/guest/src/main.rs

    output=$(RUST_LOG=info cargo run)

    echo "$output" | grep -E "R0VM\[" | awk -F "] " '{print $2}' >> "$1"
    echo "$output" | grep -E "Running execution \+ ZK certficate generation \+ verification" >> "$1"
    echo "---------------------------------------------------------------------" >> "$1"

done

rm methods/guest/src/main.rs
mv "$1" ../"$1"
cd ..