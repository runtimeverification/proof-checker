#!/bin/bash
# Usage: bench.sh <output file>

# Iterate over directories
for dir in */; do
    if [ -d "$dir" ]; then
        cd "$dir" || continue
        
        output=$(RUST_LOG=info cargo run)
        
        cd ..
        
        echo "$output" | grep -E "R0VM\[" | awk -F "] " '{print $2}' >> "$1"
        echo "$output" | grep -E "Running execution \+ ZK certficate generation \+ verification" >> "$1"
        echo "---------------------------------------------------------------------" >> "$1"
       
    fi
done
