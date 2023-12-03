#!/bin/bash
# Usage: bench.sh <output file> [example name]

if [ -z "$1" ]; then
    echo "Usage: bench.sh <output file> [example name]"
    exit 1
fi

output_file="$1"

# print_output
print_output() {
    echo "$1" | grep -E "R0VM\[" | awk -F "] " '{print $2}' >> "$output_file"
    echo "$1" | grep -E "Running execution \+ ZK certficate generation \+ verification" >> "$output_file"
    echo "---------------------------------------------------------------------" >> "$output_file"
}

# svm5
svm5() {
    echo "Running svm5"
    cp methods/guest/src/svm5.rs methods/guest/src/main.rs
    output=$(RUST_LOG=info cargo run)
    print_output "$output"
}

# perceptron
perceptron() {
    echo "Running perceptron"
    cp methods/guest/src/perceptron.rs methods/guest/src/main.rs
    output=$(RUST_LOG=info cargo run)
    print_output "$output"
}

# transfer
transfer() {
    echo "Running transfer"
    cp methods/guest/src/transfer.rs methods/guest/src/main.rs
    output=$(RUST_LOG=info cargo run)
    print_output "$output"
}

# transfer5000
transfer5000() {
    echo "Running transfer5000"
    cp methods/guest/src/transfer5000.rs methods/guest/src/main.rs
    output=$(RUST_LOG=info cargo run)
    print_output "$output"
}

all() {
    echo "Running all examples"
    svm5
    perceptron
    transfer
    transfer5000
}

cd csl-examples

if [ -z "$2" ]; then
    all
else
    "$2"
fi

rm methods/guest/src/main.rs
mv "$1" ../"$1"
cd ..