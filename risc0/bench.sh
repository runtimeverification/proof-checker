#!/bin/bash
# Usage: bench.sh <output file> [example name]

if [ -z "$1" ]; then
    echo "Usage: bench.sh <output file> [example name]"
    exit 1
fi

output_file="$1"

# print_output
print_output() {
    echo "$2" >> "$output_file"
    echo "$1" | grep -E "Total cycles" >> "$output_file"
    echo "$1" | grep -E "Running execution \+ ZK certficate generation \+ verification" >> "$output_file"
    echo "---------------------------------------------------------------------" >> "$output_file"
}

# svm5
svm5() {
    echo "Running svm5"
    cp guest/src/svm5.rs guest/src/main.rs
    output=$(cargo run)
    print_output "$output" "svm5"
}

# perceptron
perceptron() {
    echo "Running perceptron"
    cp guest/src/perceptron.rs guest/src/main.rs
    output=$(cargo run --release)
    print_output "$output" "perceptron"
}

# transfer
transfer() {
    echo "Running transfer"
    cp guest/src/transfer.rs guest/src/main.rs
    output=$(cargo run --release)
    print_output "$output" "transfer"
}

# transfer5000
transfer5000() {
    echo "Running transfer5000"
    cp guest/src/transfer5000.rs guest/src/main.rs
    output=$(cargo run --release)
    print_output "$output" "transfer5000"
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

rm guest/src/main.rs
mv "$1" ../"$1"
cd ..