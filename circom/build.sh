circom "$1.circom" --r1cs --wasm --sym --c
cd "$1_cpp"
make
cd ../
