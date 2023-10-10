# zkLLVM implementation for Proof-Checker

## Setting up zkLLVM
There is a list of dependencies that need to be installed before zkLLVM can be built:
```bash
sudo apt install build-essential libssl-dev cmake clang-12 git curl pkg-config libspdlog-dev
```

For the complete list of dependencies, please refer to the [zkllvm#install-dependencies](https://github.com/NilFoundation/zkllvm#install-dependencies).

After installing the dependencies, we can clone and build zkLLVM:
```bash
git clone --recurse-submodules git@github.com:NilFoundation/zkllvm.git
cd zkllvm
```
=Nil; Foundation uses "Unix Makefiles" as a CMake generator. Personally, I use "Ninja" as a CMake generator, as I have experienced faster builds with it, especially with increment builds. Both are fine.
Install Ninja dependencie.
```bash
sudo apt-get install ninja-build
```

Then, we can finally configure the CMake and build the zkLLVM compiler:
```bash
cmake -G "Ninja" -B ${ZKLLVM_BUILD:-build} -DCMAKE_BUILD_TYPE=Release -DCIRCUIT_ASSEMBLY_OUTPUT=TRUE .
ninja -C ${ZKLLVM_BUILD:-build} assigner clang -j$(nproc)
```
`clang` is the zkLLVM compiler, and `assigner` is the tool that assigns the input to the circuit and can tell us if the circuit is satisfiable or not.
From their official documentation: 
> You can also run the assigner with the --check flag to validate the satisfiability of the circuit. If the circuit is satisfiable, the assigner will output the satisfying assignment in the assignment.tbl file. If there is an error, the assigner will output the error message and throw an exception via std::abort.

Further reading for zkLLVM usage: [zkllvm#usage](https://github.com/NilFoundation/zkllvm#usage).

