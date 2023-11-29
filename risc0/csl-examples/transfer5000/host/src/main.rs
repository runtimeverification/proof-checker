// These constants represent the RISC-V ELF and the image ID generated by risc0-build.
// The ELF is used for proving and the ID is used for verification.
use methods::{CSL_TRANSFER5000_RISC0_ELF, CSL_TRANSFER5000_RISC0_ID};

use risc0_zkvm::{default_prover, ExecutorEnv};
use std::time::Instant;

fn main() {
    // Initialize tracing. In order to view logs, run `RUST_LOG=info cargo run`
    env_logger::init();

    let now = Instant::now();

    // For example:
    let env = ExecutorEnv::builder().build().unwrap();

    // Obtain the default prover.
    let prover = default_prover();

    // Produce a receipt by proving the specified ELF binary.
    let receipt = prover.prove_elf(env, CSL_TRANSFER5000_RISC0_ELF).unwrap();

    receipt.verify(CSL_TRANSFER5000_RISC0_ID).unwrap();

    println!(
        "Running execution + ZK certficate generation + verification took {} s",
        now.elapsed().as_secs()
    );
}
