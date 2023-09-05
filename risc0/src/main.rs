use zk_host::methods::{GUEST_ELF, GUEST_ID};

use risc0_zkvm::{default_executor_from_elf, serde::from_slice, ExecutorEnv};

use std::fs::File;
use std::io::BufReader;
use std::time::Instant;

fn main() {
    let now = Instant::now();

    println!("Setting up env...");

    if std::env::args().len() != 4 {
        panic!("Expected 4 arguments. Received {}.", std::env::args().len())
    }

    let gamma_filepath = std::env::args().nth(1).expect("No claim file path given");
    let gamma_file = File::open(gamma_filepath).expect("The gamma file was not found");
    let gamma_reader = BufReader::new(gamma_file);

    let claims_filepath = std::env::args().nth(2).expect("No claim file path given");
    let claims_file = File::open(claims_filepath).expect("The claims file was not found");
    let claims_reader = BufReader::new(claims_file);

    let proof_filepath = std::env::args().nth(3).expect("No proof file path given");
    let proof_file = File::open(proof_filepath).expect("The proof file was not found");
    let proof_reader = BufReader::new(proof_file);

    // First, we construct an executor environment
    let env = ExecutorEnv::builder()
        .read_fd(10, gamma_reader)
        .read_fd(11, claims_reader)
        .stdin(proof_reader)
        .build()
        .unwrap();

    // Next, we make an executor, loading the (renamed) ELF binary.
    let mut exec = default_executor_from_elf(env, GUEST_ELF).unwrap();

    println!("Checking the proof...");

    // Run the executor to produce a session.
    let session = exec.run().unwrap();

    println!("Ran in {} s", now.elapsed().as_secs());

    println!("Generating the certificate...");

    // Prove the session to produce a receipt.
    let receipt = session.prove().unwrap();

    // TODO: Implement code for transmitting or serializing the receipt for
    // other parties to verify here
    let theorem: usize = from_slice(&receipt.journal).unwrap();
    println!(
        "We can prove the theorem in {} cycles and have a ZK certificate for it!",
        theorem
    );

    // Optional: Verify receipt to confirm that recipients will also be able to
    // verify your receipt
    receipt.verify(GUEST_ID).unwrap();

    println!(
        "Running execution + ZK certficate generation + verification took {} s",
        now.elapsed().as_secs()
    );
}
