use zk_host::methods::{GUEST_ELF, GUEST_ID};

use risc0_zkvm::{default_executor_from_elf, serde::from_slice, ExecutorEnv};

use std::fs::File;
use std::io::BufReader;
use std::time::Instant;

fn main() {
    let now = Instant::now();

    let file_path = std::env::args().nth(1).expect("No proof file path given");

    println!("Setting up env...");
    let f = File::open(file_path).expect("The proof file was not found");
    let reader = BufReader::new(f);

    // First, we construct an executor environment
    let env = ExecutorEnv::builder().stdin(reader).build().unwrap();

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
