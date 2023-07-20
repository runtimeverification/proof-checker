use zk_host::methods::{GUEST_ELF, GUEST_ID};

use risc0_zkvm::{
    default_executor_from_elf,
    serde::{from_slice, to_vec},
    ExecutorEnv,
};

extern crate checker;
use checker::Instruction;
use std::time::Instant;

fn main() {
    let now = Instant::now();

    let proof: &[u8] = &[
        Instruction::Prop1 as u8,               // (p1: phi0 -> (phi1 -> phi0))

        Instruction::List as u8, 0 as u8,
        Instruction::List as u8, 0 as u8,
        Instruction::List as u8, 0 as u8,
        Instruction::List as u8, 0 as u8,
        Instruction::List as u8, 0 as u8,
        Instruction::MetaVar as u8, 1 as u8,          // Stack: p1 ; phi1
        Instruction::Save as u8,                // phi1 save at 0

        Instruction::List as u8, 0 as u8,
        Instruction::List as u8, 0 as u8,
        Instruction::List as u8, 0 as u8,
        Instruction::List as u8, 0 as u8,
        Instruction::List as u8, 0 as u8,
        Instruction::MetaVar as u8, 0 as u8,          // Stack: p1 ; phi1 ; phi0
        Instruction::Save as u8,                // phi0 save at 1

        Instruction::InstantiateSchema as u8,   // Stack: (p2: phi0 -> (phi0 -> phi0))

        Instruction::Prop1 as u8,               // Stack: p2 ; p1
        Instruction::Load as u8, 0 as u8,             // Stack: p2 ; p1 ; phi1
        Instruction::Load as u8, 1 as u8,             // Stack: p2 ; p1 ; phi0
        Instruction::Load as u8, 1 as u8,             // Stack: p2 ; p1 ; phi0 ; phi0
        Instruction::Implication as u8,         // Stack: p2 ; p1 ; phi1; phi0 -> phi0

        Instruction::Save as u8,                // phi0 -> phi0 save at 3

        Instruction::InstantiateSchema as u8,   // Stack: p2 ; (p3: phi0 -> (phi0 -> phi0) -> phi0)

        Instruction::Prop2 as u8,               // Stack: p2 ; p3; (p4: (phi0 -> (phi1 -> phi2)) -> ((phi0 -> phi1) -> (phi0 -> phi2))
        Instruction::Load as u8, 0 as u8,
        Instruction::Load as u8, 2 as u8,
        Instruction::InstantiateSchema as u8,

        Instruction::List as u8, 0 as u8,
        Instruction::List as u8, 0 as u8,
        Instruction::List as u8, 0 as u8,
        Instruction::List as u8, 0 as u8,
        Instruction::List as u8, 0 as u8,
        Instruction::MetaVar as u8, 2 as u8,
        Instruction::Load as u8, 1 as u8,
        Instruction::InstantiateSchema as u8,

        Instruction::ModusPonens as u8,
        Instruction::ModusPonens as u8,         // Stack: phi0 -> phi0

        Instruction::EOF as u8,                                    // EOF
    ];

    println!("Setting up env...");

    // First, we construct an executor environment
    let env = ExecutorEnv::builder()
        .stdin(proof)
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
    println!("We can prove the theorem in {} cycles and have a ZK certificate for it!", theorem);

    // Optional: Verify receipt to confirm that recipients will also be able to
    // verify your receipt
    receipt.verify(GUEST_ID).unwrap();

    println!("Running execution + ZK certficate generation + verification took {} s", now.elapsed().as_secs());
}

