use zk_host::methods::{GUEST_ELF, GUEST_ID};

use risc0_zkvm::{
    default_executor_from_elf,
    serde::from_slice,
    ExecutorEnv,
};

extern crate checker;
use checker::Instruction;

// TODO: Extract the proof into a file
#[test]
fn impreflex() {
    let proof: &[u8] = &[
        Instruction::Prop1 as u8,              // (p1: phi0 -> (phi1 -> phi0))

        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::MetaVar as u8, 0,         // Stack: p1 ; phi0
        Instruction::Save as u8,               // phi0 save at 0

        Instruction::Instantiate as u8, 1,     // Stack: (p2: phi0 -> (phi0 -> phi0))

        Instruction::Prop1 as u8,              // Stack: p2 ; p1
        Instruction::Load as u8, 0,            // Stack: p2 ; p1 ; phi0
        Instruction::Load as u8, 0,            // Stack: p2 ; p1 ; phi0 ; phi0
        Instruction::Implication as u8,        // Stack: p2 ; p1 ; phi1; phi0 -> phi0
        Instruction::Save as u8,               // phi0 -> phi0 save at 1

        Instruction::Instantiate as u8, 1,     // Stack: p2 ; (p3: phi0 -> ((phi0 -> phi0) -> phi0))

        Instruction::Prop2 as u8,              // Stack: p2 ; p3; (p4: (phi0 -> (phi1 -> phi2)) -> ((phi0 -> phi1) -> (phi0 -> phi2))
        Instruction::Load as u8, 1,
        Instruction::Instantiate as u8, 1,     // Stack: p2 ; p3; (p4: (phi0 -> ((phi0 -> phi0) -> phi2)) -> (p2 -> (phi0 -> phi2))

        Instruction::Load as u8, 0,
        Instruction::Instantiate as u8, 2,     // Stack: p2 ; p3; (p4: p3 -> (p2 -> (phi0 -> phi0))

        Instruction::ModusPonens as u8,        // Stack: p2 ; (p2 -> (phi0 -> phi0))
        Instruction::ModusPonens as u8,        // Stack: phi0 -> phi0
    ];

    // First, we construct an executor environment
    let env = ExecutorEnv::builder()
        .stdin(proof)
        .build()
        .unwrap();

    // Next, we make an executor, loading the (renamed) ELF binary.
    let mut exec = default_executor_from_elf(env, GUEST_ELF).unwrap();

    // Run the executor to produce a session.
    let session = exec.run().unwrap();

    // Prove the session to produce a receipt.
    let receipt = session.prove().unwrap();

    // TODO: Implement code for transmitting or serializing the receipt for
    // other parties to verify here
    let _theorem: usize = from_slice(&receipt.journal).unwrap();

    // Optional: Verify receipt to confirm that recipients will also be able to
    // verify your receipt
    receipt.verify(GUEST_ID).unwrap();
}

