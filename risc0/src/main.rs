use zk_host::methods::{GUEST_ELF, GUEST_ID};

use risc0_zkvm::{
    default_executor_from_elf,
    serde::{from_slice, to_vec},
    ExecutorEnv,
};

fn main() {
    let env = ExecutorEnv::builder().build().unwrap();
    let mut exec = default_executor_from_elf(env, GUEST_ELF).unwrap();
    let session = exec.run().unwrap();
    let receipt = session.prove().unwrap();
    receipt.verify(GUEST_ID).unwrap();
}
