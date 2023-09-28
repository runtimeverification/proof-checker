#![no_main]

use risc0_zkvm::guest::env;
risc0_zkvm::guest::entry!(main);

use std::io::Read;

extern crate checker;
use checker::verify;

pub fn main() {
    let mut begin: usize;
    let mut end: usize;

    // TODO: remove all cycle count statements when we are done profiling

    begin = env::get_cycle_count();

    let gamma_buffer = &mut Vec::new();
    let _ = env::FdReader::new(10).read_to_end(gamma_buffer).unwrap();

    let claims_buffer = &mut Vec::new();
    let _ = env::FdReader::new(11).read_to_end(claims_buffer).unwrap();

    let proof_buffer = &mut Vec::new();
    let _ = env::stdin().read_to_end(proof_buffer).unwrap();

    end = env::get_cycle_count();

    // count_0: cycles spent reading input files
    env::commit(&(end - begin));

    begin = env::get_cycle_count();

    verify(&*gamma_buffer, &*claims_buffer, &*proof_buffer);

    end = env::get_cycle_count();

    // count_1: cycles spent verifying the theorem
    env::commit(&(end - begin));

    // count_2: cycles spent throughout
    env::commit(&(env::get_cycle_count()));

}
