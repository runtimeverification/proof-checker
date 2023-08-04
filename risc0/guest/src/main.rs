#![no_main]

use risc0_zkvm::guest::env;
risc0_zkvm::guest::entry!(main);

use std::io::Read;

extern crate checker;
use checker::verify;

pub fn main() {
    let mut proof_stream = env::stdin().bytes();
    let mut _claims_stream = env::FdReader::new(10).bytes();

    let next = &mut (|| {
        match proof_stream.next() {
            Some(Ok(v)) => Some(v),
            // TODO: Error handling
            Some(Err(_r)) => None,
            None => None
        }
    });

    verify(next, vec![]);

    // This is optional
    env::commit(&env::get_cycle_count());
}
