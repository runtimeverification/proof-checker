#![no_main]

use risc0_zkvm::guest::env;
risc0_zkvm::guest::entry!(main);

use std::io::Read;

extern crate checker;
use checker::verify;

pub fn main() {
    let mut gamma_stream = env::FdReader::new(10).bytes();
    let gamma_next = &mut (|| {
        match gamma_stream.next() {
            Some(Ok(v)) => Some(v),
            // TODO: Error handling
            Some(Err(_r)) => None,
            None => None
        }
    });

    let mut claims_stream = env::FdReader::new(11).bytes();
    let claim_next = &mut (|| {
        match claims_stream.next() {
            Some(Ok(v)) => Some(v),
            // TODO: Error handling
            Some(Err(_r)) => None,
            None => None
        }
    });

    let mut proof_stream = env::stdin().bytes();
    let proof_next = &mut (|| {
        match proof_stream.next() {
            Some(Ok(v)) => Some(v),
            // TODO: Error handling
            Some(Err(_r)) => None,
            None => None
        }
    });

    verify(gamma_next, claim_next, proof_next);

    // This is optional
    env::commit(&env::get_cycle_count());
}
