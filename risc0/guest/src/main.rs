#![no_main]

use risc0_zkvm::guest::env;
risc0_zkvm::guest::entry!(main);

use std::io::Read;

extern crate checker;
use checker::verify;

pub fn main() {
    let mut stdin_stream = env::stdin().bytes();

    let next = &mut (|| {
        match stdin_stream.next() {
            Some(Ok(v)) => Some(v),
            // TODO: Error handling
            Some(Err(_r)) => None,
            None => None
        }
    });

    verify(next);

    // This won't be included once we implement the necessary methods for env::commit(Proved )
    //println!("Finished with stack {:?}", stack);

    // This is optional
    env::commit(&env::get_cycle_count());
}
