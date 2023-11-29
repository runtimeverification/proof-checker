#![no_main]
// If you want to try std support, also update the guest Cargo.toml file
#![no_std]  // std support is experimental


use risc0_zkvm::guest::env;

risc0_zkvm::guest::entry!(main);

extern crate alloc;
#[allow(unused_imports)]
use alloc::string::{String, ToString};

pub fn main() {
    let _address_to: u64 = 12345;
    let amount: u64 = 10;
    let mut _balance_sender: u64 = 100;
    let mut _balance_to: u64 = 200;
    let mut _ret: u64 = 0;
   
    
    if amount > _balance_sender {
        _ret = 0;
    } else {
        _balance_sender = _balance_sender - amount;
        _balance_to = _balance_to + amount;
        _ret = 1;
    }
    
    // commit the result to ZK journal
    env::commit(&_ret);
    
    env::log(&"Ran transfer.\n");
    env::log(&(env::get_cycle_count().to_string() + "\n")); // This took 2 seconds to run
}

