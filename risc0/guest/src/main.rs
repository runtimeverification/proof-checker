#![no_main]
#![no_std]

extern crate checker;
use checker::test_phi_implies_phi;

use risc0_zkvm::guest::env;

risc0_zkvm::guest::entry!(main);

pub fn main() {
    test_phi_implies_phi();
}
