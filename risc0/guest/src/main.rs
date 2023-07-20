#![no_main]
#![no_std]

use risc0_zkvm::guest::env::{self, FdReader};
risc0_zkvm::guest::entry!(main);

use risc0_zkvm::serde::WordRead;
use risc0_zkvm::serde::Error::DeserializeUnexpectedEnd;
use risc0_zkvm::sha::WORD_SIZE;

extern crate checker;
use checker::{verify, Instruction};

struct SimpleBuffer<'a> {
    input: &'a mut FdReader,
    v: [u8; WORD_SIZE],
    index: usize
}

const BUFFER_ERROR : u8 = 99;

fn read_from(input: &mut FdReader, buffer: &mut [u8]) -> u8 {
    // Pads with 0, but it cannot happen we take it as an argument because input needs to contain a BUFFER_EOF
    let read_buffer = (*input).read_padded_bytes(buffer);
    match read_buffer {
      Ok(_r) => (*buffer)[0],
      Err(r) => if r == DeserializeUnexpectedEnd { Instruction::EOF as u8 } else { BUFFER_ERROR }
    }
}

impl<'a> SimpleBuffer<'a> {
    fn next(&mut self) -> Option<u8> {
        if self.index < WORD_SIZE {
          self.index += 1;
          return Some(self.v[self.index - 1]);
        } else {
          read_from(self.input, &mut self.v);
          self.index = 1;
          return Some(self.v[0]);
        }
    }
}

pub fn main() {
    let mut stdin_stream = SimpleBuffer {
        input: &mut env::stdin(),
        v: [0; WORD_SIZE],
        index: WORD_SIZE
    };

    let next = &mut (|| stdin_stream.next());

    verify(next);

    env::commit(&env::get_cycle_count());
}
