use checker::verify;
use std::fs::File;
use std::io::BufReader;
use std::io::Read;

pub fn main() {
    let (mut proof_reader, mut claims_reader) = match std::env::args().len() {
        2 => (
            BufReader::new(File::open(std::env::args().nth(1).unwrap()).unwrap()).bytes(),
            BufReader::new(File::open("/dev/null").unwrap()).bytes(),
        ),
        3 => (
            BufReader::new(File::open(std::env::args().nth(2).unwrap()).unwrap()).bytes(),
            BufReader::new(File::open(std::env::args().nth(1).unwrap()).unwrap()).bytes(),
        ),
        other => panic!("Expected 1 or 2 arguments. Received {}.", other),
    };

    let proof_next = &mut (|| proof_reader.next()?.ok());
    let claims_next = &mut (|| claims_reader.next()?.ok());

    verify(proof_next, claims_next);
}
