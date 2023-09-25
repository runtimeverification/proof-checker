use checker::verify;
use std::fs::File;
use std::io::BufReader;
use std::io::Read;

pub fn main() {
    for _ in 0..100000 {
        let (mut gamma_reader, mut claims_reader, mut proof_reader) = match std::env::args().len() {
            3 => (
                BufReader::new(File::open(std::env::args().nth(1).unwrap()).unwrap()).bytes(),
                BufReader::new(File::open("/dev/null").unwrap()).bytes(),
                BufReader::new(File::open(std::env::args().nth(2).unwrap()).unwrap()).bytes(),
            ),
            4 => (
                BufReader::new(File::open(std::env::args().nth(1).unwrap()).unwrap()).bytes(),
                BufReader::new(File::open(std::env::args().nth(2).unwrap()).unwrap()).bytes(),
                BufReader::new(File::open(std::env::args().nth(3).unwrap()).unwrap()).bytes(),
            ),
            _ => panic!("Usage: checker gamma-file [claims-file] proof-file"),
        };

        let gamma_next = &mut (|| gamma_reader.next()?.ok());
        let claims_next = &mut (|| claims_reader.next()?.ok());
        let proof_next = &mut (|| proof_reader.next()?.ok());

        verify(gamma_next, claims_next, proof_next);
    }
}
