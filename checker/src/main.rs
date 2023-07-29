use checker::verify;
use std::fs::File;
use std::io::BufReader;
use std::io::Read;

pub fn main() {
    let proof_path = std::env::args().nth(1).expect("No proof file path given");
    let mut proof = BufReader::new(File::open(proof_path).unwrap()).bytes();
    let proof_next = &mut (|| match proof.next() {
        Some(Ok(v)) => Some(v),
        Some(Err(_r)) => None,
        None => None,
    });
    verify(proof_next);
}
