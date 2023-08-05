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

    let claim_path = std::env::args().nth(2).unwrap_or("/dev/null".to_string());
    let mut claim = BufReader::new(File::open(claim_path).unwrap()).bytes();
    let claim_next = &mut (|| match claim.next() {
        Some(Ok(v)) => Some(v),
        Some(Err(_r)) => None,
        None => None,
    });

    verify(proof_next, claim_next);
}
