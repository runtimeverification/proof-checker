use checker::verify;
use std::fs::File;
use std::io::BufReader;
use std::io::Read;

fn file_to_next(arg_index: usize, handler: impl FnOnce() -> String) -> impl FnMut() -> Option<u8> {
    let path = std::env::args().nth(arg_index).unwrap_or_else(|| handler());
    let mut obj = BufReader::new(File::open(path).unwrap()).bytes();
    move || obj.next()?.ok()
}

pub fn main() {
    let proof_index;
    let claim_index;

    if std::env::args().len() >= 3 {
        // If both claim and proof are present, the claim comes first
        proof_index = 2;
        claim_index = 1
    } else {
        // Otherwise, the single non-trivial argument is the proof
        proof_index = 1;
        claim_index = 2;
    }

    let proof_next = &mut (file_to_next(proof_index, || panic!("No proof file path given")));
    let claim_next = &mut (file_to_next(claim_index, || return "/dev/null".to_string()));

    verify(proof_next, claim_next);
}
