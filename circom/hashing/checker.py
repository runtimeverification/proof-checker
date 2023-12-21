from typing import list

circom_P = 21888242871839275222246405745257275088548364400416034343698204186575808495617 
P = circom_P

r = ((P // 17) + 19) % P

def fingerprint_str(a: str) -> int:
    return sum([r ** i * ord(a[i]) for i in range(len(a))]) % P

def fingerprint_concat(h_a: int, len_a: int, h_b: int, len_b: int) -> int:
    len_ab = len_a + len_b
    return (len_a + len_b, h_a + h_b * (r ** len_a) % P)

def fingerprint_set(s: list[int]) -> int:
    res = 1
    for elem in s:
        res = (res * (r - elem)) % P
    return res

class Artefact():
    def __init__(
        self,
        pattern_hash_: int,
        pattern_length: int,
        hint: int
    ): 
        self.pattern_hash_ = pattern_hash
        self.pattern_length = pattern_length
        self.hint = hint
    
    def hashed(self):
        return hash(self)

class ProofStep():
    def obligations() -> list[Artefact]:
        raise NotImplementedError
    
    def proofs() -> list[Artefact]:
        raise NotImplementedError

class Prop1(ProofStep):
    def __init__(
        self,
        h_a: int,
        len_a: int,
        h_b: int,
        len_b: int,
        index: int
    ): 
        self.h_a = h_a
        self.len_a = len_a
        self.h_b = h_b
        self.len_b = len_b

    def obligations() -> list[Artefact]:
        return [
            Artefact(pattern_hash: h_a, pattern_length: len_a, hint: 0),
            Artefact(pattern_hash: h_b, pattern_length: len_b, hint: 0)
        ]

    # Constructing "->a->ba" from "a" and "b"
    def proofs() -> list[Artefact]:
        h_res: int = 1
        len_res: int = 2 * len_a + len_b + 2

        return [
            Artefact(pattern_hash: h_res, pattern_length: len_res, hint: index)
        ]

def check_proof(C: int, M: int, N: int) -> bool:
