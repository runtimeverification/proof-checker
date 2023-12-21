from typing import list

circom_P = 21888242871839275222246405745257275088548364400416034343698204186575808495617 
P = circom_P

# Randomly chosen :)
r = ((P // 17) + 19) % P

# Map string A to polynomial P which has A as its coefficients.
# Evaluate P at point r

def fingerprint_str(a: str) -> int:
    return sum([r ** i * ord(a[i]) for i in range(len(a))]) % P

# Map multiset A to the polynomial P for which A is the exact multiset of roots.
# E.g, map {1, 2, 2} to P = (X - 1)(X - 2)(X - 2)
# Evaluate P at point r.
def fingerprint_set(s: list[int]) -> int:
    res = 1
    for elem in s:
        res = (res * (r - elem)) % P
    return res

class ExplicitPattern():
    def __init__(self, content: str): 
        self.content = content

    def implicit(self):
        return ImplicitPattern(
            hash=fingerprint_str(self.content),
            length=len(self.content)
        )

class ImplicitPattern():
    def __init__(self, hash: int, length: int):
        self.hash = hash
        self.length = length

    def concat(self, other: 'ImplicitPattern'):
        self.length = (self.length + other.length) % P
        self.hash = (self.hash + other.hash * (r ** self.length)) % P

class Artefact():
    def __init__(
        self,
        ipat: ImplicitPattern(),
        hint: int
    ): 
        self.ipat = ipat
        self.hint = hint
    
    def hashed(self):
        return hash(self)

class ProofStep():
    # Multiset of artefacts REQUIRED by this proof step
    def obligations(self) -> list[Artefact]:
        raise NotImplementedError
    
    # Multiset of artefacts PRODUCED by this proof step
    def proofs(self) -> list[Artefact]:
        raise NotImplementedError

class Prop1(ProofStep):
    def __init__(
        self,
        ipat_a: ImplicitPattern,
        ipat_b: ImplicitPattern,
        index: int
    ): 
        self.a = ipat_a
        self.b = ipat_b
        self.index = index

    def obligations(self) -> list[Artefact]:
        return [
            Artefact(ipat=self.a, hint= 0),
            Artefact(ipat=self.b, hint= 0)
        ]

    # Construct "->a->ba" from "a" and "b"
    def proofs(self) -> list[Artefact]:
        h_res: int = 1
        len_res: int = 2 * len_a + len_b + 2

        return [
            Artefact(ipat= prop1_inst,hint=self.index)
        ]

def check_proof(C: int, M: int, N: int) -> bool:
