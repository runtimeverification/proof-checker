#from typing import list
#from copy import deepcopy

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

    def concat(self, other: 'ImplicitPattern') -> 'ImplicitPattern':
        self.length = (self.length + other.length) % P
        self.hash = (self.hash + other.hash * (r ** self.length)) % P

class Artefact():
    def __init__(
        self,
        ipat: ImplicitPattern,
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
    

class ExplicitCommitment(ProofStep):
    def __init__(
            self,
            pattern: ExplicitPattern
    ):
        self.pattern = pattern

    def obligations(self) -> list[Artefact]:
        return []

    def proofs(self) -> list[Artefact]:
        return Artefact(
            ipat=self.pattern.implicit(),
            # 0 as a hint is ONLY used for ExplicitCommitments
            hint=0
        )

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
        prop1_inst: ImplicitPattern = ExplicitPattern("->") \
            .implicit() \
            .concat(self.a) \
            .concat(ExplicitPattern("->").implicit()) \
            .concat(self.b) \
            .concat(self.a)

        return [
            Artefact(ipat= prop1_inst,hint=self.index)
        ]

class Prop2(ProofStep):
    def __init__(
        self,
        ipat_a: ImplicitPattern,
        ipat_b: ImplicitPattern,
        ipat_c: ImplicitPattern,
        index: int
    ): 
        self.a = ipat_a
        self.b = ipat_b
        self.c = ipat_c
        self.index = index

    def obligations(self) -> list[Artefact]:
        return [
            Artefact(ipat=self.a, hint=0),
            Artefact(ipat=self.b, hint=0),
            Artefact(ipat=self.c, hint=0),
        ]

    # Construct "->->a->bc->->ab->ac" from "a" and "b"
    def proofs(self) -> list[Artefact]:
        prop2_inst: ImplicitPattern = ExplicitPattern("->") \
            .implicit() \
            .concat(ExplicitPattern("->").implicit()) \
            .concat(ExplicitPattern("->").implicit()) \
            .concat(self.a) \
            .concat(ExplicitPattern("->").implicit()) \
            .concat(self.b) \
            .concat(self.c) \
            .concat(ExplicitPattern("->").implicit()) \
            .concat(ExplicitPattern("->").implicit()) \
            .concat(self.a) \
            .concat(self.b) \
            .concat(ExplicitPattern("->").implicit()) \
            .concat(self.a) \
            .concat(self.c)

        return [
            Artefact(ipat= prop2_inst,hint=self.index)
        ]
    
class ModusPonens(ProofStep):
    # Premise1: a
    # Premise2: -> a b
    # Conclusion: b

    def __init__(
        self,
        artefact_a: Artefact,
        ipat_b: ImplicitPattern,
        hint_ab: int,
        index: int
    ): 
        self.artefact_a = artefact_a
        self.ipat_b = ipat_b
        self.hint_ab = hint_ab
        self.index = index

        # We will produce an artefact for b, timestamped with curr index
        self.artefact_b = Artefact(
            ipat=ipat_b,
            hint=self.index
        )

        # Implicit pattern for the implication premise obtained
        # via concatenation
        self.ipat_ab = ExplicitPattern("->").implicit() \
            .concat(artefact_a.ipat) \
            .concat(ipat_b)
        
        # Artefact for impl. premise assembled with user-given hint
        self.artefact_ab = Artefact(
            ipat=self.ipat_ab,
            hint=hint_ab
        )
    
    def obligations(self) -> list[Artefact]:
        return [
            self.artefact_a,
            self.artefact_ab
        ]
    
    def proof(self) -> list[Artefact]:
        return [
            self.artefact_b
        ]

def check_proof(
        explicit_patterns: list[ExplicitPattern], 
        proof_steps: list[Prop1 | Prop2 | ModusPonens]
    ) -> bool:

    obligation_set = set()
    proof_set = set()

    for pattern in explicit_patterns:
        ecom = ExplicitCommitment(pattern)
        obligation_set.add(ecom.obligations())
        proof_set.add(ecom.proofs())

    for step in proof_steps:
        obligation_set.add(step.obligations())
        proof_set.add(step.proofs())

    assert proof_set == obligation_set