#from typing import list
#from copy import deepcopy

circom_P = 21888242871839275222246405745257275088548364400416034343698204186575808495617 
P = circom_P

# Randomly chosen :)
# In practice we want to "Fiat-Shamir" this and derive it from
# a hash of the proof.
# Fiat-Shamir attacks, Zero Knowledge, Nethermind
r = ((P // 17) + 19) % P

# Schwartz-Zippel

# Map string A to polynomial P which has A as its coefficients.
# Evaluate P at point r
def fingerprint(a: str) -> int:
    return sum([r ** i * ord(a[i]) for i in range(len(a))]) % P

class ImplicitPattern():
    def __init__(self, hash: int, length: int):
        self.hash = hash
        self.length = length

    def concat(self, other: 'ImplicitPattern') -> 'ImplicitPattern':
        self.length = (self.length + other.length) % P
        self.hash = (self.hash + other.hash * (r ** self.length)) % P
        return self

class ExplicitPattern():
    def __init__(self, content: str): 
        self.content = content

    def implicit(self) -> ImplicitPattern:
        return ImplicitPattern(
            hash=fingerprint(self.content),
            length=len(self.content)
        )

    def well_formed(self) -> bool:
        # Placeholder
        # Constrain parsing in terms of local conditions on AST
        # Parsing for regex
        return True

class Artefact():
    def __init__(
        self,
        ipat: ImplicitPattern,
        hint: int
    ): 
        self.ipat = ipat
        self.hint = hint

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

    # Note that these are not actually proofs, but rather
    # patterns that are validated for use in instantiations
    # However, we can distinguish between these and proof artefacts
    # by using unique hints
    def proofs(self) -> list[Artefact]:
        # ->->
        assert self.pattern.well_formed()
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
    # a -> (b -> a)
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
    # Premise2: ->ab
    # Conclusion: b

    def __init__(
        self,
        artefact_a: Artefact,
        hint_ab: int,
        ipat_b: ImplicitPattern,
        index: int
    ): 
        self.artefact_a = artefact_a
        self.ipat_b = ipat_b
        self.hint_ab = hint_ab
        self.index = index

    def obligations(self) -> list[Artefact]:
        # Check that hints/timestamps for premises are strictly in the past
        # Necessary to avoid cycles in proofs
        assert self.hint_ab < self.index and self.artefact_a.hint < self.index 

        # Implicit pattern for the implication premise obtained
        # via concatenation
        self.ipat_ab = ExplicitPattern("->").implicit() \
            .concat(self.artefact_a.ipat) \
            .concat(self.ipat_b)
        
        # Artefact for impl. premise assembled with user-given hint
        artefact_ab = Artefact(
            ipat=self.ipat_ab,
            hint=self.hint_ab
        )
        return [
            self.artefact_a,
            artefact_ab
        ]
    
    def proof(self) -> list[Artefact]:
        return [
            Artefact(
                ipat=self.ipat_b,
                hint=self.index
            )
        ]

def check_proof(
        claim: ExplicitPattern,
        # O(|claim|)
        ecoms: list[ExplicitCommitment], 
        # O(|args|)
        proof_steps: list[Prop1 | Prop2 | ModusPonens]
        # O(log N) per step
        # Attempt O(1) computation of r powers from previous powers
        # N = steps
    ) -> bool:

    # Expect the last step of the proof to produce an artefact of the claim
    obligations: set[Artefact] = {Artefact(claim.implicit(), hint=len(proof_steps))}
    proofs: set[Artefact] = set()

    for ecom in ecoms:
        for p in ecom.proofs():
            proofs.add(p)

    for step in proof_steps:
        for o in step.obligations():
            obligations.add(o)
        for p in step.proofs():
            proofs.add(p)

    #assert obligations == proofs
    return (obligations, proofs)

imp_refl_claim = ExplicitPattern("->pp")
ecoms = [
    ExplicitCommitment("p"), 
    ExplicitCommitment("->pp"), 
    ExplicitCommitment("p"),
    ExplicitCommitment("p"),
    ExplicitCommitment("p"),
]

steps = [None] * 6

steps[1] = Prop2(
    ipat_a=ExplicitPattern("p").implicit(), 
    ipat_b=ExplicitPattern("->pp").implicit(), 
    ipat_c=ExplicitPattern("p").implicit(), 
    index=1
)
steps[2] = Prop1(
    ipat_a=ExplicitPattern("p").implicit(), 
    ipat_b=ExplicitPattern("->pp").implicit(), 
    index=2
)
steps[3] = ModusPonens(
    artefact_a=Artefact(
        ipat=ExplicitPattern("->p->->ppp").implicit(),
        hint=2
    ),
    ipat_b=ExplicitPattern("->->p->pp->pp").implicit(),
    hint_ab= 1,
    index= 3
)
steps[4] = Prop1(
    ipat_a=ExplicitPattern("p").implicit(), 
    ipat_b=ExplicitPattern("p").implicit(),
    index=4
)
steps[5] = ModusPonens(
    artefact_a=Artefact(
        ipat=ExplicitPattern("->p->pp").implicit(),
        hint=4
    ),
    ipat_b=ExplicitPattern("->pp"),
    hint_ab=3,
    index=5
)

# Map multiset A to the polynomial P for which A is the exact multiset of roots.
# E.g, map {1, 2, 2} to P = (X - 1)(X - 2)(X - 2)
# Evaluate P at point r.
def fingerprint_mset(s: list[int]) -> int:
    res = 1
    for elem in s:
        res = (res * (r - elem)) % P
    return res