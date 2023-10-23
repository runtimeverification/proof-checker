from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

from proof_generation.basic_interpreter import ExecutionPhase
from proof_generation.claim import Claim
from proof_generation.counting_interpreter import CountingInterpreter
from proof_generation.pattern import Pattern
from proof_generation.pretty_printing_interpreter import PrettyPrintingInterpreter
from proof_generation.proved import Proved
from proof_generation.serializing_interpreter import MemoizingInterpreter, SerializingInterpreter

if TYPE_CHECKING:
    from proof_generation.basic_interpreter import BasicInterpreter
    from proof_generation.pattern import EVar, SVar

# Proof Expressions
# =================

PatternExpression = Callable[[], Pattern]
ProvedExpression = Callable[[], Proved]


class ProofExp:
    interpreter: BasicInterpreter

    def __init__(self, interpreter: BasicInterpreter) -> None:
        self.interpreter = interpreter
        self.notation: dict[str, Pattern] = {}

    @staticmethod
    def axioms() -> list[Pattern]:
        raise NotImplementedError

    @staticmethod
    def claims() -> list[Pattern]:
        raise NotImplementedError

    def proof_expressions(self) -> list[ProvedExpression]:
        raise NotImplementedError

    # Patterns
    # ========

    def svar(self, id: int) -> Pattern:
        return self.interpreter.svar(id)

    def evar(self, id: int) -> Pattern:
        return self.interpreter.evar(id)

    def symbol(self, id: int) -> Pattern:
        return self.interpreter.symbol(id)

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        return self.interpreter.implies(left, right)

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        return self.interpreter.app(left, right)

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        return self.interpreter.exists(var, subpattern)

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        return self.interpreter.mu(var, subpattern)

    def metavar(
        self,
        name: int,
        e_fresh: tuple[EVar, ...] = (),
        s_fresh: tuple[SVar, ...] = (),
        positive: tuple[SVar, ...] = (),
        negative: tuple[SVar, ...] = (),
        application_context: tuple[EVar, ...] = (),
    ) -> Pattern:
        return self.interpreter.metavar(name, e_fresh, s_fresh, positive, negative, application_context)

    # Proof Rules
    # -----------

    def prop1(self) -> Proved:
        return self.interpreter.prop1()

    def prop2(self) -> Proved:
        return self.interpreter.prop2()

    def prop3(self) -> Proved:
        return self.interpreter.prop3()

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        return self.interpreter.modus_ponens(left, right)

    def dynamic_inst(self, proved_expr: ProvedExpression, delta: dict[int, Pattern]) -> Proved:
        if not delta:
            return proved_expr()
        for idn, p in delta.items():
            delta[idn] = self.interpreter.pattern(p)
        return self.interpreter.instantiate(proved_expr(), delta)

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        return self.interpreter.instantiate(proved, delta)

    def instantiate_pattern(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        return self.interpreter.instantiate_pattern(pattern, delta)

    def load_axiom(self, axiom_term: Pattern) -> Proved:
        assert axiom_term in self.axioms()
        axiom = Proved(axiom_term)
        self.interpreter.load(f'Axiom {str(axiom)}', axiom)
        return axiom

    def save_pattern(self, id: str, pattern: Pattern) -> Pattern:
        self.interpreter.save(id, pattern)
        return pattern

    def publish_axiom(self, proved: Pattern) -> Pattern:
        self.interpreter.publish_axiom(proved)
        return proved

    def publish_proof(self, proved: Proved) -> Proved:
        self.interpreter.publish_proof(proved)
        return proved

    def publish_claim(self, pattern: Pattern) -> Pattern:
        self.interpreter.publish_claim(pattern)
        return pattern

    def execute_gamma_phase(self) -> None:
        assert self.interpreter.phase == ExecutionPhase.Gamma
        for axiom in self.axioms():
            self.publish_axiom(self.interpreter.pattern(axiom))
        self.interpreter.into_claim_phase()

    def execute_claims_phase(self) -> None:
        assert self.interpreter.phase == ExecutionPhase.Claim
        for claim in reversed(self.claims()):
            self.publish_claim(self.interpreter.pattern(claim))
        self.interpreter.into_proof_phase()

    def execute_proofs_phase(self) -> None:
        assert self.interpreter.phase == ExecutionPhase.Proof
        for proof_expr in self.proof_expressions():
            self.publish_proof(proof_expr())

    def execute_full(self) -> None:
        assert self.interpreter.phase == ExecutionPhase.Gamma
        self.execute_gamma_phase()
        self.execute_claims_phase()
        self.execute_proofs_phase()

    @classmethod
    def serialize(cls, file_names: list[str]) -> None:
        prover = cls(
            interpreter=SerializingInterpreter(
                phase=ExecutionPhase.Gamma, out=open(file_names[0], 'wb'), claims=list(map(Claim, cls.claims()))
            )
        )

        assert isinstance(prover.interpreter, SerializingInterpreter)

        prover.execute_gamma_phase()
        # Execute gamma phase and change output file
        prover.interpreter.out.close()
        prover.interpreter.out = open(file_names[1], 'wb')

        # Execute claim phase and change output file
        prover.execute_claims_phase()
        prover.interpreter.out.close()
        prover.interpreter.out = open(file_names[2], 'wb')

        # Execute proof phase
        prover.execute_proofs_phase()
        prover.interpreter.out.close()

    @classmethod
    def prettyprint(cls, file_names: list[str]) -> None:
        prover = cls(
            PrettyPrintingInterpreter(
                phase=ExecutionPhase.Gamma, out=open(file_names[0], 'w'), claims=list(map(Claim, cls.claims()))
            )
        )

        assert isinstance(prover.interpreter, PrettyPrintingInterpreter)

        prover.execute_gamma_phase()
        # Execute gamma phase and change output file
        prover.interpreter.out.close()
        prover.interpreter.out = open(file_names[1], 'w')

        # Execute claim phase and change output file
        prover.execute_claims_phase()
        prover.interpreter.out.close()
        prover.interpreter.out = open(file_names[2], 'w')

        # Execute proof phase
        prover.execute_proofs_phase()
        prover.interpreter.out.close()

    @classmethod
    def memoize(cls, file_names: list[str]) -> None:
        counter = cls(
            CountingInterpreter(
                phase=ExecutionPhase.Gamma,
                claims=list(map(Claim, cls.claims())),
            )
        )

        assert isinstance(counter.interpreter, CountingInterpreter)
        counter.execute_full()

        memoizer = cls(
            MemoizingInterpreter(
                phase=ExecutionPhase.Gamma,
                claims=list(map(Claim, cls.claims())),
                out=open(file_names[0], 'wb'),
                patterns_for_memoization=counter.interpreter.finalize(),
            )
        )

        assert isinstance(memoizer.interpreter, MemoizingInterpreter)

        memoizer.execute_gamma_phase()
        memoizer.interpreter.out.close()
        memoizer.interpreter.out = open(file_names[1], 'wb')

        memoizer.execute_claims_phase()
        memoizer.interpreter.out.close()
        memoizer.interpreter.out = open(file_names[2], 'wb')

        memoizer.execute_proofs_phase()
        memoizer.interpreter.out.close()

    @classmethod
    def main(cls, argv: list[str]) -> None:
        exe, *argv = argv
        usage = f'Usage:\n\n python3 {exe} (binary|pretty) (claim|proof) output-file\n python3 {exe} --help\n\n'
        examples = (
            f'Examples:\n\npython3 {exe} binary claim a.out\n# outputs claims of ProofExp object in verifier-checkable binary format to file a.out\n\n'
            + f'python3 {exe} pretty claim /dev/stdout\n# outputs claims of ProofExp object in human-readable format to standard output\n'
        )

        if len(argv) == 1:
            assert argv[0] == '--help', usage
            print(usage + examples)
            return

        assert len(argv) == 3, usage
        format, mode, output_path = argv

        file_names = ['/dev/null', '/dev/null', '/dev/null']

        match mode:
            case 'gamma':
                file_names[0] = output_path
            case 'claim':
                file_names[1] = output_path
            case 'proof':
                file_names[2] = output_path

        match format:
            case 'pretty':
                cls.prettyprint(file_names)
            case 'binary':
                cls.serialize(file_names)
            case 'memo':
                cls.memoize(file_names)
