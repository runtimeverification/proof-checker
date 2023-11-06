from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable
from pathlib import Path
from typing import TYPE_CHECKING

from proof_generation.basic_interpreter import ExecutionPhase
from proof_generation.claim import Claim
from proof_generation.counting_interpreter import CountingInterpreter
from proof_generation.pattern import ESubst, EVar, Exists, Implies, Pattern, bot, phi0, phi1, phi2
from proof_generation.pretty_printing_interpreter import PrettyPrintingInterpreter
from proof_generation.proved import Proved
from proof_generation.serializing_interpreter import MemoizingInterpreter, SerializingInterpreter

if TYPE_CHECKING:
    from proof_generation.basic_interpreter import BasicInterpreter
    from proof_generation.pattern import SVar

# Proof Expressions
# =================

PatternExpression = Callable[[], Pattern]
ProvedExpression = Callable[[], Proved]


class ProofThunk:
    _expr: ProvedExpression
    conc: Pattern

    def __init__(self, expr: ProvedExpression, conc: Pattern):
        self._expr = expr
        self.conc = conc

    def __call__(self) -> Proved:
        proved = self._expr()
        # TODO Check is this call to equality is causing performance issues
        assert proved.conclusion == self.conc
        return proved


class ProofExp(ABC):
    interpreter: BasicInterpreter

    def __init__(self, interpreter: BasicInterpreter) -> None:
        self.interpreter = interpreter

    @classmethod
    @abstractmethod
    def axioms(cls) -> list[Pattern]:
        raise NotImplementedError

    @classmethod
    @abstractmethod
    def claims(cls) -> list[Pattern]:
        raise NotImplementedError

    def proof_expressions(self) -> list[ProofThunk]:
        raise NotImplementedError

    # Patterns
    # ========

    def svar(self, id: int) -> Pattern:
        return self.interpreter.svar(id)

    def evar(self, id: int) -> Pattern:
        return self.interpreter.evar(id)

    def symbol(self, name: str) -> Pattern:
        return self.interpreter.symbol(name)

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

    def dynamic_inst(self, pf: ProofThunk, delta: dict[int, Pattern]) -> ProofThunk:
        if not delta:
            return pf

        def proved_exp() -> Proved:
            for idn, p in delta.items():
                delta[idn] = self.interpreter.pattern(p)
            return self.interpreter.instantiate(pf(), delta)

        return ProofThunk(proved_exp, pf.conc.instantiate(delta))

    def prop1(self) -> ProofThunk:
        return ProofThunk(self.interpreter.prop1, Implies(phi0, Implies(phi1, phi0)))

    def prop2(self) -> ProofThunk:
        return ProofThunk(
            self.interpreter.prop2,
            Implies(Implies(phi0, Implies(phi1, phi2)), Implies(Implies(phi0, phi1), Implies(phi0, phi2))),
        )

    def prop3(self) -> ProofThunk:
        return ProofThunk(self.interpreter.prop3, Implies(Implies(Implies(phi0, bot), bot), phi0))

    def modus_ponens(self, left: ProofThunk, right: ProofThunk) -> ProofThunk:
        p, q = Implies.extract(left.conc)
        assert p == right.conc
        return ProofThunk((lambda: self.interpreter.modus_ponens(left(), right())), q)

    def exists_quantifier(self) -> ProofThunk:
        x = EVar(0)
        y = EVar(1)
        return ProofThunk(self.interpreter.exists_quantifier, Implies(ESubst(phi0, x, y), Exists(x.name, phi0)))

    def exists_generalization(self, proved: ProofThunk, var: EVar) -> ProofThunk:
        l, r = Implies.extract(proved.conc)
        return ProofThunk(
            (lambda: self.interpreter.exists_generalization(proved(), var)), Implies(Exists(var.name, l), r)
        )

    def instantiate(self, proved: ProofThunk, delta: dict[int, Pattern]) -> ProofThunk:
        return ProofThunk((lambda: self.interpreter.instantiate(proved(), delta)), proved.conc.instantiate(delta))

    def instantiate_pattern(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        return self.interpreter.instantiate_pattern(pattern, delta)

    def load_axiom(self, axiom_term: Pattern) -> ProofThunk:
        assert axiom_term in self.axioms()
        axiom = Proved(axiom_term)

        def proved_exp() -> Proved:
            self.interpreter.load(f'Axiom {str(axiom)}', axiom)
            return axiom

        return ProofThunk(proved_exp, axiom_term)
    
    def load_axiom_by_index(self, i: int) -> ProofThunk:
        return self.load_axiom(self.axioms()[i])

    def save_pattern(self, id: str, pattern: Pattern) -> Pattern:
        self.interpreter.save(id, pattern)
        return pattern

    def publish_axiom(self, proved: Pattern) -> Pattern:
        self.interpreter.publish_axiom(proved)
        return proved

    def publish_proof(self, proved: ProofThunk) -> ProofThunk:
        def proved_exp() -> Proved:
            self.interpreter.publish_proof(proved())
            return Proved(proved.conc)

        return ProofThunk(proved_exp, proved.conc)

    def publish_claim(self, pattern: Pattern) -> Pattern:
        self.interpreter.publish_claim(pattern)
        return pattern

    def execute_gamma_phase(self) -> None:
        assert self.interpreter.phase == ExecutionPhase.Gamma
        for axiom in self.axioms():
            self.publish_axiom(self.interpreter.pattern(axiom))
        self.check_interpreting()
        self.interpreter.into_claim_phase()

    def execute_claims_phase(self) -> None:
        assert self.interpreter.phase == ExecutionPhase.Claim
        for claim in reversed(self.claims()):
            self.publish_claim(self.interpreter.pattern(claim))
        self.check_interpreting()
        self.interpreter.into_proof_phase()

    def execute_proofs_phase(self) -> None:
        assert self.interpreter.phase == ExecutionPhase.Proof
        for proof_expr in self.proof_expressions():
            self.publish_proof(proof_expr)()
        self.check_interpreting()

    def execute_full(self) -> None:
        assert self.interpreter.phase == ExecutionPhase.Gamma
        self.execute_gamma_phase()
        self.execute_claims_phase()
        self.execute_proofs_phase()

    @classmethod
    def serialize(cls, file_path: Path) -> None:
        prover = cls(
            interpreter=SerializingInterpreter(
                ExecutionPhase.Gamma,
                claims=list(map(Claim, cls.claims())),
                out=open(file_path.with_suffix('.ml-gamma'), 'wb'),
                claim_out=open(file_path.with_suffix('.ml-claim'), 'wb'),
                proof_out=open(file_path.with_suffix('.ml-proof'), 'wb'),
            )
        )
        prover.execute_full()

    def check_interpreting(self) -> None:
        if not self.interpreter.safe_interpreting:
            print(f'Proof generation during {self.interpreter.phase.name} phase is potentially unsafe!')
            for warning in self.interpreter.interpreting_warnings:
                print(warning)

    @classmethod
    def prettyprint(cls, file_path: Path) -> None:
        prover = cls(
            PrettyPrintingInterpreter(
                ExecutionPhase.Gamma,
                claims=list(map(Claim, cls.claims())),
                out=open(file_path.with_suffix('.pretty-gamma'), 'w'),
                claim_out=open(file_path.with_suffix('.pretty-claim'), 'w'),
                proof_out=open(file_path.with_suffix('.pretty-proof'), 'w'),
            )
        )
        prover.execute_full()

    @classmethod
    def memoize(cls, file_path: Path) -> None:
        counter = cls(
            CountingInterpreter(
                ExecutionPhase.Gamma,
                claims=list(map(Claim, cls.claims())),
            )
        )

        assert isinstance(counter.interpreter, CountingInterpreter)
        counter.execute_full()

        memoizer = cls(
            MemoizingInterpreter(
                ExecutionPhase.Gamma,
                claims=list(map(Claim, cls.claims())),
                patterns_for_memoization=counter.interpreter.finalize(),
                out=open(file_path.with_suffix('.ml-gamma'), 'wb'),
                claim_out=open(file_path.with_suffix('.ml-claim'), 'wb'),
                proof_out=open(file_path.with_suffix('.ml-proof'), 'wb'),
            )
        )
        memoizer.execute_full()

    @classmethod
    def main(cls, argv: list[str]) -> None:
        exe, *argv = argv
        usage = f'Usage:\n\n python3 {exe} (binary|pretty|memo) output-folder slice-name\n python3 {exe} --help\n\n'
        examples = f'Examples:\n\npython3 {exe} binary pi2 propositional\n# outputs the given ProofExp in verifier-checkable binary format to pi2/propositional.ml-(gamma|claim|proof)\n\n'

        if len(argv) == 1:
            assert argv[0] == '--help', usage
            print(usage + examples)
            return

        assert len(argv) == 3, usage
        output_format, output_path, slice_name = argv

        output_dir = Path(output_path)
        if not output_dir.exists():
            print('Creating output directory...')
            output_dir.mkdir()

        match output_format:
            case 'pretty':
                cls.prettyprint(output_dir / slice_name)
            case 'binary':
                cls.serialize(output_dir / slice_name)
            case 'memo':
                cls.memoize(output_dir / slice_name)
