from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

from proof_generation.basic_interpreter import ExecutionPhase
from proof_generation.claim import Claim
from proof_generation.counting_interpreter import CountingInterpreter
from proof_generation.pattern import ESubst, EVar, Exists, Implies, PrettyOptions, bot, phi0, phi1, phi2
from proof_generation.pretty_printing_interpreter import PrettyPrintingInterpreter
from proof_generation.proved import Proved
from proof_generation.serializing_interpreter import MemoizingInterpreter, SerializingInterpreter

if TYPE_CHECKING:
    from collections.abc import Callable

    from proof_generation.basic_interpreter import BasicInterpreter
    from proof_generation.pattern import Notation, Pattern

# Proof Expressions
# =================


class ProofThunk:
    _expr: Callable[[BasicInterpreter], Proved]
    conc: Pattern

    def __init__(self, expr: Callable[[BasicInterpreter], Proved], conc: Pattern):
        self._expr = expr
        self.conc = conc

    def __call__(self, interpreter: BasicInterpreter) -> Proved:
        proved = self._expr(interpreter)
        # TODO Check is this call to equality is causing performance issues
        assert proved.conclusion == self.conc
        return proved


class ProofExp:
    _axioms: list[Pattern]
    _notations: list[Notation]
    _claims: list[Pattern]
    _proof_expressions: list[ProofThunk]

    def __init__(
        self,
        axioms: list[Pattern] | None = None,
        notations: list[Notation] | None = None,
        claims: list[Pattern] | None = None,
        proof_expressions: list[ProofThunk] | None = None,
    ) -> None:
        self._axioms = [] if axioms is None else axioms
        self._notations = [] if notations is None else notations
        self._claims = [] if claims is None else claims
        self._proof_expressions = [] if proof_expressions is None else proof_expressions

    def add_axiom(self, axiom: Pattern) -> None:
        self._axioms.append(axiom)

    def add_assumption(self, axiom: Pattern) -> None:
        self.add_axiom(axiom)

    def add_axioms(self, axioms: list[Pattern]) -> None:
        self._axioms.extend(axioms)

    def add_assumptions(self, axioms: list[Pattern]) -> None:
        self.add_axioms(axioms)

    def get_axioms(self) -> list[Pattern]:
        return self._axioms

    def add_notation(self, notation: Notation) -> None:
        self._notations.append(notation)

    def add_notations(self, notations: list[Notation]) -> None:
        self._notations.extend(notations)

    def get_notations(self) -> list[Notation]:
        return self._notations

    def add_claim(self, claim: Pattern) -> None:
        self._claims.append(claim)

    def add_claims(self, claims: list[Pattern]) -> None:
        self._claims.extend(claims)

    def get_claims(self) -> list[Pattern]:
        return self._claims

    def add_proof_expression(self, proof_expression: ProofThunk) -> None:
        self._proof_expressions.append(proof_expression)

    def add_proof_expressions(self, proof_expressions: list[ProofThunk]) -> None:
        self._proof_expressions.extend(proof_expressions)

    def get_proof_expressions(self) -> list[ProofThunk]:
        return self._proof_expressions

    # Proof Rules
    # -----------

    def dynamic_inst(self, pf: ProofThunk, delta: dict[int, Pattern]) -> ProofThunk:
        if not delta:
            return pf

        def proved_exp(interpreter: BasicInterpreter) -> Proved:
            for idn, p in delta.items():
                delta[idn] = interpreter.pattern(p)
            return interpreter.instantiate(pf(interpreter), delta)

        return ProofThunk(proved_exp, pf.conc.instantiate(delta))

    def prop1(self) -> ProofThunk:
        return ProofThunk((lambda interpreter: interpreter.prop1()), Implies(phi0, Implies(phi1, phi0)))

    def prop2(self) -> ProofThunk:
        return ProofThunk(
            (lambda interpreter: interpreter.prop2()),
            Implies(Implies(phi0, Implies(phi1, phi2)), Implies(Implies(phi0, phi1), Implies(phi0, phi2))),
        )

    def prop3(self) -> ProofThunk:
        return ProofThunk(
            (lambda interpreter: interpreter.prop3()), Implies(Implies(Implies(phi0, bot()), bot()), phi0)
        )

    def modus_ponens(self, left: ProofThunk, right: ProofThunk) -> ProofThunk:
        p, q = Implies.extract(left.conc)
        assert p == right.conc
        return ProofThunk((lambda interpreter: interpreter.modus_ponens(left(interpreter), right(interpreter))), q)

    def exists_quantifier(self) -> ProofThunk:
        x = EVar(0)
        y = EVar(1)
        return ProofThunk(
            (lambda interpreter: interpreter.exists_quantifier()), Implies(ESubst(phi0, x, y), Exists(x.name, phi0))
        )

    def exists_generalization(self, proved: ProofThunk, var: EVar) -> ProofThunk:
        l, r = Implies.extract(proved.conc)
        return ProofThunk(
            (lambda interpreter: interpreter.exists_generalization(proved(interpreter), var)),
            Implies(Exists(var.name, l), r),
        )

    def instantiate(self, proved: ProofThunk, delta: dict[int, Pattern]) -> ProofThunk:
        return ProofThunk(
            (lambda interpreter: interpreter.instantiate(proved(interpreter), delta)), proved.conc.instantiate(delta)
        )

    def load_axiom(self, axiom_term: Pattern) -> ProofThunk:
        assert axiom_term in self._axioms
        axiom = Proved(axiom_term)

        def proved_exp(interpreter: BasicInterpreter) -> Proved:
            interpreter.load(f'Axiom {str(axiom)}', axiom)
            return axiom

        return ProofThunk(proved_exp, axiom_term)

    def load_axiom_by_index(self, i: int) -> ProofThunk:
        return self.load_axiom(self._axioms[i])

    def publish_proof(self, proved: ProofThunk) -> ProofThunk:
        def proved_exp(interpreter: BasicInterpreter) -> Proved:
            interpreter.publish_proof(proved(interpreter))
            return Proved(proved.conc)

        return ProofThunk(proved_exp, proved.conc)

    def execute_gamma_phase(self, interpreter: BasicInterpreter, move_into_claim: bool = True) -> None:
        assert interpreter.phase == ExecutionPhase.Gamma
        for axiom in self._axioms:
            interpreter.publish_axiom(interpreter.pattern(axiom))
        self.check_interpreting(interpreter)
        if move_into_claim:
            interpreter.into_claim_phase()

    def execute_claims_phase(self, interpreter: BasicInterpreter, move_into_proof: bool = True) -> None:
        assert interpreter.phase == ExecutionPhase.Claim
        for claim in reversed(self._claims):
            interpreter.publish_claim(interpreter.pattern(claim))
        self.check_interpreting(interpreter)
        if move_into_proof:
            interpreter.into_proof_phase()

    def execute_proofs_phase(self, interpreter: BasicInterpreter) -> None:
        assert interpreter.phase == ExecutionPhase.Proof
        for proof_expr in self._proof_expressions:
            self.publish_proof(proof_expr)(interpreter)
        self.check_interpreting(interpreter)

    def execute_full(self, interpreter: BasicInterpreter) -> None:
        assert interpreter.phase == ExecutionPhase.Gamma
        self.execute_gamma_phase(interpreter)
        self.execute_claims_phase(interpreter)
        self.execute_proofs_phase(interpreter)

    def serialize(self, file_path: Path) -> None:
        self.execute_full(
            SerializingInterpreter(
                ExecutionPhase.Gamma,
                claims=[Claim(claim) for claim in self._claims],
                out=open(file_path.with_suffix('.ml-gamma'), 'wb'),
                claim_out=open(file_path.with_suffix('.ml-claim'), 'wb'),
                proof_out=open(file_path.with_suffix('.ml-proof'), 'wb'),
            )
        )

    def check_interpreting(self, interpreter: BasicInterpreter) -> None:
        if not interpreter.safe_interpreting:
            print(f'Proof generation during {interpreter.phase.name} phase is potentially unsafe!')
            for warning in interpreter.interpreting_warnings:
                print(warning)

    def pretty_options(self) -> PrettyOptions:
        return PrettyOptions(notations={n.definition: n for n in self._notations})

    def prettyprint(self, file_path: Path) -> None:
        self.execute_full(
            PrettyPrintingInterpreter(
                ExecutionPhase.Gamma,
                claims=[Claim(claim) for claim in self._claims],
                out=open(file_path.with_suffix('.pretty-gamma'), 'w'),
                claim_out=open(file_path.with_suffix('.pretty-claim'), 'w'),
                proof_out=open(file_path.with_suffix('.pretty-proof'), 'w'),
                pretty_options=self.pretty_options(),
            )
        )

    def memoize(self, file_path: Path) -> None:
        counting_interpreter = CountingInterpreter(
            ExecutionPhase.Gamma,
            claims=[Claim(claim) for claim in self._claims],
        )

        self.execute_full(counting_interpreter)

        self.execute_full(
            MemoizingInterpreter(
                ExecutionPhase.Gamma,
                claims=[Claim(claim) for claim in self._claims],
                patterns_for_memoization=counting_interpreter.finalize(),
                out=open(file_path.with_suffix('.ml-gamma'), 'wb'),
                claim_out=open(file_path.with_suffix('.ml-claim'), 'wb'),
                proof_out=open(file_path.with_suffix('.ml-proof'), 'wb'),
            )
        )

    def main(self, argv: list[str]) -> None:
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
                self.prettyprint(output_dir / slice_name)
            case 'binary':
                self.serialize(output_dir / slice_name)
            case 'memo':
                self.memoize(output_dir / slice_name)
