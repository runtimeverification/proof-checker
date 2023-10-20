from __future__ import annotations

from typing import TYPE_CHECKING, TextIO

from proof_generation.io_interpreter import IOInterpreter
from proof_generation.pattern import App, ESubst, Exists, Implies, Mu, SSubst
from proof_generation.proved import Proved

if TYPE_CHECKING:
    from collections.abc import Callable

    from proof_generation.basic_interpreter import ExecutionPhase
    from proof_generation.claim import Claim
    from proof_generation.pattern import EVar, MetaVar, Pattern, SVar


class PrettyPrintingInterpreter(IOInterpreter):
    def __init__(
        self,
        phase: ExecutionPhase,
        out: TextIO,
        claims: list[Claim] | None = None,
        claim_out: TextIO | None = None,
        proof_out: TextIO | None = None,
    ) -> None:
        super().__init__(phase=phase, out=out, claims=claims, claim_out=claim_out, proof_out=proof_out)
        self._notation: dict[str, Pattern] = {}

    def plug_in_notation(self, notation: dict[str, Pattern]) -> None:
        self._notation = notation

    @property
    def notation(self) -> dict[Pattern, str]:
        return {v: k for k, v in self._notation.items()}

    @staticmethod
    def pretty(print_stack: bool = True) -> Callable:
        def decorator(func: Callable) -> Callable:
            def wrapper(*args: Pattern | dict | PrettyPrintingInterpreter, **kwargs: dict) -> Pattern | Proved:
                self, *nargs = args
                assert isinstance(self, PrettyPrintingInterpreter)
                # Find and call the super method.
                result = getattr(super(PrettyPrintingInterpreter, self), func.__name__)(*nargs, **kwargs)
                # Call the pretty printing function.
                func(self, *nargs, **kwargs)
                self.out.write('\n')
                # Print stack
                if print_stack:
                    self.print_stack()
                return result

            return wrapper

        return decorator

    @pretty()
    def evar(self, id: int) -> None:
        self.out.write('EVar ')
        self.out.write(str(id))

    @pretty()
    def svar(self, id: int) -> None:
        self.out.write('SVar ')
        self.out.write(str(id))

    @pretty()
    def symbol(self, id: int) -> None:
        self.out.write('Symbol ')
        self.out.write(str(id))

    @pretty()
    def metavar(
        self,
        id: int,
        e_fresh: tuple[EVar, ...] = (),
        s_fresh: tuple[SVar, ...] = (),
        positive: tuple[SVar, ...] = (),
        negative: tuple[SVar, ...] = (),
        application_context: tuple[EVar, ...] = (),
    ) -> None:
        def write_list(name: str, lst: tuple[EVar, ...] | tuple[SVar, ...]) -> None:
            # Don't print empty arguments
            if len(lst) == 0:
                return
            self.out.write(f'{name}, len={len(lst)} ')
            for item in lst:
                self.out.write(str(item))
                self.out.write(' ')
            self.out.write('\n')

        self.out.write('MetaVar ')
        self.out.write(str(id))
        write_list('eFresh', e_fresh)
        write_list('sFresh', s_fresh)
        write_list('pos', positive)
        write_list('neg', negative)
        write_list('appctx', application_context)

    @pretty()
    def implies(self, left: Pattern, right: Pattern) -> None:
        self.out.write('Implies')

    @pretty()
    def app(self, left: Pattern, right: Pattern) -> None:
        self.out.write('App')

    @pretty()
    def exists(self, var: int, subpattern: Pattern) -> None:
        self.out.write('Exists ')
        self.out.write(str(var))

    @pretty()
    def mu(self, var: int, subpattern: Pattern) -> None:
        self.out.write('Mu ')
        self.out.write(str(var))

    @pretty()
    def esubst(self, evar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> None:
        self.out.write(f'ESubst id={evar_id}')

    @pretty()
    def ssubst(self, svar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> None:
        self.out.write(f'SSubst id={svar_id}')

    @pretty()
    def prop1(self) -> None:
        self.out.write('Prop1')

    @pretty()
    def prop2(self) -> None:
        self.out.write('Prop2')

    @pretty()
    def prop3(self) -> None:
        self.out.write('Prop3')

    @pretty()
    def modus_ponens(self, left: Proved, right: Proved) -> None:
        self.out.write('ModusPonens')

    @pretty()
    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> None:
        self.out.write('Instantiate ')
        self.out.write(', '.join(map(str, delta.keys())))

    @pretty()
    def instantiate_pattern(self, pattern: Pattern, delta: dict[int, Pattern]) -> None:
        self.out.write('Instantiate ')
        self.out.write(', '.join(map(str, delta.keys())))

    @pretty()
    def pop(self, term: Pattern | Proved) -> None:
        self.out.write('Pop')

    @pretty(print_stack=False)
    def save(self, id: str, term: Pattern | Proved) -> None:
        self.out.write('Save')

    @pretty()
    def load(self, id: str, term: Pattern | Proved) -> None:
        self.out.write('Load ')
        self.out.write(id)
        self.out.write('=')
        self.out.write(str(self.memory.index(term)))

    @pretty(print_stack=False)
    def publish_proof(self, proved: Proved) -> None:
        self.out.write('Publish')

    @pretty(print_stack=False)
    def publish_axiom(self, axiom: Pattern) -> None:
        self.out.write('Publish')

    @pretty(print_stack=False)
    def publish_claim(self, pattern: Pattern) -> None:
        self.out.write('Publish')

    def pretty_print_pattern(self, p: Pattern) -> str:
        # TODO: Figure out how to avoid this "double" definition of pretty printing for some cases
        # like implication while keeping notations
        match p:
            case Implies(left, right):
                return f'({self.pretty_print_pattern(left)} -> {self.pretty_print_pattern(right)})'
            case App(left, right):
                return f'(app ({self.pretty_print_pattern(left)}) ({self.pretty_print_pattern(right)}))'
            case Exists(var, subpattern):
                return f'(∃ x{var} . {self.pretty_print_pattern(subpattern)})'
            case Mu(var, subpattern):
                return f'(μ X{var} . {self.pretty_print_pattern(p.subpattern)})'
            case ESubst(pattern, var, plug):
                return f'({self.pretty_print_pattern(pattern)}[{self.pretty_print_pattern(plug)}/{str(var)}])'
            case SSubst(pattern, var, plug):
                return f'({self.pretty_print_pattern(pattern)}[{self.pretty_print_pattern(plug)}/{str(var)}])'

        return str(p)

    def print_stack(self) -> None:
        self.out.write('\tStack:\n')
        for i, item in enumerate(self.stack):
            if isinstance(item, Proved):
                self.out.write(f'\t{i}: ⊢ {self.pretty_print_pattern(item.conclusion)}\n')
                continue
            self.out.write(f'\t{i}: {self.pretty_print_pattern(item)}\n')


class NotationlessPrettyPrinter(PrettyPrintingInterpreter):
    pass
