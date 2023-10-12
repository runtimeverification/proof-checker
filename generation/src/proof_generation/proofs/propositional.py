from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import TYPE_CHECKING, Optional, Tuple

from proof_generation.pattern import Implication, MetaVar, Notation, Bot, bot
from proof_generation.proof import ProofExp

if TYPE_CHECKING:
    from proof_generation.basic_interpreter import BasicInterpreter
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProvedExpression
    from proof_generation.proved import Proved

phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)
phi0_implies_phi0 = Implication(phi0, phi0)


@dataclass(frozen=True, eq=False)
class Negation(Notation):
    phi0: Pattern

    @staticmethod
    def definition() -> Pattern:
        return Implication(MetaVar(0), bot)

    def __str__(self) -> str:
        return f'~({str(self.phi0)})'


def neg(p: Pattern) -> Pattern:
    return Negation(p)


@dataclass(frozen=True, eq=False)
class Top(Notation):
    @staticmethod
    def definition() -> Pattern:
        return neg(bot)

    def __str__(self) -> str:
        return '\u22A4'


top = Top()


@dataclass(frozen=True, eq=False)
class Or(Notation):
    left: Pattern
    right: Pattern

    @staticmethod
    def definition() -> Pattern:
        return Implication(neg(MetaVar(0)), MetaVar(1))

    def __str__(self) -> str:
        return f'({str(self.left)}) \/ ({str(self.right)})'

def ml_or(l: Pattern, r: Pattern) -> Pattern:
    return Or(l, r)


def unwrap(x, error_msg):
    assert x, error_msg
    return x


def is_imp(pat: Pattern) -> Optional[Tuple[Pattern, Pattern]]:
    if isinstance(pat, Implication):
        return pat.left, pat.right
    return None

def get_imp(pat: Pattern) -> Tuple[Pattern, Pattern]:
    return unwrap(is_imp(pat), "Expected an implication but got: " + str(pat) + "\n")

def is_bot(pat: Pattern) -> bool:
    if pat == bot.conclusion():
        return True
    if isinstance(pat, Bot):
        return True
    if isinstance(pat, Notation):
        return is_bot(pat.conclusion())
    return False

def get_bot(pat: Pattern):
    assert is_bot(pat), "Expected Bot but instead got: " + str(pat) + "\n"

def is_neg(pat: Pattern) -> Optional[Pattern]:
    if is_imp(pat) and is_bot(pat.right):
        return pat.left
    if isinstance(pat, Negation):
        return pat.phi0
    if isinstance(pat, Notation):
        return is_neg(pat.conclusion())
    return None

def get_neg(pat: Pattern) -> Pattern:
    return unwrap(is_neg(pat), "Expected a negation but got: " + str(pat) + "\n")

def is_top(pat: Pattern) -> bool:
    if is_imp(pat):
        return is_bot(pat.left) and is_bot(pat.right)
    if isinstance(pat, Top):
        return True
    if isinstance(pat, Notation):
        return is_top(pat.conclusion())
    return False

def get_top(pat: Pattern):
    assert is_top(pat), "Expected Top but instead got: " + str(pat) + "\n"

def is_or(pat: Pattern) -> Optional[Tuple[Pattern, Pattern]]:
    if is_imp(pat):
        if l := is_neg(pat.left):
            return l, pat.right
        return None
    if isinstance(pat, Or):
        return pat.left, pat.right
    if isinstance(pat, Notation):
        return is_or(pat.conclusion())
    return None

def get_or(pat: Pattern) -> Tuple[Pattern, Pattern]:
    return unwrap(is_or(pat), "Expected an Or but got: " + str(pat) + "\n")

class Propositional(ProofExp):
    def __init__(self, interpreter: BasicInterpreter) -> None:
        super().__init__(interpreter)

    @staticmethod
    def axioms() -> list[Pattern]:
        return []

    @staticmethod
    def claims() -> list[Pattern]:
        phi0 = MetaVar(0)
        return [
            Implication(phi0, phi0),  # Reflexivity
            top,  # Top
            Implication(bot, phi0),  # Bot_elim
            Implication(neg(neg(phi0)), phi0),  # Contradiction
            Implication(neg(phi0), Implication(phi0, phi1)),  # Absurd
            Implication(Implication(neg(phi0), phi0), phi0),  # Peirce_bot
        ]

    def proof_expressions(self) -> list[ProvedExpression]:
        return [
            self.imp_refl,
            self.top_intro,
            self.bot_elim,
            self.contradiction_proof,
            self.absurd,
            self.peirce_bot,
        ]

    # Proofs
    # ======

    # phi0 -> phi0
    def imp_refl(self, p: Pattern = MetaVar(0)) -> Proved:
        # fmt: off
        return self.dynamic_inst(
            self.modus_ponens(
                self.modus_ponens(
                    self.dynamic_inst(self.prop2, {1: phi0_implies_phi0, 2: phi0}),
                    self.dynamic_inst(self.prop1, {1: phi0_implies_phi0})
                ),
                self.dynamic_inst(self.prop1, {1: phi0}),
            ),
            {0: p})

    # phi1 -> phi2 and phi2 -> phi3 yields also a proof of phi1 -> phi3
    def imp_transitivity(self, phi0_imp_phi1: Proved, phi1_imp_phi2: Proved) -> Proved:
        # TODO: Consider if the extra loads caused by these calls are problematic
        a, b = get_imp(phi0_imp_phi1.conclusion)
        b2, c = get_imp(phi1_imp_phi2.conclusion)
        assert b == b2

        return self.modus_ponens(
            # (a -> b) -> (a -> c)
            self.modus_ponens(
                # (a -> (b -> c)) -> ((a -> b) -> (a -> c))
                self.dynamic_inst(self.prop2, {0: a, 1: b, 2: c}),
                #  a -> (b -> c)
                self.modus_ponens(
                    # (b -> c) -> (a -> (b -> c))
                    self.dynamic_inst(self.prop1, {0: phi1_imp_phi2.conclusion, 1: a}),
                    phi1_imp_phi2,
                ),
            ),
            phi0_imp_phi1,
        )

    # top
    def top_intro(self) -> Proved:
        return self.imp_refl(bot)

    # bot -> p
    def bot_elim(self, p: Pattern = MetaVar(0)) -> Proved:
        neg_neg_p = neg(neg(p))

        return self.modus_ponens(
            # ((bot -> neg neg p) -> (bot -> p)))
            self.modus_ponens(
                # (bot -> (neg neg p -> p)) -> ((bot -> neg neg p) -> (bot -> p))
                self.dynamic_inst(self.prop2, {0: bot, 1: neg_neg_p, 2: p}),
                # (bot -> (neg neg p -> p))
                self.modus_ponens(
                    # (neg neg p -> p) -> (bot -> (neg neg p -> p))
                    self.dynamic_inst(self.prop1, {0: Implication(neg_neg_p, p), 1: bot}),
                    # (neg neg p -> p)
                    self.dynamic_inst(self.prop3, {0: p}),
                ),
            ),
            # (bot -> (neg neg p))
            self.dynamic_inst(self.prop1, {0: bot, 1: neg(p)}),
        )

    # (neg phi0 -> bot) -> phi0
    def contradiction_proof(self) -> Proved:
        return self.prop3()

    # (neg a) -> a -> b
    def absurd(self, a: Pattern = MetaVar(0), b: Pattern = MetaVar(1)) -> Proved:
        bot_to_b = Implication(bot, b)

        return self.modus_ponens(
            self.dynamic_inst(self.prop2, {0: a, 1: bot, 2: b}),
            # a -> bot -> b
            self.modus_ponens(
                self.dynamic_inst(self.prop1, {0: bot_to_b, 1: a}),
                self.bot_elim(b)
            ),
        )

    # (((ph0 -> bot) -> ph0) -> ph0)
    def peirce_bot(self) -> Proved:
        def phi0_bot_imp_ph0() -> Pattern:
            # ((ph0 -> bot) -> ph0)
            return Implication(Implication(phi0, bot), phi0)

        def phi0_bot_imp_bot() -> Pattern:
            # (ph0 -> bot) -> bot)
            return Implication(Implication(phi0, bot), bot)

        def phi0_bot_imp_phi0_bot() -> Pattern:
            # (phi0 -> bot) -> (phi0->bot)
            return Implication(Implication(phi0, bot), Implication(phi0, bot))

        def modus_ponens_1() -> Proved:
            return self.modus_ponens(
                self.dynamic_inst(
                    self.prop2,
                    {
                        # ((ph0 -> bot) -> ph0) = neg 0 -> 0
                        0: phi0_bot_imp_ph0(),
                        # ((ph0 -> bot) -> bot) = neg 0 -> bot
                        1: phi0_bot_imp_bot(),
                        2: phi0,
                    },
                ),
                self.modus_ponens(
                    self.dynamic_inst(
                        self.prop1,
                        {
                            # (((ph0 -> bot) -> bot) -> ph0)
                            0: Implication(phi0_bot_imp_bot(), phi0),
                            # ((ph0 -> bot) -> ph0)
                            1: phi0_bot_imp_ph0(),
                        },
                    ),
                    # ph0
                    self.dynamic_inst(self.prop3, {0: phi0}),
                ),
            )

        def modus_ponens_2() -> Proved:
            return self.modus_ponens(
                self.dynamic_inst(
                    self.prop2,
                    {
                        0: phi0_bot_imp_ph0(),
                        1: phi0_bot_imp_phi0_bot(),
                        # (((ph0 -> bot) -> phi0) -> ((ph0 -> bot) -> bot)))
                        2: Implication(phi0_bot_imp_ph0(), phi0_bot_imp_bot()),
                    },
                ),
                self.modus_ponens(
                    self.dynamic_inst(
                        self.prop1,
                        {
                            # ((phi0 -> bot) -> (phi0 -> bot)) -> (((ph0 -> bot) -> phi0) -> ((ph0 -> bot) -> bot))),
                            0: Implication(
                                Implication(
                                    Implication(phi0, bot),
                                    Implication(phi0, bot),
                                ),
                                Implication(
                                    phi0_bot_imp_ph0(),
                                    phi0_bot_imp_bot(),
                                ),
                            ),
                            1: phi0_bot_imp_ph0(),
                        },
                    ),
                    self.dynamic_inst(
                        self.prop2,
                        {
                            0: Implication(phi0, bot),
                            1: phi0,
                            2: bot,
                        },
                    ),
                ),
            )

        def modus_ponens_3() -> Proved:
            return self.modus_ponens(
                # ((phi0 -> bot) -> (phi0 -> bot)) -> (((phi0 -> bot) -> phi0) -> ((phi0 -> bot) -> (phi0->bot)))
                self.dynamic_inst(
                    self.prop1,
                    {
                        0: phi0_bot_imp_phi0_bot(),
                        1: phi0_bot_imp_ph0(),
                    },
                ),
                # ((phi0 -> bot) -> phi0) -> ((phi0 -> bot) -> phi0)
                self.imp_refl(
                    Implication(phi0, bot)
                ),
            )

        return self.modus_ponens(
            modus_ponens_1(),
            self.modus_ponens(
                self.modus_ponens(
                    self.dynamic_inst(
                        self.prop2,
                        {
                            0: phi0_bot_imp_ph0(),
                            1: phi0_bot_imp_ph0(),
                            2: phi0_bot_imp_bot(),
                        },
                    ),
                    self.modus_ponens(
                        modus_ponens_2(),
                        modus_ponens_3(),
                    ),
                ),
                self.imp_refl(phi0_bot_imp_ph0()),
            ),
        )


if __name__ == '__main__':
    Propositional.main(sys.argv)
