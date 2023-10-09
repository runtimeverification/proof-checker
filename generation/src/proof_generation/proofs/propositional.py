from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import TYPE_CHECKING

from proof_generation.pattern import Implication, MetaVar, Notation, bot
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
            self.imp_reflexivity,
            self.top_intro,
            self.bot_elim,
            self.contradiction_proof,
            self.absurd,
            self.peirce_bot,
        ]

    # Proofs
    # ======

    # phi0 -> phi0
    def imp_reflexivity(self) -> Proved:
        # fmt: off
        return self.modus_ponens(
            self.modus_ponens(
                self.dynamic_inst(self.prop2, {1: phi0_implies_phi0, 2: phi0}),
                self.dynamic_inst(self.prop1, {1: phi0_implies_phi0})
            ),
            self.dynamic_inst(self.prop1, {1: phi0}),
        )

    # phi1 -> phi2 and phi2 -> phi3 yields also a proof of phi1 -> phi3
    def imp_transitivity(self, phi0_imp_phi1: ProvedExpression, phi1_imp_phi2: ProvedExpression) -> Proved:
        # TODO: Consider if the extra loads caused by these calls are problematic
        phi0_imp_phi1_conc = phi0_imp_phi1().conclusion

        match phi0_imp_phi1_conc:
            case Implication(phi0, phi1):
                pass
            case _:
                raise AssertionError('Expected implication')
        phi1_imp_phi2_conc = phi1_imp_phi2().conclusion
        match phi1_imp_phi2_conc:
            case Implication(phi1_r, phi2):
                assert phi1_r == phi1
            case _:
                raise AssertionError('Expected implication')

        return self.modus_ponens(
            # (phi0 -> phi1) -> (phi0 -> phi2)
            self.dynamic_inst(
                lambda: self.modus_ponens(
                    # (1 -> (phi1 -> phi2)) -> ((1 -> phi1) -> (1 -> phi2))
                    self.dynamic_inst(self.prop2, {0: MetaVar(1), 1: phi1, 2: phi2}),
                    #  1 -> (phi1 -> phi2)
                    self.modus_ponens(
                        # (phi1 -> phi2) -> (1 -> (phi1 -> phi2))
                        self.dynamic_inst(self.prop1, {0: phi1_imp_phi2_conc}),
                        phi1_imp_phi2(),
                    ),
                ),
                {1: phi0},
            ),
            phi0_imp_phi1(),
        )

    def top_intro(self) -> Proved:
        return self.dynamic_inst(self.imp_reflexivity, {0: bot})

    def bot_elim(self) -> Proved:
        neg_neg_phi0 = neg(neg(phi0))

        return self.modus_ponens(
            # ((bot -> neg neg 0) -> (bot -> 0)))
            self.modus_ponens(
                # (bot -> (neg neg 0 -> 0)) -> ((bot -> neg neg 0) -> (bot -> 0))
                self.dynamic_inst(self.prop2, {0: bot, 1: neg_neg_phi0, 2: phi0}),
                # (bot -> (neg neg 0 -> 0))
                self.modus_ponens(
                    # (neg neg 0 -> 0) -> (bot -> (neg neg 0 -> 0))
                    self.dynamic_inst(self.prop1, {0: Implication(neg_neg_phi0, phi0), 1: bot}),
                    # (neg neg 0 -> 0)
                    self.dynamic_inst(self.prop3, {0: phi0}),
                ),
            ),
            # (bot -> (neg neg phi0))
            self.dynamic_inst(self.prop1, {0: bot, 1: neg(phi0)}),
        )

    # (neg phi0 -> bot) -> phi0
    def contradiction_proof(self) -> Proved:
        return self.dynamic_inst(self.prop3, {0: phi0})

    # (neg phi0) -> phi0 -> phi1
    def absurd(self) -> Proved:
        bot_to_1 = Implication(bot, phi1)

        return self.modus_ponens(
            self.dynamic_inst(self.prop2, {0: phi0, 1: bot, 2: phi1}),
            self.modus_ponens(
                self.dynamic_inst(self.prop1, {0: bot_to_1, 1: phi0}), self.dynamic_inst(self.bot_elim, {0: phi1})
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
                self.dynamic_inst(
                    self.imp_reflexivity,
                    {
                        # (phi0 -> bot)
                        0: Implication(phi0, bot),
                    },
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
                self.dynamic_inst(self.imp_reflexivity, {0: phi0_bot_imp_ph0()}),
            ),
        )


if __name__ == '__main__':
    Propositional.main(sys.argv)
