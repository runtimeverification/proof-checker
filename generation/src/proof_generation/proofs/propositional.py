from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.proof import Implication, MetaVar, Mu, ProofExp, SVar

if TYPE_CHECKING:
    from proof_generation.proof import BasicInterpreter, Pattern, PatternExpression, Proved, ProvedExpression


class Propositional(ProofExp):
    def __init__(self, interpreter: BasicInterpreter) -> None:
        super().__init__(interpreter)

    @staticmethod
    def claims() -> list[Pattern]:
        phi0 = MetaVar(0)
        bot = Mu(SVar(0), SVar(0))
        top = Implication(bot, bot)
        return [Implication(phi0, phi0), top, Implication(bot, phi0)]

    def claim_expressions(self) -> list[PatternExpression]:
        return [self.phi0_implies_phi0, self.top, self.bot_implies_phi0]

    def proof_expressions(self) -> list[ProvedExpression]:
        return [self.imp_reflexivity, self.top_intro, self.bot_elim]

    # Notation
    # ========

    def phi0(self) -> Pattern:
        if ret := self.load_notation('phi0'):
            return ret
        return self.save_notation('phi0', self.metavar(0))

    def phi0_implies_phi0(self) -> Pattern:
        if ret := self.load_notation('phi0-implies-phi0'):
            return ret
        return self.save_notation('phi0-implies-phi0', self.implies(self.phi0(), self.phi0()))

    def bot(self) -> Pattern:
        if ret := self.load_notation('bot'):
            return ret
        return self.save_notation('bot', self.mu(0, self.svar(0)))

    def neg_notation(self) -> Pattern:
        if ret := self.load_notation('neg'):
            return ret
        return self.save_notation('neg', self.implies(self.phi0(), self.bot()))

    def neg(self, p: PatternExpression) -> Pattern:
        return self.instantiate_notation(self.neg_notation(), (0,), (p(),))

    def top(self) -> Pattern:
        if ret := self.load_notation('top'):
            return ret
        return self.save_notation('top', self.neg(self.bot))

    def bot_implies_phi0(self) -> Pattern:
        if ret := self.load_notation('bot-implies-phi0'):
            return ret
        return self.save_notation('bot-implies-phi0', self.implies(self.phi0(), self.bot()))

    # Proofs
    # ======

    # phi0 -> phi0
    def imp_reflexivity(self) -> Proved:
        # fmt: off
        return self.modus_ponens(
            self.modus_ponens(
                self.prop2().instantiate((1, 2,), (self.phi0_implies_phi0(), self.phi0()),),
                self.prop1().instantiate((1,), (self.phi0_implies_phi0(),)),
            ),
            self.prop1().instantiate((1,), (self.phi0(),)),
        )

    # phi1 -> phi2 and phi2 -> phi3 yields also a proof of phi1 -> phi3
    def imp_transitivity(self, phi0_imp_phi0: Proved, phi1_imp_phi2: Proved) -> Proved:
        phi0_imp_phi1_conc = phi0_imp_phi0.conclusion

        match phi0_imp_phi1_conc:
            case Implication(phi0, phi1):
                pass
            case _:
                raise AssertionError('Expected implication')
        phi1_imp_phi2_conc = phi1_imp_phi2.conclusion
        match phi1_imp_phi2_conc:
            case Implication(phi1_r, phi2):
                assert phi1_r == phi1
            case _:
                raise AssertionError('Expected implication')

        return self.modus_ponens(
            self.modus_ponens(
                self.prop2().instantiate((1, 2, 0), (phi1, phi2, self.metavar(1))),
                self.modus_ponens(self.prop1().instantiate((0,), (phi1_imp_phi2_conc,)), phi1_imp_phi2),
            ).instantiate((1,), (phi0,)),
            phi0_imp_phi0,
        )

    def top_intro(self) -> Proved:
        return self.imp_reflexivity().instantiate((0,), (self.bot(),))

    def bot_elim(self) -> Proved:
        return self.modus_ponens(
            # ((bot -> neg neg 0) -> (bot -> 0)))
            self.modus_ponens(
                # (bot -> (neg neg 0 -> 0)) -> ((bot -> neg neg 0) -> (bot -> 0))
                self.prop2().instantiate((0, 1, 2), (self.bot(), self.neg(lambda: self.neg(self.phi0)), self.phi0())),
                # (bot -> (neg neg 0 -> 0))
                self.modus_ponens(
                    # (neg neg 0 -> 0) -> (bot -> (neg neg 0 -> 0))
                    self.prop1().instantiate((0, 1), (self.implies(
                                self.neg(lambda: self.neg(self.phi0)), self.phi0()
                            ), self.bot()
                        )),
                    # (neg neg 0 -> 0)
                    self.prop3().instantiate((0,), (self.phi0(),)),
                ),
            ),
            # (bot -> (neg neg phi0))
            self.prop1().instantiate((0, 1), (self.bot(), self.neg(self.phi0))),
        )


if __name__ == '__main__':
    Propositional.main(sys.argv)
