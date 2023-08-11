from proof_generation.format import MLPrinter
from proof_generation.proof import EVar, Exists, MetaVar, Mu, SVar, bot, implies, neg
from proof_generation.proofs.propositional import Propositional

if __name__ == '__main__':
    mlp = MLPrinter()

    mlp.pprint(bot)

    not_phi0 = neg(MetaVar(0))
    mlp.pprint(not_phi0)

    some_diverse_pattern = Mu(SVar(0), Exists(EVar(0), implies(MetaVar(25, e_fresh=(EVar(5),)), bot)))
    mlp.pprint(some_diverse_pattern)

    mlp.pprint(Propositional().imp_reflexivity())

    mlpds = MLPrinter(desugar_axioms=True)
    mlpds.pprint(Propositional().imp_reflexivity())
