Proof hint

:   A proof hint is an informal artifact produced during the run of an instrumented algorithm.
    For example, the LLVM backend produces a stream of rewrites applied and simplifications made.
    The resolution decision procedure for propositional formulae produces binary DAG over propositions.


Kore Language Specification

:   Kore is a language at an abstraction somewhere between the high-level K format and applicative matching logic. 
    It is at slightly higher level than many-sorted polyadic matching logic.
    Since Kore was developed before the semantics of K in matching logic was completely fleshed out
    there are some outdated concepts and unsoundness
    (in particular with reference to injections).
    As such, we use this as a guideline to produce a formal AML theory rather than an absolute source of truth.

DSL Theory

:   These are pythonic incarnations of AML theories, and enumerate notations and axioms used.

DSL Langauge Specification

:   A DSL language specification is a DSL Theory aimed at formalizing a K lanuage.
    It is generated using a Kore Language specification as a guide.
    This specification needs to patch any unsoundness in the Kore Language Specification,
    and represents a formal, sound, AML theory for the language.

DSL Proof Expression

:   Within the context of a DSL Theory, matching logic claims and proofs are
    expressed in a DSL. This DSL gives us human accessible
    interface for writing claims and proofs with respect to a Theory.
    Currently this DSL is fairly low level, but we will build tools and libraries
    to make it easier and higher level to use.

    This DSL will be used to implement translations of proof hints for various algorithms
    into formal matching logic proofs.

DSL Interpreters

:   Since these proofs may grow pretty unboundedly large,
    one of the goals of the DSL Proof Expressions is to allow
    representing them without holding its entirety in memory.

    We do this by making the DSL a "shallow embedding"
    of matching logic patterns and proofs---we never build
    an explicit representation of proofs for example as an python ADT/dataclass.
    Instead matching logic constructs such as its syntax and proof rules
    correspond to python functions that may be interpreted in various contexts.

    One obvious way to interpret a proof is to verify that it is correct.
    Another, is to pretty print it, or to render it as LaTeX.
    Still another is the optimize it by sharing sub-proofs as lemmas,
    or removing redundant instantiations.

Binary AML Proof

:   To represent the proof of a claim in AML, we need four components

    1.  An `ml-theory` file encodes a list of axiom patterns represented in an efficient binary language.
    2.  An `ml-claims` file encodes a list of claim patterns represented in the same language.
    3.  An `ml-proof` file encodes proofs of the claims in an `ml-claims` file assuming the axioms in an `ml-theory`
    4.  An `ml-metadata` file encodes the information needed for pretty printing axioms, claims, and proofs defined in the above binary format.
        This includes the names for symbols, axioms, and theorems, as well as mixfix representations for notations etc.
        This is an vital and important part of an AML proof. Otherwise we would not be able to read the axioms in a Theory,
        or the claims that are proved. And how can we trust something we cannot read?

    Eventually, through the use of notation, our goal is to be able to reconstruct
    a human readable language specification from the `ml-theory` and the `ml-metadata`.
    It will likely be at the same level of abstraction as the current Kore specification,
    though, hopefully more user-friendly.

Proof Aggregation

:   The binary proof format is not intended to be massively parallizable.
    We instead expect the proofs to be broken up into multiple
    sub-proofs of reasonably sized subproofs each with its own theory, claims and proofs.

    For example, we expect a proof of program execution to be broken up at least into the following components:

    *   Generic Matching Logic Lemmas including propositional logic lemmas, frame-reasoning, and fixpoint related lemmas.
    *   Generic K related lemmas including term algebras, maps, ints, sorts etc.
    *   Language specific lemmas: shortcuts for easy application of rules summarizing a single rule exection into a lemma.
    *   Program specific lemmas: Through the use of the KSummarizer, we may replace execution of multiple consecutive rules, e.g. for the body of a for loop into a single lemma.
    *   For long executions we may a single execution trace into sub-executions with perhaps a few though thousand execution steps in each subproof.

    To aggregate these subproofs together we may allow the following operation:

    >   If the union of the `ml-theory` and `ml-claims` of one proof are the subset of the `ml-theory` of another
    >   then we assume the existance of a proof with the `ml-theory` of the first, and the `ml-claims` as the union of their `ml-claims`.
    >   The resulting aggregated proof will have an `ml-theory` and `ml-claims` component, but no `ml-proof` component, and instead refer to the subproofs.

    Since membership checking and unions are fairly cheap operations over Merkle trees I think this should be a relatively cheap operation in ZK.



Why do we need a separate Binary langauge vs a pythonic DSL?

:   The Binary format and the DSL have opposing goals---the
    DSL aims to be a high-level language for easy human readability
    and a library for proof *generation*.
    On the other hand, the binary language aims to be a
    low-level machine interpretable language with a clear mathematical semantics.
    This allows it to be easily verified by the proof checker.

    Further, the DSL is just one way to generate AML proofs.
    There are other projects that will implement other ideologies, such as the AML in Coq project.
    Forcing these to generate a complex human python based DSL is wasted time.


DSL Language Specification
==========================


```
class RewriteTheory:
    # Builder
    # =======

    def module(name: str) -> RewriteModule:
        ...

    class RewriteModule:
        # Builder
        # =======

        def import(name: str) -> RewriteModule: ...
        def sort(name: str) -> KSort: ...
        def hooked_sort(name: str) -> KSort: ...
        def constructor(name: str, ...) -> KSymbol: ...
        def cell(name: str, ...) -> KSymbol: ...
        def function(name: str, ...) -> KSymbol: ...
        def subsort(KSort, KSort) -> Ordinal: ...
        def equational_rewrite(requires, lhs, ensures, rhs) -> Ordinal: ...
        def rewrite_rule(requires, lhs, ensures, rhs) -> Ordinal: ...

        # Accessors
        # =========

        def get_sort(str) -> KSort:

    # Accessors
    # =========

    def get_rule_by_ordinal(int: ordinal) -> RewriteRule | EquationalRule:
        ...

    def get_modules() -> list[RewriteModule]
    def get_axioms() -> list[Pattern]:


class SingleRewriteTheory(RewriteTheory):
    """ This pseudocode is a manual translation of the "SingleRewrite"
        K Definition.
    """

    def definition(self):
        with self.module('BASIC-K') as mod:
            # Adds the symbols for `inhabitants_K`, `inhabitants_KItem`
            mod.sort('K')
            mod.sort('KItem')

        with self.module('KSEQ') as mod:
            basic_k = mod.import('BASIC-K')
            sort_k = basic_k.get_sort('K')
            sort_kitem = basic_k.get_sort('KItem')

            # Check for `constructor` attribute
            kseq = mod.constructor('kseq',
                                input=(sort_kitem, sort_k)
                                output=sort_k
                           )
            dotk = mod.constructor('dotk', input=(), output=sort_k)

            # Check for `functional` attribute, but no `constructor` attribute.
            append = mod.function('append',
                            input=(sort_k, sort_k)
                            output=sort_k
                        )

            # Axiom without other attributes?
            # Ask K team to add an attribute to identify these.
            mod.equational_rewrite( append(kseq(KVar('K'), KVar('KS')), KVar('X1'))
                                  , kseq(KVar('K'), append(KVar('KS')), KVar('X1'))
                                  )

        with self.module('INJ') as mod:
            # `symbol inj` is a special case.
            # We ignore the symbol declaration and the simplification axiom
            # over `inj` as well.

        with self.module('K') as mod:
            mod.import('KSEQ')
            mod.import('INJ')

        with self.module('SINGLE-REWRITE') as mod:
            mod.import('K')
            sort_top_cell = mod.sort('SortTopCell')
            sort_counter_cell = mod.sort('SortCounterCell')
            sort_foo = mod.sort('Foo')

            sort_int = mod.hooked_sort('Int')

            sort_k = mod.get_sort('K')

            # Check for `cell`, `cellName` attribute
            counter_cell mod.cell('generatedCounter', input=(sort_int,), output=sort_counter_cell)
            top_cell = mod.cell('generatedTop', input=(sort_top_cell, sort_counter_cell), output=sort_counter_cell)
            k_cell = mod.cell('k', input=(sort_k,), output=sort_k_cell)

            fooa = mod.constructor('FooA', input=(), output=sort_foo)
            foob = mod.constructor('FooB', input=(), output=sort_foo)

            # Check for `subsort` attribute
            mod.subsort(sort_k_cell, sort_k_item)
            mod.subsort(sort_foo, sort_k_item)
            mod.subsort(sort_top_cell, sort_k_item)
            mod.subsort(sort_int, sort_k_item)

            # All *axioms* with `functional`, `constructor`, `assoc`, `unit`, `idem` attributes can be ignored.
            # They are covered by the corresponding attribute of symbol declarations.

            # Check for `\rewrites` at root of pattern
            # TODO: Ask K Team to add an attribute.
            mod.rewrite_rule( mod.constrained_term(top_cell(k_cell(kseq(fooa()))))
                              mod.constrained_term(top_cell(k_cell(kseq(foob()))))
                            )


class ExecutionProofGenerator:
    def __init__(self, theory: RewriteTheory, init_config: Pattern):
       self.init_config = initial_config
       self.curr_config = initial_config
       """ Invariant: Holds a proof for `init_config =>* curr_config` """
       self.proof : ProofExpression = ...


    def rewrite_event(rule_ordinal: int, substitution):
        """ Extends the proof with an additional rewrite step """
        ...

    class SimplificationContext:
        generator: ExecutionProofGenerator

        def enter_subcontext(position: list[int]) -> SimplificationContext:
            ...

        def apply_funtional_simplification(...):
            """ Apply a functional simplification to the term at the position of this context. """
            ...

        def apply_builtin_simplification(...):
            """ Apply a builtin simplification to the term at the position of this context.
                Record axioms needed.
            """
            ...


    def enter_context(position: list[int]) -> SimplificationContext:
        ...


    def finalize(...) -> ProofExp:
        """ Returns a proof expression for the claim `
            whose axioms include all assumptions needed,
        """


    @staticmethod
    def from_llvm_proof_hint(...) -


```

