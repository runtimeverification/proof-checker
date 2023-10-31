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

DSL Theory / `ProofExpr`

:   These are pythonic incarnations of AML theories, and include notations and axioms.
    Within the context of a Theory, we generate matching logic proofs of claims
    using the (pythonic incarnation of) AML's proof system, called a ProofExpr. 

    These Theories and `ProofExpr`s may be deserialized into concrete AML proofs in the form of our binary proof language.

DSL Langauge Specification

:   A DSL language specification is a DSL Theory aimed at formalizing a K lanuage.
    It is generated using a Kore Language specification as a guide.
    This specification needs to patch any unsoundness in the Kore Language Specification,
    and represent a formal, sound, AML theory for a language.


Binary AML

:   To represent the proof of a claim in AML, we need four components

    1.  An `ml-theory` file encodes a list of axiom patterns represented in an efficient binary language.
    2.  An `ml-claims` file encodes a list of claim patterns represented in the same language.
    3.  An `ml-proof` file encodes proofs of the claims in an `ml-claims` file assuming the axioms in an `ml-theory`
    4.  An `ml-metadata` file encodes the information needed for pretty printing axioms, claims, and proofs defined in the above binary format.
        This includes the names for symbols, axioms, and theorems, as well as mixfix representations for notations etc.
        This is an vital and important part of an AML proof. Otherwise we would not be able to read the axioms in a Theory,
        or the claims that are proved. And how can we trust something we cannot read? 


Questions to answer


* Why do we need a separate Binary langauge vs a pythonic DSL
