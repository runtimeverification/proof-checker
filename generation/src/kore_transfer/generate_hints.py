from __future__ import annotations

from typing import TYPE_CHECKING

import pyk.kore.syntax as kore
from pyk.kore.parser import KoreParser
from pyk.ktool.krun import KRunOutput, _krun

if TYPE_CHECKING:
    from collections.abc import Iterator
    from pathlib import Path

    import proof_generation.pattern as nf
    from kore_transfer.generate_definition import KoreDefinition
    from kore_transfer.kore_converter import KoreConverter
    from rewrite.llvm_proof_hint import LLVMRewriteTrace


class KoreHint:
    def __init__(self, pattern: nf.Pattern, axiom: nf.Pattern, instantiations: tuple[nf.Pattern, ...]) -> None:
        # TODO: Change interface according to the real hint format
        self._pattern: nf.Pattern = pattern
        self._axiom: nf.Pattern = axiom
        self._instantiations: tuple[nf.Pattern, ...] = instantiations

    @property
    def pattern(self) -> nf.Pattern:
        return self._pattern

    @property
    def relevant_axiom(self) -> nf.Pattern:
        """Return the relevant axiom for the given hint."""
        return self._axiom

    @property
    def instantiations(self) -> dict[int, nf.Pattern]:
        return dict(enumerate(self._instantiations))


def get_proof_hints(
    kompiled_dir: Path,
    program_file: Path,
    definition: type[KoreDefinition],
    kore_converter: KoreConverter,
    max_step: int,
) -> Iterator[KoreHint]:
    """This function should return proof hints."""
    for step in range(max_step + 1):
        configuration_for_step: kore.Pattern = _get_confguration_for_depth(kompiled_dir, program_file, step)
        # TODO: Absolutely hardcoded solution until we have hints
        assert (
            isinstance(configuration_for_step, kore.App)
            and isinstance(configuration_for_step.args[0], kore.App)
            and isinstance(configuration_for_step.args[0].args[0], kore.App)
        )

        pattern = kore_converter.convert_pattern(configuration_for_step)
        inst1 = kore_converter.convert_pattern(configuration_for_step.args[0].args[0].args[1])
        inst2 = kore_converter.convert_pattern(configuration_for_step.args[1])

        hint = KoreHint(pattern, definition.axioms()[0], (inst1, inst2))
        yield hint


def _get_confguration_for_depth(definition_dir: Path, input_file: Path, depth: int) -> kore.Pattern:
    """Generate the configuration for the given depth."""
    # TODO: This can be also done using KAST and then using the KRun class but it soesn't seem easier to me
    finished_process = _krun(input_file=input_file, definition_dir=definition_dir, output=KRunOutput.KORE, depth=depth)
    # TODO: We can consider implementing a better error handling
    assert finished_process.returncode == 0, 'KRun failed'

    parsed = KoreParser(finished_process.stdout)
    return parsed.pattern()


def get_proof_hints_from_rewrite_trace(
    llvm_proof_hint: LLVMRewriteTrace,
    axioms: list[kore.Axiom],
    kore_converter: KoreConverter,
    max_step: int,
) -> Iterator[KoreHint]:
    """Emits proof hints corresponding to the given LLVM rewrite trace."""
    assert max_step <= len(
        llvm_proof_hint.trace
    ), f'The requested number of rewrites {max_step} exceeds the length of the given trace {len(llvm_proof_hint.trace)}!'

    pre_config = kore_converter.convert_pattern(llvm_proof_hint.initial_config)

    # TODO: Handle the no-rewrites case, which requires changing the KoreHints representation
    if max_step <= 0:
        pass
        # yield KoreHint(pre_config, None, None)
    else:
        # Note that here len(llvm_proof_hint.trace) > 0
        post_config = pre_config
        for step in range(max_step):
            rewrite_step = llvm_proof_hint.trace[step]
            pre_config = post_config
            axiom = kore_converter.convert_axiom(axioms[rewrite_step.rule_ordinal])
            subst = kore_converter.convert_substitution(rewrite_step.substitution)
            hint = KoreHint(pre_config, axiom, subst)
            post_config = kore_converter.convert_pattern(rewrite_step.post_config)
            yield hint
