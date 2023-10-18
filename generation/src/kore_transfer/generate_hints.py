from __future__ import annotations

from itertools import count
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


class KoreHint:
    def __init__(self, pattern: nf.Pattern, axiom: nf.Pattern | None, instantiations: tuple[nf.Pattern, ...]) -> None:
        # TODO: Change interface according to the real hint format
        self._pattern: nf.Pattern = pattern
        self._axiom: nf.Pattern | None = axiom
        self._instantiations: tuple[nf.Pattern, ...] = instantiations

    @property
    def pattern(self) -> nf.Pattern:
        return self._pattern

    @property
    def relevant_axiom(self) -> nf.Pattern | None:
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
    """This function should return proof hinst."""
    if max_step > 0:
        counter = iter(range(max_step + 1))
    else:
        # Unbounded iteration
        counter = count(0)

    last_axiom: kore.Pattern | None = None
    for step in counter:
        configuration_for_step: kore.Pattern = _get_confguration_for_depth(kompiled_dir, program_file, step)
        if last_axiom and configuration_for_step == last_axiom:
            break
        else:
            last_axiom = configuration_for_step

        # TODO: Absolutely hardcoded solution until we have hints
        assert (
            isinstance(configuration_for_step, kore.App)
            and isinstance(configuration_for_step.args[0], kore.App)
            and isinstance(configuration_for_step.args[0].args[0], kore.App)
        )

        pattern = kore_converter.convert_pattern(configuration_for_step)
        inst1 = kore_converter.convert_pattern(configuration_for_step.args[0].args[0].args[1])
        inst2 = kore_converter.convert_pattern(configuration_for_step.args[1])

        # TODO: The choice for an axiom is hardcoded and should be changed!
        axiom = _choose_axiom(step, definition)
        hint = KoreHint(pattern, axiom, (inst1, inst2))
        yield hint


def _get_confguration_for_depth(definition_dir: Path, input_file: Path, depth: int) -> kore.Pattern:
    """Generate the configuration for the given depth."""
    # TODO: This can be also done using KAST and then using the KRun class but it soesn't seem easier to me
    finished_process = _krun(input_file=input_file, definition_dir=definition_dir, output=KRunOutput.KORE, depth=depth)
    # TODO: We can consider implementing a better error handling
    assert finished_process.returncode == 0, 'KRun failed'

    parsed = KoreParser(finished_process.stdout)
    return parsed.pattern()


def _choose_axiom(step: int, definition: type[KoreDefinition]) -> nf.Pattern | None:
    if step < len(definition.axioms()):
        return definition.axioms()[step]
    else:
        return None
