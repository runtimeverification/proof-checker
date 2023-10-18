from typing import TYPE_CHECKING, IO, Any

from proof_generation.stateful_interpreter import StatefulInterpreter
from proof_generation.basic_interpreter import ExecutionPhase
from proof_generation.claim import Claim


class IOInterpreter(StatefulInterpreter):
    def __init__(
        self,
        phase: ExecutionPhase,
        out: IO[Any],
        claims: list[Claim] | None = None,
        claim_out: IO[Any] | None = None,
        proof_out: IO[Any] | None = None,
    ):
        self.out = gamma_out

    def into_claim_phase(self):
        super().into_claim_phase()
        self.out = self.claim_out

    def into_proof_phase(self):
        super().into_claim_phase()
        self.out = self.proof_out
