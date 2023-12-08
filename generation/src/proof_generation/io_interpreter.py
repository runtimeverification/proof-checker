from __future__ import annotations

from typing import IO, TYPE_CHECKING, Any

from proof_generation.stateful_interpreter import StatefulInterpreter

if TYPE_CHECKING:
    from proof_generation.claim import Claim
    from proof_generation.interpreter import ExecutionPhase


class IOInterpreter(StatefulInterpreter):
    def __init__(
        self,
        phase: ExecutionPhase,
        out: IO[Any],
        claims: list[Claim] | None = None,
        claim_out: IO[Any] | None = None,
        proof_out: IO[Any] | None = None,
    ) -> None:
        super().__init__(phase, claims)
        self.out = out
        self.claim_out = claim_out
        self.proof_out = proof_out

    def into_claim_phase(self) -> None:
        assert self.claim_out
        super().into_claim_phase()
        self.out.close()
        self.out = self.claim_out

    def into_proof_phase(self) -> None:
        assert self.proof_out
        super().into_proof_phase()
        self.out.close()
        self.out = self.proof_out

    def __del__(self) -> None:
        self.out.close()
