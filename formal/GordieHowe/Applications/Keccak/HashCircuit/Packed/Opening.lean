-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.PackedClaim
public import GordieHowe.ProofSystem.Zerocheck.UnivariateSkip
public import GordieHowe.Foundations.ToMathlib.PiSingle
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

@[expose] public section

/-!
# The terminal claims of the batched-Keccak alternative as a linear form

The batched-Keccak alternative authenticates the skip's `u`-batched terminal operand claim through
the packed Keccak state words. This file states the operand arrays of a vector indexed by operand,
group and point (`toOperands`). The Keccak operand map that the terminal is read through is
`KeccakOperands.keccakOperands`.

Source: `lib/sumcheck/keccak_skip_link.h` and `masked_boolean_skip.h` on `main` at `f4e27b3c`.
`BooleanSkip = BasicBooleanSkip<GF2_256<>>` (`boolean_skip.h` line 550), and `finish_rows`
(`masked_boolean_skip.h` lines 186-206) builds the opening row
`∑_j u_j · (terminal_j + pad_j) = constant + ∑_k (frob(M_k + public_k, k) + power(k))`, whose left
side is the batched terminal of the operand arrays plus the pads.
-/

namespace GordieHowe.HashCircuit.Packed.Opening
open IOP

open PackedClaim Sumcheck.UnivariateSkip

variable {K : Type} [Field K] {a M : ℕ} {ι : Type} [Fintype ι]

variable [CharP K 2]

variable {w n : ℕ}

/-- The operand arrays of a vector indexed by operand, group and point. -/
def toOperands (v : Fin 3 → Fin (2 ^ n) → Fin w → K) : Operands K w n := ⟨v 0, v 1, v 2⟩

end GordieHowe.HashCircuit.Packed.Opening
