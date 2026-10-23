-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.Gadgets.Shake256
public import GordieHowe.ProofSystem.RingSwitching.PackedClaim

@[expose] public section

/-!
# The hook of a batched permutation (`KeccakBatch::start`)

A hooked permutation of a Keccak batch (`lib/circuits/keccak/keccak_batch.h` at `e5daf0a`,
lines 120-130 and 184-190) commits its start state as 100 words, and the circuit asserts that
start word `(x, y, c)` is `Σ_j β_j · A[x][y][16c + j]` for the circuit-computed input state `A`
(`packed`, lines 327-333). `packLane` is the packing of one lane chunk.
-/

namespace GordieHowe.KeccakHook

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.PackedClaim

variable {K : Type*} [Field K] [DecidableEq K]

/-- Lane bit `16c + j`, bit `j` of packed word `c`. -/
def laneBit (c : Fin 4) (j : Fin (2 ^ 4)) : Fin 64 :=
  ⟨16 * c + j, by have := c.isLt; have : (j : ℕ) < 16 := j.isLt; omega⟩

/-- Packed word `c` of a lane (`packed`):
`Σ_j β_j · v[16c + j]`. -/
def packLane (B : PackedBasis K 4) (v : BitWires K 64) (c : Fin 4) : K :=
  ∑ j : Fin (2 ^ 4), B.β j * v (laneBit c j)

/-- On a Boolean lane, the packed word is `pack` of its bits. -/
theorem packLane_eq_pack (B : PackedBasis K 4) {v : BitWires K 64} (hv : AllBool v)
    (c : Fin 4) : packLane B v c = pack B fun j => decide (v (laneBit c j) = 1) := by
  unfold packLane pack
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases hv (laneBit c j) with h | h <;> simp [h]

/-- **Decoding a packed lane word returns the lane's bits.** -/
theorem decode_packLane [CharP K 2] (B : PackedBasis K 4) {v : BitWires K 64}
    (hv : AllBool v) (c : Fin 4) (j : Fin (2 ^ 4)) :
    decode B (packLane B v c) j = v (laneBit c j) := by
  rw [packLane_eq_pack B hv, decode_pack]
  rcases hv (laneBit c j) with h | h <;> simp [h]

end GordieHowe.KeccakHook
