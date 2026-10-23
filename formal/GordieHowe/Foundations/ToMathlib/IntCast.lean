-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Int.Cast.Lemmas

@[expose] public section

/-!
# The cast of `Int.toNat`

Candidate for upstreaming next to `ZMod.natCast_toNat`, which is this lemma for `ZMod p`.
-/

namespace Int

/-- The cast of `z.toNat` is the cast of `z` for `0 ≤ z`, in any additive group with one. -/
theorem cast_toNat_of_nonneg {R : Type*} [AddGroupWithOne R] {z : ℤ} (hz : 0 ≤ z) :
    ((z.toNat : ℕ) : R) = (z : R) := by
  calc ((z.toNat : ℕ) : R) = (((z.toNat : ℕ) : ℤ) : R) := (Int.cast_natCast _).symm
    _ = (z : R) := by rw [Int.toNat_of_nonneg hz]

end Int
