-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.Round

@[expose] public section

/-!
# The `[0, 1, 2]` GKR interpolation nodes over an odd-characteristic field

The prime-field C++ backends initialize `poly_evaluation_point(i) = of_scalar(i)`
(`lib/algebra/fp14.h:92-93`, `lib/algebra/fp24.h:87`, `lib/algebra/fp_goldilocks.h:186-188`), so the
three interpolation nodes are `0, 1, 2`. They are distinct in any field of characteristic `p > 2`:
`2 ≠ 0` since `p ∤ 2`, and `2 ≠ 1` since `1 ≠ 0`.
-/

namespace GordieHowe.Sumcheck.Round
open IOP

variable {F : Type} [Field F]

theorem two_ne_zero_of_charP (p : ℕ) [CharP F p] (hp : 2 < p) : (2 : F) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h2
  exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)

/-- `2 ≠ 1` in every field. -/
theorem field_two_ne_one : (2 : F) ≠ 1 := fun h =>
  one_ne_zero (α := F) (by linear_combination h)

/-- The nodes `[0, 1, 2]` in a field of characteristic `p > 2`. -/
def _root_.GordieHowe.Sumcheck.Nodes.zeroOneTwo (p : ℕ) [CharP F p] (hp : 2 < p) : Nodes F where
  point := fun i => ![(0 : F), 1, 2] i
  injective := by
    have h20 : (2 : F) ≠ 0 := two_ne_zero_of_charP p hp
    have h21 : (2 : F) ≠ 1 := field_two_ne_one
    intro i j hij
    have h02 : (0 : F) ≠ 2 := Ne.symm h20
    have h12 : (1 : F) ≠ 2 := Ne.symm h21
    fin_cases i <;> fin_cases j <;> simp_all
  zero := by simp
  one := by simp

@[simp] theorem _root_.GordieHowe.Sumcheck.Nodes.zeroOneTwo_point (p : ℕ) [CharP F p] (hp : 2 < p) (i : Fin 3) :
    (Nodes.zeroOneTwo (F := F) p hp).point i = ![(0 : F), 1, 2] i := rfl

end GordieHowe.Sumcheck.Round
