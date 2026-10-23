-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

@[expose] public section

/-!
# Affine random batching with an arbitrary fixed offset

A violated residual vector cannot be hidden by adding a fixed committed mask value: the verifier's
uniformly random linear combination vanishes for at most a `1 / |F|` fraction of challenge vectors.
No honesty or zero value of the offset is assumed.
-/

namespace GordieHowe.AffineBatching

open MvPolynomial

variable {F : Type} [Field F] {n : ℕ}

/-- The scalar tested by affine batching. -/
def value (offset : F) (residual challenge : Fin n → F) : F :=
  offset + ∑ i, challenge i * residual i

/-- Polynomial in the verifier's independent batching coefficients. -/
noncomputable def polynomial (offset : F) (residual : Fin n → F) : MvPolynomial (Fin n) F :=
  C offset + ∑ i, C (residual i) * X i

@[simp] theorem eval_polynomial (offset : F) (residual challenge : Fin n → F) :
    eval challenge (polynomial offset residual) = value offset residual challenge := by
  simp [polynomial, value, mul_comm]

theorem polynomial_degree (offset : F) (residual : Fin n → F) :
    (polynomial offset residual).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le (by simp)
  apply totalDegree_finsetSum_le
  intro i _
  simpa using totalDegree_mul (C (residual i) : MvPolynomial (Fin n) F) (X i)

/-- A nonzero residual makes the batching polynomial nonzero for every offset. -/
theorem polynomial_ne_zero (offset : F) {residual : Fin n → F}
    (hne : ∃ i, residual i ≠ 0) : polynomial offset residual ≠ 0 := by
  classical
  intro hp
  obtain ⟨i, hi⟩ := hne
  have h0 := congrArg (eval (0 : Fin n → F)) hp
  have h1 := congrArg (eval (Pi.single i 1)) hp
  have hoffset : offset = 0 := by simpa [polynomial] using h0
  simp [value, Pi.single_apply, hoffset] at h1
  exact hi h1

/-- Counting form of the `1 / |F|` batching error, including zero-dimensional
challenge vectors (whose nonzero-residual hypothesis is impossible). -/
theorem card_zeros_mul_card_le [Fintype F] [DecidableEq F] (offset : F)
    {residual : Fin n → F} (hne : ∃ i, residual i ≠ 0) :
    (Finset.univ.filter fun challenge => value offset residual challenge = 0).card *
      Fintype.card F ≤ Fintype.card F ^ n := by
  have hcard : 0 < Fintype.card F := Fintype.card_pos
  have hF : (0 : ℚ≥0) < (Fintype.card F : ℚ≥0) := by exact_mod_cast hcard
  have h := schwartz_zippel_totalDegree (polynomial_ne_zero offset hne)
    (Finset.univ : Finset F)
  rw [Fintype.piFinset_univ, Finset.card_univ] at h
  rw [div_le_div_iff₀ (by positivity) hF] at h
  have hnat :
      (Finset.univ.filter fun challenge => value offset residual challenge = 0).card *
        Fintype.card F ≤ (polynomial offset residual).totalDegree * Fintype.card F ^ n := by
    simpa only [eval_polynomial] using (show
      (Finset.univ.filter fun challenge => eval challenge (polynomial offset residual) = 0).card *
        Fintype.card F ≤ (polynomial offset residual).totalDegree * Fintype.card F ^ n by
      exact_mod_cast h)
  exact hnat.trans (by
    simpa using Nat.mul_le_mul_right (Fintype.card F ^ n)
      (polynomial_degree offset residual))

end GordieHowe.AffineBatching
