-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFOracleQuenched

public section

/-!
# Conditioned attempts against a scaled accepted mass

* `tvDist_condSome_le_scaled`: two attempts conditioned on acceptance are within
  `∑ |A₀(a) - r · A₁(a)| / (r · ∑ A₁(a))` for every scale `r > 0`, the accepted masses read in `ℝ`
  (`sum_abs_div_sub_div_le`).
* `LoopSigner.keptLaw`: the law of a loop signer's kept `(w₁, c)` when every attempt draws a
  fresh uniform challenge (`freshAttempt`), conditioned on keeping.

About Mathlib objects only.
-/

open Finset
open scoped ENNReal BigOperators

namespace PMF

section CondSome

variable {α : Type*} [Fintype α]

/-- The accepted mass of an attempt that does not always reject is positive, in `ℝ`. -/
theorem sum_toReal_apply_some_pos {A : PMF (Option α)} (h : A none ≠ 1) :
    0 < ∑ a, (A (some a)).toReal := by
  rw [sum_toReal_apply_some]
  exact ENNReal.toReal_pos (one_sub_apply_none_ne_zero h)
    (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)

/-- The conditioned law in `ℝ`: the accepted mass over the total accepted mass. -/
theorem toReal_condSome_apply (A : PMF (Option α)) (h : A none ≠ 1) (a : α) :
    (condSome A h a).toReal = (A (some a)).toReal / ∑ b, (A (some b)).toReal := by
  rw [condSome_apply, ENNReal.toReal_div, sum_toReal_apply_some]

/-- **Two conditioned attempts against a scaled accepted mass**: for every `r > 0`, the laws of
`A₀` and `A₁` conditioned on acceptance are within `∑ |A₀(a) - r · A₁(a)| / (r · ∑ A₁(a))`. -/
theorem tvDist_condSome_le_scaled (A₀ A₁ : PMF (Option α)) (h₀ : A₀ none ≠ 1)
    (h₁ : A₁ none ≠ 1) {r : ℝ} (hr : 0 < r) :
    tvDist (condSome A₀ h₀) (condSome A₁ h₁) ≤
      (∑ a, |(A₀ (some a)).toReal - r * (A₁ (some a)).toReal|) /
        (r * ∑ a, (A₁ (some a)).toReal) := by
  have hg : ∀ a, (A₁ (some a)).toReal / ∑ b, (A₁ (some b)).toReal =
      r * (A₁ (some a)).toReal / (r * ∑ b, (A₁ (some b)).toReal) := fun a =>
    (mul_div_mul_left _ _ hr.ne').symm
  have h := sum_abs_div_sub_div_le (f := fun a => (A₀ (some a)).toReal)
    (g := fun a => r * (A₁ (some a)).toReal) (fun _ => ENNReal.toReal_nonneg)
    (sum_toReal_apply_some_pos h₀)
    (by rw [← mul_sum]; exact mul_pos hr (sum_toReal_apply_some_pos h₁))
  rw [← mul_sum, mul_div_assoc] at h
  rw [tvDist_eq_sum]
  simp only [toReal_condSome_apply, hg]
  linarith

/-- An attempt that always rejects conditions to the default law. -/
theorem condSomeOr_of_apply_none_eq_one {A : PMF (Option α)} (d : PMF α) (h : A none = 1) :
    condSomeOr A d = d := by
  rw [condSomeOr]
  simp [h]

end CondSome

section KeptLaw

variable {V C : Type} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype C] [DecidableEq C]
  [Nonempty C]

/-- **The kept law of a loop signer with fresh challenges**: every attempt draws `y ← P` and a
fresh uniform challenge `c`, accepts by `acc`, and keeps `(w1 y, c)` with probability `κ`
(`freshAttempt`); the law of the kept pair, or the uniform law if no attempt keeps. -/
@[expose] noncomputable def LoopSigner.keptLaw (S : LoopSigner V C) [Fintype S.Y] : PMF (V × C) :=
  condSomeOr (freshAttempt S.P S.w1 S.acc S.κ S.hκ) (uniformOfFintype _)

end KeptLaw

end PMF
