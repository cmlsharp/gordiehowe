-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFOracleQuenched

public section

/-!
# The law with a given density

* `ofWeight`: the law on a finite type with density proportional to a weight `w`
  (`ofWeight_apply`, `toReal_ofWeight_apply`).
* `ofWeight_one`: a constant density gives the uniform law.
* `condSome_eq_ofWeight`: an attempt whose accepted mass is proportional to `w`, conditioned on
  acceptance, is `ofWeight w`.
* `tvDist_ofWeight_le_of_le`: for weights `f ≤ g`, the laws `ofWeight f` and `ofWeight g` are
  within `∑ (g - f) / ∑ g` (`sum_abs_div_sub_div_le`).

About Mathlib objects only.
-/

open Finset
open scoped ENNReal BigOperators

namespace PMF

variable {α : Type*} [Fintype α]

/-- **The law with density proportional to `w`**, for a weight with finite positive total. -/
noncomputable def ofWeight (w : α → ℝ≥0∞) (h0 : ∑ a, w a ≠ 0) (ht : ∑ a, w a ≠ ⊤) : PMF α :=
  ofFintype (fun a => w a / ∑ b, w b) (by
    simp only [div_eq_mul_inv]
    rw [← sum_mul, ENNReal.mul_inv_cancel h0 ht])

/-- The density of `ofWeight w`. -/
theorem ofWeight_apply (w : α → ℝ≥0∞) (h0 : ∑ a, w a ≠ 0) (ht : ∑ a, w a ≠ ⊤) (a : α) :
    ofWeight w h0 ht a = w a / ∑ b, w b := by
  rw [ofWeight, ofFintype_apply]

/-- The density of `ofWeight w`, in `ℝ`. -/
theorem toReal_ofWeight_apply (w : α → ℝ≥0∞) (h0 : ∑ a, w a ≠ 0) (ht : ∑ a, w a ≠ ⊤) (a : α) :
    (ofWeight w h0 ht a).toReal = (w a).toReal / ∑ b, (w b).toReal := by
  rw [ofWeight_apply, ENNReal.toReal_div, ENNReal.toReal_sum fun b _ =>
    ne_top_of_le_ne_top ht (single_le_sum (fun c _ => zero_le) (mem_univ b))]

/-- **A constant density** gives the uniform law. -/
theorem ofWeight_one [Nonempty α] (h0 : ∑ _a : α, (1 : ℝ≥0∞) ≠ 0) (ht : ∑ _a : α, (1 : ℝ≥0∞) ≠ ⊤) :
    ofWeight (fun _ : α => (1 : ℝ≥0∞)) h0 ht = uniformOfFintype α := by
  ext a
  rw [ofWeight_apply, uniformOfFintype_apply, sum_const, card_univ, nsmul_eq_mul, mul_one, one_div]

/-- **An attempt proportional to `w`**: if the accepted mass of `A` at `a` is `r · w a` with
`r ≠ 0`, the law of `A` conditioned on acceptance is `ofWeight w`. -/
theorem condSome_eq_ofWeight {A : PMF (Option α)} (h : A none ≠ 1) (w : α → ℝ≥0∞)
    (h0 : ∑ a, w a ≠ 0) (ht : ∑ a, w a ≠ ⊤) {r : ℝ≥0∞} (hA : ∀ a, A (some a) = r * w a) :
    condSome A h = ofWeight w h0 ht :=
  eq_of_apply_eq_mul (F := w) (a := r * (1 - A none)⁻¹) (b := (∑ b, w b)⁻¹)
    (fun a => by rw [condSome_apply, hA, div_eq_mul_inv]; ring)
    (fun a => by rw [ofWeight_apply, div_eq_mul_inv, mul_comm])

/-- **Two laws with densities `f ≤ g`** are within `∑ (g - f) / ∑ g` in total variation. -/
theorem tvDist_ofWeight_le_of_le {f g : α → ℝ≥0∞} (hf0 : ∑ a, f a ≠ 0) (hft : ∑ a, f a ≠ ⊤)
    (hg0 : ∑ a, g a ≠ 0) (hgt : ∑ a, g a ≠ ⊤) (hfg : ∀ a, f a ≤ g a) :
    tvDist (ofWeight f hf0 hft) (ofWeight g hg0 hgt) ≤
      (∑ a, ((g a).toReal - (f a).toReal)) / ∑ a, (g a).toReal := by
  have hgfin : ∀ a, g a ≠ ⊤ := fun a =>
    ne_top_of_le_ne_top hgt (single_le_sum (fun c _ => zero_le) (mem_univ a))
  have hffin : ∀ a, f a ≠ ⊤ := fun a => ne_top_of_le_ne_top (hgfin a) (hfg a)
  have hpos : ∀ (w : α → ℝ≥0∞), ∑ a, w a ≠ 0 → ∑ a, w a ≠ ⊤ → 0 < ∑ a, (w a).toReal :=
    fun w h0 ht => by
      rw [← ENNReal.toReal_sum fun b _ =>
        ne_top_of_le_ne_top ht (single_le_sum (fun c _ => zero_le) (mem_univ b))]
      exact ENNReal.toReal_pos h0 ht
  rw [tvDist_eq_sum]
  simp only [toReal_ofWeight_apply]
  have h := sum_abs_div_sub_div_le (f := fun a => (f a).toReal) (g := fun a => (g a).toReal)
    (fun _ => ENNReal.toReal_nonneg) (hpos f hf0 hft) (hpos g hg0 hgt)
  have habs : ∑ a, |(f a).toReal - (g a).toReal| = ∑ a, ((g a).toReal - (f a).toReal) :=
    sum_congr rfl fun a _ => by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (ENNReal.toReal_mono (hgfin a) (hfg a)))]
  rw [habs, mul_div_assoc] at h
  linarith

end PMF
