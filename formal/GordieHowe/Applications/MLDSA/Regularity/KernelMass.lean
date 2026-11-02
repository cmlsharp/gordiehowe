-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The `ℓ¹` mass of the single-coefficient kernel

A weight `f` on `ZMod q` with `0 ≤ f ≤ 1` and `f x · |x| ≤ C` for `x ≠ 0` (`|x|` the centered
absolute value) has total mass `∑_x f x ≤ 1 + 2 (J + C ∑_{J < a ≤ (q-1)/2} 1/a)`. With the
dyadic bound `∑_{2^s ≤ a < 2^(s+t)} 1/a ≤ t` (`sum_Ico_two_pow_inv_le`) this gives
`∑_x f x ≤ 33 + 36 C` at `q = 8380417` (`sum_le_of_mul_abs_le`), so `∑_x f x ≤ 610` for
`C ≤ 16.02` (`sum_le_610`), covering the hint-split kernels `C = q / L` of ML-DSA-65
(`q / 523383 ≈ 16.012`) and ML-DSA-87 (`q / 523535 ≈ 16.007`), and `∑_x f x ≤ 1620` for
`C ≤ q / 190307 ≈ 44.04` (`sum_le_1620`), the hint-split kernel of ML-DSA-44. This is
the mass `S₁` of the fixed-mask route (note, Section 6, (18), with the dyadic bound in place of the
logarithm).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

/-- Dyadic harmonic blocks: `∑_{2^s ≤ a < 2^(s+t)} 1/a ≤ t`. -/
theorem sum_Ico_two_pow_inv_le (s t : ℕ) :
    ∑ a ∈ (Ico (2 ^ s) (2 ^ (s + t)) : Finset ℕ), (1 / (a : ℝ)) ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← Finset.sum_Ico_consecutive _ (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega))
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : s + t ≤ s + (t + 1)))]
    have hblock : ∑ a ∈ (Ico (2 ^ (s + t)) (2 ^ (s + (t + 1))) : Finset ℕ), (1 / (a : ℝ)) ≤ 1 := by
      have hpos : (0 : ℝ) < 2 ^ (s + t) := by positivity
      calc ∑ a ∈ (Ico (2 ^ (s + t)) (2 ^ (s + (t + 1))) : Finset ℕ), (1 / (a : ℝ))
          ≤ ∑ _a ∈ (Ico (2 ^ (s + t)) (2 ^ (s + (t + 1))) : Finset ℕ), (1 / (2 : ℝ) ^ (s + t)) := by
            refine Finset.sum_le_sum fun a ha => ?_
            have : (2 : ℝ) ^ (s + t) ≤ a := by exact_mod_cast (Finset.mem_Ico.mp ha).1
            exact one_div_le_one_div_of_le hpos this
        _ = 1 := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
              show 2 ^ (s + (t + 1)) - 2 ^ (s + t) = 2 ^ (s + t) by rw [← add_assoc, pow_succ]; omega]
            push_cast
            field_simp
    push_cast
    linarith

/-- The kernel mass at `q = 8380417`: `∑_x f x ≤ 1 + 2 (16 + 18 C) = 33 + 36 C`, keeping the
sixteen coefficients of centered absolute value at most `16` at `1` and the rest at `C / a` over
the eighteen dyadic blocks `[2^4, 2^22)`. -/
theorem sum_le_of_mul_abs_le {f : ZMod 8380417 → ℝ} {C : ℝ} (h0 : ∀ x, 0 ≤ f x)
    (h1 : ∀ x, f x ≤ 1) (hC : ∀ x, x ≠ 0 → f x * |(x.valMinAbs : ℝ)| ≤ C) :
    ∑ x, f x ≤ 33 + 36 * C := by
  -- `h a` bounds `f` at centered absolute value `a`
  have hle : ∀ x : ZMod 8380417, ∀ a : ℕ, (x.valMinAbs.natAbs = a) → 1 ≤ a →
      f x ≤ if a ≤ 16 then 1 else C / a := by
    intro x a hxa ha
    split_ifs
    · exact h1 x
    · have hx0 : x ≠ 0 := by
        intro h
        rw [h, ZMod.valMinAbs_zero] at hxa
        omega
      have hpos : (0 : ℝ) < a := by exact_mod_cast ha
      have habs : |(x.valMinAbs : ℝ)| = a := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs, hxa]
        simp
      rw [le_div_iff₀ hpos, ← habs]
      exact hC x hx0
  set hf : ℕ → ℝ := fun a => if a ≤ 16 then 1 else C / a
  have hC0 : 0 ≤ C := le_trans (mul_nonneg (h0 1) (abs_nonneg _)) (hC 1 (by decide))
  have hsum_eq : ∑ x, f x = ∑ v ∈ range 8380417, f (v : ZMod 8380417) := by
    refine Finset.sum_nbij' (fun x : ZMod 8380417 => x.val) (fun v => (v : ZMod 8380417))
      (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x)) (fun _ _ => Finset.mem_univ _)
      (fun x _ => ZMod.natCast_zmod_val x) (fun v hv => ZMod.val_natCast_of_lt
        (Finset.mem_range.mp hv)) (fun x _ => by rw [ZMod.natCast_zmod_val])
  have hsplit : range 8380417 = range 1 ∪ (Ico 1 4190209 ∪ (Ico 4190209 8380417 : Finset ℕ)) := by
    ext v
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj1 : Disjoint (range 1) (Ico 1 4190209 ∪ (Ico 4190209 8380417 : Finset ℕ)) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at hv hv'
    omega
  have hdisj2 : Disjoint (Ico 1 4190209 : Finset ℕ) (Ico 4190209 8380417) :=
    Finset.Ico_disjoint_Ico_consecutive _ _ _
  have hlow : ∑ v ∈ (Ico 1 4190209 : Finset ℕ), f (v : ZMod 8380417) ≤ ∑ a ∈ (Ico 1 4190209 : Finset ℕ), hf a := by
    refine Finset.sum_le_sum fun v hv => ?_
    obtain ⟨hv1, hv2⟩ := Finset.mem_Ico.mp hv
    refine hle _ v ?_ hv1
    rw [ZMod.valMinAbs_natCast_of_le_half (by omega)]
    simp
  have hhigh : ∑ v ∈ (Ico 4190209 8380417 : Finset ℕ), f (v : ZMod 8380417) ≤ ∑ a ∈ (Ico 1 4190209 : Finset ℕ), hf a := by
    calc ∑ v ∈ (Ico 4190209 8380417 : Finset ℕ), f (v : ZMod 8380417) ≤ ∑ v ∈ (Ico 4190209 8380417 : Finset ℕ), hf (8380417 - v) := by
          refine Finset.sum_le_sum fun v hv => ?_
          obtain ⟨hv1, hv2⟩ := Finset.mem_Ico.mp hv
          refine hle _ _ ?_ (by omega)
          rw [ZMod.valMinAbs_natCast_of_half_lt (by omega) hv2]
          omega
      _ = ∑ a ∈ (Ico 1 4190209 : Finset ℕ), hf a := by
          rw [Finset.sum_Ico_reflect hf 4190209 (by norm_num : 8380417 ≤ 8380417 + 1)]
  have hhalf : ∑ a ∈ (Ico 1 4190209 : Finset ℕ), hf a ≤ 16 + C * 18 := by
    rw [← Finset.sum_Ico_consecutive _ (by norm_num : 1 ≤ 17) (by norm_num : 17 ≤ 4190209)]
    have e1 : ∑ a ∈ (Ico 1 17 : Finset ℕ), hf a = 16 := by
      rw [Finset.sum_congr rfl fun a ha => if_pos (by simp at ha; omega)]
      simp
    have e2 : ∑ a ∈ (Ico 17 4190209 : Finset ℕ), hf a ≤ C * 18 := by
      calc ∑ a ∈ (Ico 17 4190209 : Finset ℕ), hf a = C * ∑ a ∈ (Ico 17 4190209 : Finset ℕ), (1 / (a : ℝ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a ha => ?_
            simp only [hf]
            rw [if_neg (by simp at ha; omega), mul_one_div]
        _ ≤ C * ∑ a ∈ (Ico 16 4194304 : Finset ℕ), (1 / (a : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hC0
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun a _ _ =>
              one_div_nonneg.mpr (Nat.cast_nonneg a)
            intro a ha
            rw [Finset.mem_Ico] at ha ⊢
            omega
        _ ≤ C * 18 := by
            refine mul_le_mul_of_nonneg_left ?_ hC0
            have hd := sum_Ico_two_pow_inv_le 4 18
            norm_num at hd
            simpa only [one_div] using hd
    linarith
  rw [hsum_eq, hsplit, Finset.sum_union hdisj1, Finset.sum_union hdisj2, Finset.sum_range_one]
  have := h1 ((0 : ℕ) : ZMod 8380417)
  linarith

/-- The kernel mass at `q = 8380417` for `C ≤ 16.02`: `∑_x f x ≤ 610`. -/
theorem sum_le_610 {f : ZMod 8380417 → ℝ} {C : ℝ} (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1)
    (hC : ∀ x, x ≠ 0 → f x * |(x.valMinAbs : ℝ)| ≤ C) (hC' : C ≤ 1602 / 100) :
    ∑ x, f x ≤ 610 := by
  linarith [sum_le_of_mul_abs_le h0 h1 hC]

/-- The kernel mass at `q = 8380417` for `C ≤ q / 190307` (the hint-split kernel of ML-DSA-44,
`C = q / L` with `L = 190307`): `∑_x f x ≤ 1620`. -/
theorem sum_le_1620 {f : ZMod 8380417 → ℝ} {C : ℝ} (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1)
    (hC : ∀ x, x ≠ 0 → f x * |(x.valMinAbs : ℝ)| ≤ C) (hC' : C ≤ 8380417 / 190307) :
    ∑ x, f x ≤ 1620 := by
  have := sum_le_of_mul_abs_le h0 h1 hC
  have : (33 : ℝ) + 36 * (8380417 / 190307) ≤ 1620 := by norm_num
  linarith

end GordieHowe.MLDSA.Regularity
