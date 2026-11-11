-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.NegacyclicParseval
public import GordieHowe.Foundations.ToMathlib.FixedTrig

public section

/-!
# The negacyclic spectrum in fixed point

For `n = 2^e` and an integer vector `f`, the real and imaginary parts of `spec f j` are
`∑ i, f i cos (π i (2j + 1) / n)` and `∑ i, f i sin (π i (2j + 1) / n)`. With the fixed-point
cosine and sine at scale `2^P` in their place, `specReFix e P f j` and `specImFix e P f j` are
within `‖f‖₁` of `2^P` times those parts, so the natural number

    specSqFix e P f j = (|specReFix| + ‖f‖₁)² + (|specImFix| + ‖f‖₁)²

bounds `2^(2P) · specSq f j` (`specSq_le_specSqFix`).
-/

namespace GordieHowe.DFT

open Finset

variable {n : ℕ}

/-- The `ℓ₁` norm `∑ i, |f i|` of an integer vector. -/
def l1Norm (f : Fin n → ℤ) : ℕ := ∑ i, (f i).natAbs

/-- The real part of the spectrum at frequency `j` in fixed point at scale `2^P`,
`∑ i, f i · cosFix e P (i (2j + 1))`. -/
def specReFix (e P : ℕ) (f : Fin n → ℤ) (j : Fin n) : ℤ :=
  ∑ i, f i * FixedPoint.cosFix e P ((i : ℕ) * (2 * j + 1))

/-- The imaginary part of the spectrum at frequency `j` in fixed point at scale `2^P`,
`∑ i, f i · sinFix e P (i (2j + 1))`. -/
def specImFix (e P : ℕ) (f : Fin n → ℤ) (j : Fin n) : ℤ :=
  ∑ i, f i * FixedPoint.sinFix e P ((i : ℕ) * (2 * j + 1))

/-- **The squared spectrum in fixed point**: `(|specReFix| + ‖f‖₁)² + (|specImFix| + ‖f‖₁)²`,
an upper bound on `2^(2P) · specSq f j` for `n = 2^e`. -/
def specSqFix (e P : ℕ) (f : Fin n → ℤ) (j : Fin n) : ℕ :=
  ((specReFix e P f j).natAbs + l1Norm f) ^ 2 + ((specImFix e P f j).natAbs + l1Norm f) ^ 2

/-- For `n = 2^e`, the root of the negacyclic transform is `exp (i π / 2^e)`. -/
theorem negRoot_eq_unitRoot {e : ℕ} (hn : n = 2 ^ e) : negRoot n = FixedPoint.unitRoot e := by
  subst hn
  rw [negRoot_eq, FixedPoint.unitRoot_eq]
  congr 1
  push_cast
  field_simp

/-- A weighted sum of values within `1` of `c i` is within `∑ |f i|` of `∑ f i · c i`. -/
theorem abs_sum_mul_sub_le (f g : Fin n → ℤ) (c : Fin n → ℝ) (hg : ∀ i, |(g i : ℝ) - c i| ≤ 1) :
    |((∑ i, f i * g i : ℤ) : ℝ) - ∑ i, (f i : ℝ) * c i| ≤ l1Norm f := by
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [l1Norm, Nat.cast_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_sub, abs_mul, Nat.cast_natAbs, Int.cast_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (hg i)

/-- `x ≤ |a| + b` squared: from `|x − a| ≤ b`, `x² ≤ (|a| + b)²`. -/
theorem sq_le_sq_abs_add_of_abs_sub_le {x a b : ℝ} (h : |x - a| ≤ b) : x ^ 2 ≤ (|a| + b) ^ 2 := by
  have hx : |x| ≤ |a| + b := by
    calc |x| = |a + (x - a)| := by ring_nf
      _ ≤ |a| + |x - a| := abs_add_le _ _
      _ ≤ |a| + b := by linarith
  rw [← sq_abs x]
  exact pow_le_pow_left₀ (abs_nonneg _) hx 2

/-- **The fixed-point squared spectrum bounds the spectrum**: for `n = 2^e`,
`2^(2P) · specSq f j ≤ specSqFix e P f j`. -/
theorem specSq_le_specSqFix {e : ℕ} (P : ℕ) (hn : n = 2 ^ e) (f : Fin n → ℤ) (j : Fin n) :
    2 ^ (2 * P) * specSq f j ≤ specSqFix e P f j := by
  set ψ := FixedPoint.unitRoot e
  have hspec : spec f j = ∑ i, (f i : ℂ) * ψ ^ ((i : ℕ) * (2 * j + 1)) := by
    rw [spec_eq_sum, negRoot_eq_unitRoot hn]
  have hre : (spec f j).re =
      ∑ i, (f i : ℝ) * Real.cos (Real.pi * (((i : ℕ) * (2 * j + 1) : ℕ) : ℝ) / 2 ^ e) := by
    rw [hspec, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
    rw [(FixedPoint.re_im_unitRoot_pow e _).1]
  have him : (spec f j).im =
      ∑ i, (f i : ℝ) * Real.sin (Real.pi * (((i : ℕ) * (2 * j + 1) : ℕ) : ℝ) / 2 ^ e) := by
    rw [hspec, Complex.im_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero]
    rw [(FixedPoint.re_im_unitRoot_pow e _).2]
  have hR := abs_sum_mul_sub_le f (fun i => FixedPoint.cosFix e P ((i : ℕ) * (2 * j + 1)))
    (fun i => 2 ^ P * Real.cos (Real.pi * (((i : ℕ) * (2 * j + 1) : ℕ) : ℝ) / 2 ^ e))
    fun i => FixedPoint.abs_cosFix_sub_le e P _
  have hI := abs_sum_mul_sub_le f (fun i => FixedPoint.sinFix e P ((i : ℕ) * (2 * j + 1)))
    (fun i => 2 ^ P * Real.sin (Real.pi * (((i : ℕ) * (2 * j + 1) : ℕ) : ℝ) / 2 ^ e))
    fun i => FixedPoint.abs_sinFix_sub_le e P _
  have eR : ∑ i, (f i : ℝ) * (2 ^ P * Real.cos (Real.pi * (((i : ℕ) * (2 * j + 1) : ℕ) : ℝ) /
      2 ^ e)) = 2 ^ P * (spec f j).re := by
    rw [hre, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have eI : ∑ i, (f i : ℝ) * (2 ^ P * Real.sin (Real.pi * (((i : ℕ) * (2 * j + 1) : ℕ) : ℝ) /
      2 ^ e)) = 2 ^ P * (spec f j).im := by
    rw [him, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [eR] at hR
  rw [eI] at hI
  rw [abs_sub_comm] at hR hI
  have h1 := sq_le_sq_abs_add_of_abs_sub_le hR
  have h2 := sq_le_sq_abs_add_of_abs_sub_le hI
  have hsq : 2 ^ (2 * P) * specSq f j =
      (2 ^ P * (spec f j).re) ^ 2 + (2 ^ P * (spec f j).im) ^ 2 := by
    rw [specSq_eq, Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hsq, specSqFix, specReFix, specImFix]
  push_cast
  rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
  push_cast at h1 h2 ⊢
  linarith

end GordieHowe.DFT
