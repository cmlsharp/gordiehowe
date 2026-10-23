-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.NNRealDyadic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

/-!
# Ratios of naturals below a real power of two

`num / den ≤ 2^s` in `ℝ≥0` for a real exponent `s` with `s · n = −e`, from the inequality
`num^n · 2^e ≤ den^n` of naturals, the form in which a per-round error with a fractional number of
bits is checked by `decide`. Candidates for Mathlib.
-/

namespace GordieHowe

open scoped NNReal

/-- **A bound by a real power of two from a bound on a natural power**: `x ≤ 2^s` when
`x^n ≤ 2^(s · n)` for some `n ≠ 0`. -/
theorem le_two_rpow_of_pow_le {x : ℝ≥0} {n : ℕ} (hn : n ≠ 0) {s : ℝ}
    (h : x ^ n ≤ (2 : ℝ≥0) ^ (s * n)) : x ≤ (2 : ℝ≥0) ^ s := by
  rw [NNReal.rpow_mul, NNReal.rpow_natCast] at h
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) hn).mp h

/-- **A ratio of naturals below a real power of two**: `num / den ≤ 2^s` when `s · n = −e` and
`num^n · 2^e ≤ den^n` for some `n ≠ 0`. -/
theorem ratio_le_two_rpow {num den n e : ℕ} {s : ℝ} (hd : 0 < den) (hn : n ≠ 0)
    (hs : s * n = -(e : ℝ)) (h : num ^ n * 2 ^ e ≤ den ^ n) :
    (num : ℝ≥0) / den ≤ (2 : ℝ≥0) ^ s := by
  refine le_two_rpow_of_pow_le hn ?_
  rw [hs, NNReal.rpow_neg, NNReal.rpow_natCast, div_pow, ← Nat.cast_pow, ← Nat.cast_pow,
    ← one_div]
  exact_mod_cast ratio_le_dyadic (c := 1) (pow_pos hd n) (by rw [one_mul]; exact h)

/-- **A real bounded by a dyadic ratio, below a real power of two**: `x ≤ 2^s` in `ℝ` when
`x ≤ M / 2^E`, `s · n = −e` and `M^n · 2^e ≤ (2^E)^n` for some `n ≠ 0` (`ratio_le_two_rpow`). -/
theorem real_le_two_rpow_of_le_ratio {x : ℝ} {M E n e : ℕ} {s : ℝ} (hn : n ≠ 0)
    (hs : s * n = -(e : ℝ)) (hx : x ≤ M / 2 ^ E) (h : M ^ n * 2 ^ e ≤ (2 ^ E) ^ n) :
    x ≤ (2 : ℝ) ^ s := by
  have h' := ratio_le_two_rpow (num := M) (den := 2 ^ E) (pow_pos two_pos E) hn hs h
  have h'' := NNReal.coe_le_coe.mpr h'
  push_cast at h''
  exact hx.trans h''

/-- A real power of two is monotone in the exponent. -/
theorem two_rpow_le_two_rpow {s s' : ℝ} (h : s ≤ s') : (2 : ℝ≥0) ^ s ≤ (2 : ℝ≥0) ^ s' :=
  NNReal.rpow_le_rpow_of_exponent_le one_le_two h

/-- **A ratio over `q − 1` plus `L` ratios over `q`** as one ratio of naturals:
`B / (q − 1) + L · (l / q) = (B q + L l (q − 1)) / ((q − 1) q)`, for `q > 1`. -/
theorem ratio_pred_add_mul_ratio {B L l q : ℕ} (hq : 1 < q) :
    (B : ℝ≥0) / ((q : ℝ≥0) - 1) + L * ((l : ℝ≥0) / q) =
      ((B * q + L * l * (q - 1) : ℕ) : ℝ≥0) / ((q - 1) * q : ℕ) := by
  have h1 : ((q - 1 : ℕ) : ℝ≥0) ≠ 0 := by exact_mod_cast (show q - 1 ≠ 0 by omega)
  have h2 : (q : ℝ≥0) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [show (q : ℝ≥0) - 1 = ((q - 1 : ℕ) : ℝ≥0) by rw [Nat.cast_tsub, Nat.cast_one],
    ← mul_div_assoc, div_add_div _ _ h1 h2]
  simp only [Nat.cast_add, Nat.cast_mul]
  ring

end GordieHowe
