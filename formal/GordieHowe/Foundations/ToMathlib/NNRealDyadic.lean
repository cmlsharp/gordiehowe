-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Basic.NNReal.Basic

@[expose] public section

/-!
# Ratios of naturals below a dyadic

`num / den ≤ c / 2^e` in `ℝ≥0` from the inequality `num · 2^e ≤ c · den` of naturals, the form in
which the configurations' per-round error bounds are checked by `decide`. Candidates for Mathlib.
-/

namespace GordieHowe

open scoped NNReal

/-- **A ratio of naturals below a dyadic**: `num / den ≤ c / 2^e` when `num · 2^e ≤ c · den`. -/
theorem ratio_le_dyadic {num den c e : ℕ} (hd : 0 < den) (h : num * 2 ^ e ≤ c * den) :
    (num : ℝ≥0) / den ≤ (c : ℝ≥0) / 2 ^ e := by
  rw [div_le_div_iff₀ (by exact_mod_cast hd) (by positivity)]
  exact_mod_cast h

/-- **The commit error below a dyadic**: `num / (q − 1) ≤ c / 2^e` when
`num · 2^e ≤ c · (q − 1)`. -/
theorem ratio_pred_le_dyadic {num q c e : ℕ} (h : num * 2 ^ e ≤ c * (q - 1)) :
    (num : ℝ≥0) / ((q : ℝ≥0) - 1) ≤ (c : ℝ≥0) / 2 ^ e := by
  rw [show (q : ℝ≥0) - 1 = ((q - 1 : ℕ) : ℝ≥0) by rw [Nat.cast_tsub, Nat.cast_one]]
  rcases Nat.eq_zero_or_pos (q - 1) with h0 | h0
  · rw [h0, Nat.cast_zero, div_zero]
    positivity
  · exact ratio_le_dyadic h0 h

/-- **The commit error of `nrep` repetitions below a dyadic**: `(num / (q − 1)) ^ nrep ≤ c / 2^e`
when `num ^ nrep · 2^e ≤ c · (q − 1) ^ nrep`. -/
theorem ratio_pred_pow_le_dyadic {num q c e nrep : ℕ}
    (h : num ^ nrep * 2 ^ e ≤ c * (q - 1) ^ nrep) :
    ((num : ℝ≥0) / ((q : ℝ≥0) - 1)) ^ nrep ≤ (c : ℝ≥0) / 2 ^ e := by
  rw [show (q : ℝ≥0) - 1 = ((q - 1 : ℕ) : ℝ≥0) by rw [Nat.cast_tsub, Nat.cast_one], div_pow,
    ← Nat.cast_pow, ← Nat.cast_pow]
  rcases Nat.eq_zero_or_pos ((q - 1) ^ nrep) with h0 | h0
  · rw [h0, Nat.cast_zero, div_zero]
    positivity
  · exact ratio_le_dyadic h0 h

/-- **A column round below a dyadic**: the far, mask and joint subfield counts over one
denominator. -/
theorem column_le_dyadic {A B E den c e : ℕ} (hd : 0 < den) (h : (A + B + E) * 2 ^ e ≤ c * den) :
    ((A : ℝ≥0) + B) / den + (E : ℝ≥0) / den ≤ (c : ℝ≥0) / 2 ^ e := by
  rw [← add_div]
  exact_mod_cast ratio_le_dyadic hd h

end GordieHowe
