-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Data.NNRat.BigOperators
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-!
# Nonnegative rationals as extended nonnegative reals

Weights that a program compares are nonnegative rationals (`ℚ≥0`, whose order and arithmetic have
compiled code), and the probability bounds about them are stated in `ℝ≥0∞`. Mathlib casts `ℚ≥0`
into `ℝ≥0∞` through `ℝ≥0` (`ENNReal.coe_nnratCast`) but states its cast lemmas only for division
semirings, which `ℝ≥0∞` is not. This file states them for `ℝ≥0∞`.

- The cast lemmas (`norm_cast`): `0`, `1`, natural numbers, `+`, `*`, `/` (by a nonzero rational),
  `min`, `max`, finite sums and products, the order (`≤`, `<`, `=`), finiteness and `toReal`.
- `NNRat.minOneDiv a b`: `min 1 (a / b)` with the value `ℝ≥0∞` gives it at `b = 0` (`1` for
  `a ≠ 0`, `0` for `a = 0`), so that its cast is `min 1 (a / b)` in `ℝ≥0∞`
  (`ENNReal.nnratCast_minOneDiv`) for all `a` and `b`.
-/

open scoped ENNReal NNReal NNRat BigOperators

namespace ENNReal

variable {q r : ℚ≥0}

/-- The cast into `ℝ≥0∞` is the cast into `ℝ≥0` followed by the coercion. -/
theorem nnratCast_def (q : ℚ≥0) : (q : ℝ≥0∞) = ((q : ℝ≥0) : ℝ≥0∞) := rfl

@[simp] theorem nnratCast_ne_top (q : ℚ≥0) : (q : ℝ≥0∞) ≠ ⊤ := coe_ne_top

@[simp] theorem nnratCast_lt_top (q : ℚ≥0) : (q : ℝ≥0∞) < ⊤ := coe_lt_top

@[norm_cast] theorem toReal_nnratCast (q : ℚ≥0) : (q : ℝ≥0∞).toReal = (q : ℝ) := by
  rw [nnratCast_def, coe_toReal]
  rfl

@[simp, norm_cast] theorem nnratCast_zero : ((0 : ℚ≥0) : ℝ≥0∞) = 0 := by
  simp [nnratCast_def]

@[simp, norm_cast] theorem nnratCast_one : ((1 : ℚ≥0) : ℝ≥0∞) = 1 := by
  simp [nnratCast_def]

@[simp, norm_cast] theorem nnratCast_natCast (n : ℕ) : ((n : ℚ≥0) : ℝ≥0∞) = n := by
  simp [nnratCast_def]

@[simp, norm_cast] theorem nnratCast_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((OfNat.ofNat n : ℚ≥0) : ℝ≥0∞) = OfNat.ofNat n :=
  nnratCast_natCast n

@[simp, norm_cast] theorem nnratCast_add (q r : ℚ≥0) :
    ((q + r : ℚ≥0) : ℝ≥0∞) = (q : ℝ≥0∞) + (r : ℝ≥0∞) := by
  simp [nnratCast_def, NNRat.cast_add]

@[simp, norm_cast] theorem nnratCast_mul (q r : ℚ≥0) :
    ((q * r : ℚ≥0) : ℝ≥0∞) = (q : ℝ≥0∞) * (r : ℝ≥0∞) := by
  simp [nnratCast_def, NNRat.cast_mul]

@[simp, norm_cast] theorem nnratCast_div (q : ℚ≥0) (hr : r ≠ 0) :
    ((q / r : ℚ≥0) : ℝ≥0∞) = (q : ℝ≥0∞) / (r : ℝ≥0∞) := by
  rw [nnratCast_def, nnratCast_def, nnratCast_def, NNRat.cast_div,
    coe_div (by exact_mod_cast hr)]

@[simp, norm_cast] theorem nnratCast_le_nnratCast : (q : ℝ≥0∞) ≤ (r : ℝ≥0∞) ↔ q ≤ r := by
  simp [nnratCast_def]

@[simp, norm_cast] theorem nnratCast_lt_nnratCast : (q : ℝ≥0∞) < (r : ℝ≥0∞) ↔ q < r := by
  simp [nnratCast_def]

@[simp, norm_cast] theorem nnratCast_inj : (q : ℝ≥0∞) = (r : ℝ≥0∞) ↔ q = r := by
  simp [nnratCast_def]

@[simp] theorem nnratCast_eq_zero : (q : ℝ≥0∞) = 0 ↔ q = 0 := by
  rw [← nnratCast_zero, nnratCast_inj]

theorem nnratCast_ne_zero : (q : ℝ≥0∞) ≠ 0 ↔ q ≠ 0 := nnratCast_eq_zero.not

@[simp] theorem nnratCast_le_one : (q : ℝ≥0∞) ≤ 1 ↔ q ≤ 1 := by
  rw [← nnratCast_one, nnratCast_le_nnratCast]

/-- The cast is monotone. -/
theorem nnratCast_mono : Monotone fun q : ℚ≥0 => (q : ℝ≥0∞) :=
  fun _ _ h => nnratCast_le_nnratCast.2 h

@[simp, norm_cast] theorem nnratCast_min (q r : ℚ≥0) :
    ((min q r : ℚ≥0) : ℝ≥0∞) = min (q : ℝ≥0∞) (r : ℝ≥0∞) :=
  nnratCast_mono.map_min

@[simp, norm_cast] theorem nnratCast_max (q r : ℚ≥0) :
    ((max q r : ℚ≥0) : ℝ≥0∞) = max (q : ℝ≥0∞) (r : ℝ≥0∞) :=
  nnratCast_mono.map_max

@[simp, norm_cast] theorem nnratCast_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ≥0) :
    ((∏ i ∈ s, f i : ℚ≥0) : ℝ≥0∞) = ∏ i ∈ s, (f i : ℝ≥0∞) := by
  simp [nnratCast_def, NNRat.cast_prod, ofNNReal_finsetProd]

@[simp, norm_cast] theorem nnratCast_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ≥0) :
    ((∑ i ∈ s, f i : ℚ≥0) : ℝ≥0∞) = ∑ i ∈ s, (f i : ℝ≥0∞) := by
  simp [nnratCast_def, NNRat.cast_sum, ofNNReal_finsetSum]

/-- **A keep test in `ℚ≥0` is the same test in `ℝ≥0∞`**: a coin `n` below `D` times a product of
two rational weights. -/
theorem natCast_lt_natCast_mul_mul_iff (n D : ℕ) (a b : ℚ≥0) :
    ((n : ℚ≥0) < D * (a * b)) ↔ ((n : ℝ≥0∞) < D * ((a : ℝ≥0∞) * (b : ℝ≥0∞))) := by
  rw [← nnratCast_lt_nnratCast, nnratCast_mul, nnratCast_mul, nnratCast_natCast, nnratCast_natCast]

/-- The extended real of a nonnegative rational's real value is its cast. -/
theorem ofReal_nnratCast (q : ℚ≥0) : ENNReal.ofReal (q : ℝ) = (q : ℝ≥0∞) := by
  rw [nnratCast_def]
  exact (ofReal_coe_nnreal : ENNReal.ofReal ((q : ℝ≥0) : ℝ) = _)

/-- The extended real of a rational's real value is the cast of its nonnegative part. -/
theorem ofReal_ratCast (x : ℚ) : ENNReal.ofReal (x : ℝ) = (x.toNNRat : ℝ≥0∞) := by
  rw [← ofReal_nnratCast]
  by_cases hx : 0 ≤ x
  · congr 1
    exact_mod_cast (congrArg (fun q : ℚ => (q : ℝ)) (Rat.coe_toNNRat x hx)).symm
  · rw [Rat.toNNRat_eq_zero.2 (le_of_not_ge hx), NNRat.cast_zero,
      ofReal_of_nonpos (by exact_mod_cast le_of_not_ge hx), ofReal_zero]

end ENNReal

namespace NNRat

/-- **`min 1 (a / b)` with the convention of `ℝ≥0∞` at `b = 0`**: `1` when `a ≠ 0` and `0` when
`a = 0` (in `ℝ≥0∞`, `a / 0 = ⊤` for `a ≠ 0` and `0 / 0 = 0`). Its cast is `min 1 (a / b)` in
`ℝ≥0∞` for all `a` and `b` (`ENNReal.nnratCast_minOneDiv`). -/
def minOneDiv (a b : ℚ≥0) : ℚ≥0 :=
  if b = 0 then (if a = 0 then 0 else 1) else min 1 (a / b)

theorem minOneDiv_le_one (a b : ℚ≥0) : minOneDiv a b ≤ 1 := by
  unfold minOneDiv
  split_ifs <;> simp

end NNRat

namespace ENNReal

@[simp, norm_cast] theorem nnratCast_minOneDiv (a b : ℚ≥0) :
    ((NNRat.minOneDiv a b : ℚ≥0) : ℝ≥0∞) = min 1 ((a : ℝ≥0∞) / (b : ℝ≥0∞)) := by
  unfold NNRat.minOneDiv
  split_ifs with hb ha
  · simp [ha, hb]
  · rw [hb, nnratCast_zero, ENNReal.div_zero (nnratCast_ne_zero.2 ha), nnratCast_one,
      min_top_right]
  · rw [nnratCast_min, nnratCast_one, nnratCast_div _ hb]

end ENNReal
