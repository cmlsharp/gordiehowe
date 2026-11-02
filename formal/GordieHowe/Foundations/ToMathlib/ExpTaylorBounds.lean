-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Rational bounds on `exp` for numerical certificates

Checkable forms of Mathlib's Taylor bound `Real.exp_bound`
(`|exp x - ∑_{i < n} xⁱ / i!| ≤ |x|ⁿ (n + 1) / (n! n)` for `|x| ≤ 1`), for proving
`exp x ≤ r` and `r ≤ exp x` at rational `x` and `r` by `norm_num`:

* `Real.exp_le_of_taylor_le`, `Real.le_exp_of_le_taylor`: the Taylor bound at `|x| ≤ 1`;
* `Real.exp_le_pow_of_exp_div_le`, `Real.pow_le_exp_of_le_exp_div`: `exp x = exp (x / m)^m`, for
  arguments of absolute value above `1`;
* `Real.exp_le_two_pow_of_le`, `Real.exp_le_inv_two_pow_of_le`: `exp x ≤ 2^m` and
  `exp x ≤ 2^-m` from `log 2 ∈ (0.6931471803, 0.6931471808)` (`Real.log_two_gt_d9`,
  `Real.log_two_lt_d9`), for large arguments;
* `Real.exp_le_inv_two_pow_mul_of_exp_add_le`: `exp x ≤ 2^-m · r` from a bound on
  `exp(x + 0.6931471808 m)`, for large negative arguments at full relative precision.

The statements are about Mathlib objects only and are candidates for upstreaming.
-/

open Finset
open scoped Nat

namespace Real

/-- **An upper bound on `exp` from its Taylor polynomial** at `|x| ≤ 1`: if the degree-`n - 1`
Taylor sum plus the remainder bound `|x|ⁿ (n + 1) / (n! n)` of `Real.exp_bound` is at most `r`,
then `exp x ≤ r`. -/
theorem exp_le_of_taylor_le {x r : ℝ} (n : ℕ) (hn : 0 < n) (hx : |x| ≤ 1)
    (h : ∑ i ∈ range n, x ^ i / i.factorial + |x| ^ n * (n.succ / (n.factorial * n)) ≤ r) :
    exp x ≤ r := by
  have hb := exp_bound hx hn
  have := le_abs_self (exp x - ∑ i ∈ range n, x ^ i / i.factorial)
  linarith

/-- **A lower bound on `exp` from its Taylor polynomial** at `|x| ≤ 1`: if `r` is at most the
degree-`n - 1` Taylor sum minus the remainder bound of `Real.exp_bound`, then `r ≤ exp x`. -/
theorem le_exp_of_le_taylor {x r : ℝ} (n : ℕ) (hn : 0 < n) (hx : |x| ≤ 1)
    (h : r ≤ ∑ i ∈ range n, x ^ i / i.factorial - |x| ^ n * (n.succ / (n.factorial * n))) :
    r ≤ exp x := by
  have hb := exp_bound hx hn
  have := neg_abs_le (exp x - ∑ i ∈ range n, x ^ i / i.factorial)
  linarith

/-- `exp x ≤ r^m` from `exp (x / m) ≤ r`, for `m > 0`. -/
theorem exp_le_pow_of_exp_div_le {x r : ℝ} {m : ℕ} (hm : 0 < m) (h : exp (x / m) ≤ r) :
    exp x ≤ r ^ m := by
  have hx : exp x = exp (x / m) ^ m := by
    rw [← exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hm.ne')]
  rw [hx]
  exact pow_le_pow_left₀ (exp_pos _).le h m

/-- `r^m ≤ exp x` from `0 ≤ r ≤ exp (x / m)`, for `m > 0`. -/
theorem pow_le_exp_of_le_exp_div {x r : ℝ} {m : ℕ} (hm : 0 < m) (hr : 0 ≤ r)
    (h : r ≤ exp (x / m)) : r ^ m ≤ exp x := by
  have hx : exp x = exp (x / m) ^ m := by
    rw [← exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hm.ne')]
  rw [hx]
  exact pow_le_pow_left₀ hr h m

/-- **`exp x ≤ 2^m`** when `x ≤ 0.6931471803 m` (`Real.log_two_gt_d9`). -/
theorem exp_le_two_pow_of_le {x : ℝ} {m : ℕ} (h : x ≤ m * (6931471803 / 10 ^ 10)) :
    exp x ≤ 2 ^ m := by
  have hl := log_two_gt_d9
  norm_num at hl
  have h2 : (2 : ℝ) ^ m = exp (m * log 2) := by
    rw [exp_nat_mul, exp_log (by norm_num)]
  rw [h2]
  refine exp_le_exp.2 (h.trans ?_)
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

/-- **`exp x ≤ 2^-m`** when `x ≤ -0.6931471808 m` (`Real.log_two_lt_d9`). -/
theorem exp_le_inv_two_pow_of_le {x : ℝ} {m : ℕ} (h : x ≤ -(m * (6931471808 / 10 ^ 10))) :
    exp x ≤ 2⁻¹ ^ m := by
  have hl := log_two_lt_d9
  norm_num at hl
  have h2 : (2⁻¹ : ℝ) ^ m = exp (-(m * log 2)) := by
    rw [exp_neg, exp_nat_mul, exp_log (by norm_num), inv_pow]
  rw [h2]
  refine exp_le_exp.2 (h.trans ?_)
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

/-- **`exp x ≤ 2^-m · r`** when `exp(x + 0.6931471808 m) ≤ r` (`Real.log_two_lt_d9`): the
argument is shifted by `m log 2 ≤ 0.6931471808 m` into the range of the Taylor bound. -/
theorem exp_le_inv_two_pow_mul_of_exp_add_le {x r : ℝ} (m : ℕ)
    (h : exp (x + m * (6931471808 / 10 ^ 10)) ≤ r) : exp x ≤ 2⁻¹ ^ m * r := by
  have hl := log_two_lt_d9
  norm_num at hl
  have h2 : (2⁻¹ : ℝ) ^ m = exp (-(m * log 2)) := by
    rw [exp_neg, exp_nat_mul, exp_log (by norm_num), inv_pow]
  have hx : exp x = 2⁻¹ ^ m * exp (x + m * log 2) := by
    rw [h2, ← exp_add]
    ring_nf
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [hx]
  refine mul_le_mul_of_nonneg_left ((exp_le_exp.2 ?_).trans h) (by positivity)
  nlinarith

end Real
