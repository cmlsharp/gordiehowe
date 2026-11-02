-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# A quadratic lower bound on `log (1 - x)` on an interval `[0, x₀]`

For `0 ≤ x ≤ x₀ < 1` and every `n`,

    -log (1 - x) - x ≤ κₙ(x₀) · x²,   κₙ(x₀) = ∑_{i < n} x₀ⁱ / (i + 2) + x₀ⁿ / (1 - x₀)

(`Real.neg_log_one_sub_sub_le`), from the Taylor series of `log (1 - x)` truncated at order `n + 1`
with its geometric remainder (`Real.abs_log_sub_add_sum_range_le`). As `n → ∞`, `κₙ(x₀)` decreases
to the chord coefficient `(-log (1 - x₀) - x₀) / x₀²`; at `n = 0` it is `1 / (1 - x₀)`. In
exponential form, `exp (-x - κ x²) ≤ 1 - x` for every `κ ≥ κₙ(x₀)`
(`Real.exp_neg_sub_mul_sq_le_one_sub`).

The statements are about Mathlib objects only and are candidates for upstreaming.
-/

open Finset

namespace Real

/-- **The quadratic coefficient of `-log (1 - x) - x` on `[0, x₀]`** at truncation order `n`:
`κₙ(x₀) = ∑_{i < n} x₀ⁱ / (i + 2) + x₀ⁿ / (1 - x₀)`. -/
noncomputable def logOneSubCoeff (n : ℕ) (x₀ : ℝ) : ℝ :=
  ∑ i ∈ range n, x₀ ^ i / ((i : ℝ) + 2) + x₀ ^ n / (1 - x₀)

/-- **`-log (1 - x) - x ≤ κₙ(x₀) x²`** for `0 ≤ x ≤ x₀ < 1` and every truncation order `n`. -/
theorem neg_log_one_sub_sub_le {x x₀ : ℝ} (n : ℕ) (hx : 0 ≤ x) (hxx : x ≤ x₀) (hx₀ : x₀ < 1) :
    -log (1 - x) - x ≤ logOneSubCoeff n x₀ * x ^ 2 := by
  have hx1 : x < 1 := hxx.trans_lt hx₀
  have habs : |x| < 1 := by rw [abs_of_nonneg hx]; exact hx1
  have h := Real.abs_log_sub_add_sum_range_le habs (n + 1)
  rw [abs_of_nonneg hx, Finset.sum_range_succ'] at h
  have hlog := (abs_le.1 h).1
  have hterm : ∀ i ∈ range n, x ^ (i + 1 + 1) / (((i + 1 : ℕ) : ℝ) + 1) ≤
      x ^ 2 * (x₀ ^ i / ((i : ℝ) + 2)) := fun i _ => by
    have hp : x ^ i ≤ x₀ ^ i := pow_le_pow_left₀ hx hxx i
    have hd : (((i + 1 : ℕ) : ℝ) + 1) = (i : ℝ) + 2 := by push_cast; ring
    rw [hd, mul_div_assoc', show x ^ (i + 1 + 1) = x ^ 2 * x ^ i by ring]
    gcongr
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hrem : x ^ (n + 1 + 1) / (1 - x) ≤ x ^ 2 * (x₀ ^ n / (1 - x₀)) := by
    have hp : x ^ n ≤ x₀ ^ n := pow_le_pow_left₀ hx hxx n
    rw [mul_div_assoc', show x ^ (n + 1 + 1) = x ^ 2 * x ^ n by ring]
    have h1 : 0 < 1 - x₀ := by linarith
    have hx₀0 : 0 ≤ x₀ := hx.trans hxx
    calc x ^ 2 * x ^ n / (1 - x) ≤ x ^ 2 * x₀ ^ n / (1 - x) := by gcongr
      _ ≤ x ^ 2 * x₀ ^ n / (1 - x₀) := by gcongr
  simp only [Nat.cast_zero, zero_add, pow_one, div_one] at hlog
  rw [logOneSubCoeff, add_mul]
  nlinarith

/-- **`exp (-x - κ x²) ≤ 1 - x`** for `0 ≤ x ≤ x₀ < 1` and every `κ ≥ κₙ(x₀)`. -/
theorem exp_neg_sub_mul_sq_le_one_sub {x x₀ κ : ℝ} (n : ℕ) (hκ : logOneSubCoeff n x₀ ≤ κ)
    (hx : 0 ≤ x) (hxx : x ≤ x₀) (hx₀ : x₀ < 1) :
    exp (-x - κ * x ^ 2) ≤ 1 - x := by
  have hx1 : 0 < 1 - x := by linarith
  have h := neg_log_one_sub_sub_le n hx hxx hx₀
  have hκx : logOneSubCoeff n x₀ * x ^ 2 ≤ κ * x ^ 2 := by gcongr
  calc exp (-x - κ * x ^ 2) ≤ exp (log (1 - x)) := exp_le_exp.2 (by linarith)
    _ = 1 - x := exp_log hx1

end Real
