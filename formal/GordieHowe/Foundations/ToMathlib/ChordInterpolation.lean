-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-!
# Chord interpolation at equally spaced nodes

The hat functions `nodeHat n m y = max 0 (1 − |n y − m|)` at the nodes `m / n`, `m ≤ n`, are the
piecewise-linear interpolation basis on `[0, 1]`: they are nonnegative (`nodeHat_nonneg`), sum to one
(`sum_nodeHat`) and reproduce `y` (`sum_nodeHat_mul`) on `[0, 1]`. By Jensen's inequality a convex
`g` lies below its chord interpolant (`ConvexOn.le_sum_nodeHat_mul`), in particular
`exp (λ y) ≤ ∑_m nodeHat n m y · exp (λ m / n)` (`exp_le_sum_nodeHat_mul_exp`).
-/

open Finset Real
open scoped BigOperators

namespace GordieHowe

/-- **The hat function at the node `m / n`**: `max 0 (1 − |n y − m|)`, the piecewise-linear
function equal to `1` at `m / n`, to `0` at the other nodes `k / n`, and linear in between. -/
noncomputable def nodeHat (n m : ℕ) (y : ℝ) : ℝ := max 0 (1 - |(n : ℝ) * y - m|)

/-- Every hat function is nonnegative. -/
theorem nodeHat_nonneg (n m : ℕ) (y : ℝ) : 0 ≤ nodeHat n m y := le_max_left _ _

/-- The tent `max 0 (1 − |s|)` is the second difference of `max 0 ·` at `s`. -/
theorem max_zero_one_sub_abs (s : ℝ) :
    max 0 (1 - |s|) = max 0 (s + 1) - 2 * max 0 s + max 0 (s - 1) := by
  rcases le_total 0 s with h | h
  · rw [abs_of_nonneg h]
    simp only [max_def]
    split_ifs <;> linarith
  · rw [abs_of_nonpos h]
    simp only [max_def]
    split_ifs <;> linarith

/-- **The hat as a ramp difference**: `nodeHat n m y = A m − A (m + 1)` with
`A k = max 0 (n y − k + 1) − max 0 (n y − k)`. -/
theorem nodeHat_eq_sub (n m : ℕ) (y : ℝ) :
    nodeHat n m y = (max 0 (n * y - m + 1) - max 0 (n * y - m)) -
      (max 0 (n * y - ((m + 1 : ℕ) : ℝ) + 1) - max 0 (n * y - ((m + 1 : ℕ) : ℝ))) := by
  rw [nodeHat, max_zero_one_sub_abs]
  push_cast
  have e1 : (n : ℝ) * y - (m + 1) + 1 = n * y - m := by ring
  have e2 : (n : ℝ) * y - (m + 1) = n * y - m - 1 := by ring
  rw [e1, e2]
  ring

/-- **Partition of unity**: on `[0, 1]` the hats at the nodes `m / n`, `m ≤ n`, sum to one. -/
theorem sum_nodeHat {n : ℕ} {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∑ m ∈ range (n + 1), nodeHat n m y = 1 := by
  set t : ℝ := n * y
  have ht0 : 0 ≤ t := mul_nonneg (Nat.cast_nonneg n) hy0
  have htn : t ≤ n := by
    have := mul_le_mul_of_nonneg_left hy1 (Nat.cast_nonneg (α := ℝ) n)
    simpa [t] using this
  simp_rw [nodeHat_eq_sub]
  rw [sum_range_sub' (fun k : ℕ => max 0 (t - k + 1) - max 0 (t - k))]
  push_cast
  simp only [max_def]
  split_ifs <;> linarith

/-- **Linear reproduction**: on `[0, 1]`, `∑_m nodeHat n m y · (m / n) = y`. -/
theorem sum_nodeHat_mul {n : ℕ} (hn : 0 < n) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∑ m ∈ range (n + 1), nodeHat n m y * ((m : ℝ) / n) = y := by
  set t : ℝ := n * y
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have ht0 : 0 ≤ t := mul_nonneg (Nat.cast_nonneg n) hy0
  have htn : t ≤ n := by
    have := mul_le_mul_of_nonneg_left hy1 (Nat.cast_nonneg (α := ℝ) n)
    simpa [t] using this
  set A : ℕ → ℝ := fun k => max 0 (t - k + 1) - max 0 (t - k)
  set B : ℕ → ℝ := fun k => max 0 (t - k)
  have hA : ∀ m : ℕ, A (m + 1) = B m - B (m + 1) := fun m => by
    simp only [A, B]
    push_cast
    rw [show t - (m + 1) + 1 = t - m by ring]
  have key : ∀ m : ℕ, nodeHat n m y * (m : ℝ) =
      ((m : ℝ) * A m - ((m + 1 : ℕ) : ℝ) * A (m + 1)) + (B m - B (m + 1)) := fun m => by
    rw [nodeHat_eq_sub, ← hA]
    simp only [A, t]
    push_cast
    ring
  have hsum : ∑ m ∈ range (n + 1), nodeHat n m y * (m : ℝ) = t := by
    simp_rw [key]
    rw [sum_add_distrib, sum_range_sub' (fun m : ℕ => (m : ℝ) * A m),
      sum_range_sub' B]
    simp only [A, B]
    push_cast
    simp only [max_def]
    split_ifs <;> nlinarith
  simp_rw [div_eq_mul_inv, ← mul_assoc]
  rw [← Finset.sum_mul, hsum]
  simp only [t]
  field_simp

/-- **A convex function lies below its chord interpolant**: for `g` convex on `ℝ` and
`y ∈ [0, 1]`, `g y ≤ ∑_{m ≤ n} nodeHat n m y · g (m / n)` (Jensen's inequality). -/
theorem _root_.ConvexOn.le_sum_nodeHat_mul {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) {n : ℕ}
    (hn : 0 < n) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    g y ≤ ∑ m ∈ range (n + 1), nodeHat n m y * g ((m : ℝ) / n) := by
  have h := hg.map_sum_le (t := range (n + 1)) (w := fun m => nodeHat n m y)
    (p := fun m : ℕ => (m : ℝ) / n) (fun m _ => nodeHat_nonneg n m y) (sum_nodeHat hy0 hy1)
    (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at h
  rwa [sum_nodeHat_mul hn hy0 hy1] at h

/-- **The chord bound for `exp`**: for `y ∈ [0, 1]` and every real `λ`,
`exp (λ y) ≤ ∑_{m ≤ n} nodeHat n m y · exp (λ m / n)`. -/
theorem exp_le_sum_nodeHat_mul_exp {n : ℕ} (hn : 0 < n) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (lam : ℝ) :
    exp (lam * y) ≤ ∑ m ∈ range (n + 1), nodeHat n m y * exp (lam * m / n) := by
  have hg : ConvexOn ℝ Set.univ (fun s => exp (lam * s)) := by
    have := convexOn_exp.comp_linearMap (LinearMap.lsmul ℝ ℝ lam)
    simpa [Function.comp_def] using this
  have h := hg.le_sum_nodeHat_mul hn hy0 hy1
  simpa only [mul_div_assoc] using h

end GordieHowe
