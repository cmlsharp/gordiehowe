-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Weighted averages and square roots

Two inequalities for a finite weighted sum `∑ ω, w ω * f ω` with nonnegative weights:

- `Real.sum_mul_sqrt_le_sqrt_sum_mul` (Jensen's inequality for the square root): for weights
  summing to `1`, `∑ ω, w ω * √(g ω) ≤ √(∑ ω, w ω * g ω)`;
- `Real.abs_sqrt_sum_mul_sub_sqrt_sum_mul_le` (the reverse triangle inequality in the weighted
  `L²` norm): `|√(∑ ω, w ω * p ω) - √(∑ ω, w ω * q ω)| ≤ √(∑ ω, w ω * (√(p ω) - √(q ω)) ^ 2)`.

Both are about Mathlib objects only and are candidates for upstreaming. They average the
pure-state bounds of `GordieHowe/Model/Quantum/O2H/Basic.lean` over a probability distribution.
-/

open Finset
open scoped BigOperators

namespace Real

variable {Ω : Type*} [Fintype Ω]

/-- Jensen's inequality for the square root under weights summing to `1`, by Cauchy–Schwarz. -/
theorem sum_mul_sqrt_le_sqrt_sum_mul {w g : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (hg : ∀ ω, 0 ≤ g ω) : ∑ ω, w ω * √(g ω) ≤ √(∑ ω, w ω * g ω) := by
  have h := sum_sqrt_mul_sqrt_le univ hw fun ω => mul_nonneg (hw ω) (hg ω)
  rw [hw1, sqrt_one, one_mul] at h
  refine le_of_eq_of_le (sum_congr rfl fun ω _ => ?_) h
  rw [sqrt_mul (hw ω), ← mul_assoc, mul_self_sqrt (hw ω)]

/-- The reverse triangle inequality in the weighted `L²` norm, applied to `√p` and `√q`. -/
theorem abs_sqrt_sum_mul_sub_sqrt_sum_mul_le {w p q : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω) :
    |√(∑ ω, w ω * p ω) - √(∑ ω, w ω * q ω)| ≤ √(∑ ω, w ω * (√(p ω) - √(q ω)) ^ 2) := by
  let vec : (Ω → ℝ) → EuclideanSpace ℝ Ω := fun f => WithLp.toLp 2 fun ω => √(w ω) * f ω
  have hnorm : ∀ f, ‖vec f‖ = √(∑ ω, w ω * f ω ^ 2) := fun f => by
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine sum_congr rfl fun ω _ => ?_
    simp [vec, mul_pow, sq_sqrt (hw ω)]
  have hsq : ∀ (f : Ω → ℝ), (∀ ω, 0 ≤ f ω) → ∑ ω, w ω * √(f ω) ^ 2 = ∑ ω, w ω * f ω :=
    fun f hf => sum_congr rfl fun ω _ => by rw [sq_sqrt (hf ω)]
  have hsub : vec (fun ω => √(p ω)) - vec (fun ω => √(q ω)) = vec fun ω => √(p ω) - √(q ω) := by
    ext ω
    simp [vec, mul_sub]
  have h := abs_norm_sub_norm_le (vec fun ω => √(p ω)) (vec fun ω => √(q ω))
  rwa [hsub, hnorm, hnorm, hnorm, hsq p hp, hsq q hq] at h

end Real
