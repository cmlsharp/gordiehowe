-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Chebyshev
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

The uniform-average forms, from Cauchy–Schwarz (`Finset.expect_mul_sq_le_sq_mul_sq`,
`sq_sum_le_card_mul_sum_sq`):

- `Real.expect_mul_le_sqrt_mul_sqrt`: `𝔼 f g ≤ √(𝔼 f²) · √(𝔼 g²)`;
- `Finset.sq_expect_le_expect_sq` (Jensen's inequality for the square): `(𝔼 f)² ≤ 𝔼 f²`;
- `Finset.sum_le_card_mul_of_sum_sq_le`: `∑_{i ∈ s} f i ≤ #s · C` from `∑_{i ∈ s} f i² ≤ #s · C²`;
- `Finset.expect_sq_sum_expect_le`: `𝔼_a (∑_b 𝔼_c E a b c)² ≤ C` from
  `∑_a (∑_b E a b c)² ≤ |α| · C` for every `c`.
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

/-- **Cauchy–Schwarz for uniform averages**: `𝔼 f g ≤ √(𝔼 f²) · √(𝔼 g²)`. -/
theorem expect_mul_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    𝔼 i ∈ s, f i * g i ≤ √(𝔼 i ∈ s, f i ^ 2) * √(𝔼 i ∈ s, g i ^ 2) :=
  (le_sqrt_of_sq_le (expect_mul_sq_le_sq_mul_sq s f g)).trans_eq
    (sqrt_mul (expect_nonneg fun _ _ => sq_nonneg _) _)

end Real

namespace Finset

/-- **Jensen's inequality for the square** under a uniform average: `(𝔼 f)² ≤ 𝔼 f²`. -/
theorem sq_expect_le_expect_sq {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    (𝔼 i ∈ s, f i) ^ 2 ≤ 𝔼 i ∈ s, f i ^ 2 := by
  have h := expect_mul_sq_le_sq_mul_sq s f fun _ => 1
  simpa only [mul_one, one_pow, expect_const hs] using h

/-- An `ℓ²` bound gives the `ℓ¹` bound: `∑_{i ∈ s} f i ≤ #s · C` when
`∑_{i ∈ s} f i² ≤ #s · C²` and `C ≥ 0`. -/
theorem sum_le_card_mul_of_sum_sq_le {ι : Type*} {s : Finset ι} {f : ι → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∑ i ∈ s, f i ^ 2 ≤ #s * C ^ 2) : ∑ i ∈ s, f i ≤ #s * C := by
  have h1 : (∑ i ∈ s, f i) ^ 2 ≤ (#s * C) ^ 2 :=
    (sq_sum_le_card_mul_sum_sq (s := s) (f := f)).trans <| by
      rw [mul_pow, sq (#s : ℝ), mul_assoc]
      exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
  exact (abs_le_of_sq_le_sq' h1 (mul_nonneg (Nat.cast_nonneg _) hC)).2

/-- **The mean square of an averaged sum**: if `∑_a (∑_b E a b c)² ≤ |α| · C` for every `c`, then
`𝔼_a (∑_b 𝔼_c E a b c)² ≤ C` (Jensen's inequality over `c`). -/
theorem expect_sq_sum_expect_le {α β γ : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [Fintype γ] [Nonempty γ] (E : α → β → γ → ℝ) {C : ℝ}
    (h : ∀ c, ∑ a, (∑ b, E a b c) ^ 2 ≤ Fintype.card α * C) :
    𝔼 a, (∑ b, 𝔼 c, E a b c) ^ 2 ≤ C := by
  have hα : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  calc 𝔼 a, (∑ b, 𝔼 c, E a b c) ^ 2 = 𝔼 a, (𝔼 c, ∑ b, E a b c) ^ 2 := by
        simp_rw [expect_sum_comm]
    _ ≤ 𝔼 a, 𝔼 c, (∑ b, E a b c) ^ 2 :=
        expect_le_expect fun a _ => sq_expect_le_expect_sq univ_nonempty _
    _ = 𝔼 c, 𝔼 a, (∑ b, E a b c) ^ 2 := expect_comm _ _ _
    _ ≤ 𝔼 _c : γ, C := expect_le_expect fun c _ => by
        rw [expect_eq_sum_div_card, card_univ, div_le_iff₀ hα, mul_comm]
        exact h c
    _ = C := expect_const univ_nonempty C

end Finset
