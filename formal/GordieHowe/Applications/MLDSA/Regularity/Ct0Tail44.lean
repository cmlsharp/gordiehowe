-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.ChallengeTail

@[expose] public section

/-!
# The ct₀-check at ML-DSA-44

The ct₀-check of FIPS 204 Algorithm 7 line 28 rejects when `‖c·t₀‖∞ ≥ γ₂`. At ML-DSA-44
(FIPS 204 Table 1: `τ = 39`, `γ₂ = (q - 1)/88 = 95232`, `k = 4`; `‖t₀‖∞ ≤ 2^12 = 4096` from
Power2Round with `d = 13`) it can fail, and the bounds below control how often, for `c` uniform on
`B_39`. Write `s_m = ‖t₀,m‖₂² / (256 · 4096²)` for the normalized squared norm of component `m`.

* `one_sub_le_expect_challengeBall_ct0_mldsa44_half`: if `s_m ≤ 1/2` for every component, the
  check passes with probability at least `1 - 3/4000` (the cosh-chord bound at
  `u = 4 log(7/5)`, where the per-coefficient bound is `2 (5/7)^93 (1 + (cosh u - 1)/2)^39`).
* `one_sub_le_expect_challengeBall_ct0_mldsa44_thirtyOneFiftieths`: if `s_m ≤ 31/50` for every
  component, it passes with probability at least `1 - 3/250` (at `u = 4 log(4/3)`).
* `sum_choose_hinge_mldsa44`, `expect_challengeBall_indicator_centeredCoeffs_le_mldsa44`: for every
  `t₀` with `‖t₀‖∞ ≤ 4096`, `Pr_c[|(c·t₀)_x| ≥ γ₂] ≤ 𝔼 max(|S_39| - 21, 0) / (93/4 - 21) =
  8737343/25769803776` per coefficient (the convex comparison with the hinge at `21`, against the
  simple random walk `S_39`).
* `one_sub_le_expect_challengeBall_ct0_mldsa44`: a union over the `1024` coefficients, so the
  check passes with probability at least `1 - 217/625 = 0.6528` for every such `t₀`.

The rates `u = 4 log r` make `e^u = r^4` and `e^{-u γ₂ / 4096} = r^-93` rational
(`exp_neg_four_log_mul_mldsa44`, `cosh_four_log`), so each bound is a rational inequality.
-/

open Finset Real
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA LatticeCrypto TransformOps

/-! ### Numerical facts -/

/-- At the rate `u = 4 log r`, the Chernoff factor of `γ₂ = 95232` with `B = 4096` is
`exp(-u γ₂ / B) = r^-93`. -/
theorem exp_neg_four_log_mul_mldsa44 {r : ℝ} (hr : 0 < r) :
    exp (-(4 * log r * ((95232 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ))) = (r ^ 93)⁻¹ := by
  rw [show 4 * log r * ((95232 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) = ((93 : ℕ) : ℝ) * log r by
    push_cast; ring, ← log_pow, exp_neg, exp_log (by positivity)]

/-- At the rate `u = 4 log r`, `cosh u = (r^4 + r^-4)/2`. -/
theorem cosh_four_log {r : ℝ} (hr : 0 < r) : cosh (4 * log r) = (r ^ 4 + (r ^ 4)⁻¹) / 2 := by
  rw [cosh_eq, exp_neg, show (4 : ℝ) * log r = ((4 : ℕ) : ℝ) * log r by norm_num, ← log_pow,
    exp_log (by positivity)]

/-- The ML-DSA-44 side condition `2τB < q` for `τ = 39`, `B = 4096`. -/
theorem two_mul_tau_mul_le_modulus_mldsa44 : 2 * (39 * 4096) < modulus := by
  norm_num [modulus]

/-- `ringDegree · 4096² = 256 · 4096²` as reals. -/
theorem ringDegree_mul_sq_mldsa44 :
    ((ringDegree : ℕ) : ℝ) * ((4096 : ℕ) : ℝ) ^ 2 = 256 * 4096 ^ 2 := by
  norm_num [ringDegree]

/-- **The hinge moment of the simple random walk with 39 steps**:
`∑_{j ≤ 39} C(39, j) max(|j - (39 - j)| - 21, 0) = 419392464`, so
`𝔼 max(|S_39| - 21, 0) = 419392464 / 2^39`. -/
theorem sum_choose_hinge_mldsa44 :
    ∑ j ∈ range (39 + 1), ((Nat.choose 39 j : ℕ) : ℝ) *
      max (|(j : ℝ) - ((39 - j : ℕ) : ℝ)| - 21) 0 = 419392464 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial,
    abs_of_nonneg, abs_of_nonpos, max_def]

variable [nttOps : NTTRingOps] [NTTRingLaws nttOps]

/-! ### Through the norms of the components -/

/-- **The ct₀-check at ML-DSA-44 for components of normalized norm at most `1/2`**: for `t₀` with
`‖t₀‖∞ ≤ 4096` and `‖t₀,m‖₂² / (256 · 4096²) ≤ 1/2` for every component, the check
`‖c·t₀‖∞ < 95232` passes for at least a `1 - 3/4000` fraction of `c ∈ B_39`
(`one_sub_le_expect_challengeBall_ct0_chord` at `u = 4 log(7/5)`). -/
theorem one_sub_le_expect_challengeBall_ct0_mldsa44_half (t0 : RqVec 4)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hs : ∀ m, ∑ i, (centeredVec t0 m i : ℝ) ^ 2 / (256 * 4096 ^ 2) ≤ 1 / 2) :
    1 - 3 / 4000 ≤
      𝔼 c : ChallengeBall 39,
        (if ∀ x, |centeredCoeffs (c.1 • t0) x| < 95232 then 1 else 0 : ℝ) := by
  have hu : (0 : ℝ) ≤ 4 * log (7 / 5) := by
    have := log_pos (by norm_num : (1 : ℝ) < 7 / 5)
    linarith
  refine le_trans ?_ (one_sub_le_expect_challengeBall_ct0_chord (τ := 39) (B := 4096)
    (by norm_num [ringDegree]) (by norm_num) t0 ht0 two_mul_tau_mul_le_modulus_mldsa44 hu 95232
    fun m => by rw [ringDegree_mul_sq_mldsa44]; exact hs m)
  rw [exp_neg_four_log_mul_mldsa44 (by norm_num), cosh_four_log (by norm_num)]
  norm_num [ringDegree]

/-- **The ct₀-check at ML-DSA-44 for components of normalized norm at most `31/50`**: for `t₀`
with `‖t₀‖∞ ≤ 4096` and `‖t₀,m‖₂² / (256 · 4096²) ≤ 31/50` for every component, the check
`‖c·t₀‖∞ < 95232` passes for at least a `1 - 3/250` fraction of `c ∈ B_39`
(`one_sub_le_expect_challengeBall_ct0_chord` at `u = 4 log(4/3)`). -/
theorem one_sub_le_expect_challengeBall_ct0_mldsa44_thirtyOneFiftieths (t0 : RqVec 4)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hs : ∀ m, ∑ i, (centeredVec t0 m i : ℝ) ^ 2 / (256 * 4096 ^ 2) ≤ 31 / 50) :
    1 - 3 / 250 ≤
      𝔼 c : ChallengeBall 39,
        (if ∀ x, |centeredCoeffs (c.1 • t0) x| < 95232 then 1 else 0 : ℝ) := by
  have hu : (0 : ℝ) ≤ 4 * log (4 / 3) := by
    have := log_pos (by norm_num : (1 : ℝ) < 4 / 3)
    linarith
  refine le_trans ?_ (one_sub_le_expect_challengeBall_ct0_chord (τ := 39) (B := 4096)
    (by norm_num [ringDegree]) (by norm_num) t0 ht0 two_mul_tau_mul_le_modulus_mldsa44 hu 95232
    fun m => by rw [ringDegree_mul_sq_mldsa44]; exact hs m)
  rw [exp_neg_four_log_mul_mldsa44 (by norm_num), cosh_four_log (by norm_num)]
  norm_num [ringDegree]

/-! ### For every `t₀` -/

/-- **The per-coefficient ct₀ tail at ML-DSA-44 for every `t₀`**: for `‖t₀‖∞ ≤ 4096` and every
coefficient `x`, `Pr_{c ∈ B_39}[|(c·t₀)_x| ≥ 95232] ≤ 8737343/25769803776`
(`expect_challengeBall_indicator_centeredCoeffs_le_hinge` at `θ = 21`, `γ₂/B = 93/4`). -/
theorem expect_challengeBall_indicator_centeredCoeffs_le_mldsa44 (t0 : RqVec 4)
    (ht0 : polyVecNorm t0 ≤ 4096) (x : Fin 4 × Fin ringDegree) :
    𝔼 c : ChallengeBall 39,
        (if ((95232 : ℕ) : ℝ) ≤ |(centeredCoeffs (c.1 • t0) x : ℝ)| then 1 else 0 : ℝ) ≤
      8737343 / 25769803776 := by
  refine (expect_challengeBall_indicator_centeredCoeffs_le_hinge (τ := 39) (B := 4096)
    (by norm_num [ringDegree]) (by norm_num) t0 ht0 two_mul_tau_mul_le_modulus_mldsa44 x
    (θ := 21) (by norm_num)).trans_eq ?_
  rw [sum_choose_hinge_mldsa44]
  norm_num

/-- **The ct₀-check at ML-DSA-44 for every `t₀`**: for `‖t₀‖∞ ≤ 4096`, the check
`‖c·t₀‖∞ < 95232` passes for at least a `1 - 217/625 = 0.6528` fraction of `c ∈ B_39` (a union
over the `1024` coefficients of `expect_challengeBall_indicator_centeredCoeffs_le_mldsa44`). -/
theorem one_sub_le_expect_challengeBall_ct0_mldsa44 (t0 : RqVec 4)
    (ht0 : polyVecNorm t0 ≤ 4096) :
    1 - 217 / 625 ≤
      𝔼 c : ChallengeBall 39,
        (if ∀ x, |centeredCoeffs (c.1 • t0) x| < 95232 then 1 else 0 : ℝ) := by
  refine le_trans ?_ (one_sub_le_expect_challengeBall_ct0 t0 95232
    (expect_challengeBall_indicator_centeredCoeffs_le_mldsa44 t0 ht0) (by norm_num [ringDegree]))
  norm_num [ringDegree]

end GordieHowe.MLDSA.Regularity
