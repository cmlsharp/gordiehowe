-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.WeightLowerBound
public import GordieHowe.Applications.MLDSA.Regularity.T0Law
public import GordieHowe.Applications.MLDSA.Signing.ChallengeAbsMoment
public import GordieHowe.Foundations.ToMathlib.ExpTaylorBounds

@[expose] public section

/-!
# The inverse square of the acceptance floor, averaged over keys and matrices

The regularity gap divides by the mean member weight, and Cauchy–Schwarz over the matrix leaves
`√(𝔼 w⁻²)` for a lower bound `w` on it (`expect_ringRegGap_le_sqrt`). This file bounds that
average at ML-DSA-65 and ML-DSA-87 with `w` the acceptance floor under a random-oracle
`SampleInBall` (`oracleAcceptFloor`), averaged over the oracle, uniform box secrets and a uniform
matrix.

**The bound as a function of `S = ‖t₀‖₂²`.** For `c` uniform on `B_τ`, the hint mean
`𝔼_c hintBoundSum(c, t₀)` is at most `hintMeanBound p S = 256 k · 2^12 · h(τ S / (256 k 2^24)) / L`
with `h = absMomentBound` (`expect_hintBoundSum_le_hintMeanBound`, from
`sum_expect_challengeBall_abs_centeredCoeffs_le`), and the hint second moment is at most
`hintSqMeanBound p S = τ S / L²` (`expect_hintBoundSqSum_le`), `L = 2(γ₂ - β) - 1`. So the oracle
average `𝔼_G (oracleAcceptFloor)⁻²` is at most `floorInvSqBound p κ S =
acceptFloor(hintMeanBound + 2^-64, hintSqMeanBound + 2^-64)⁻² + 2^-1000`
(`expect_inv_sq_oracleAcceptFloor_le_floorInvSqBound_mldsa65`, `_mldsa87`, from
`expect_inv_sq_oracleAcceptFloor_le_mldsa65`), a monotone function of `S`
(`monotone_floorInvSqBound`).

**The layered tail.** `expect_expect_le_layers_chord` bounds `𝔼_{s, Â} floorInvSqBound(S)` on a
grid `a_0 < … < a_7 = 256 k 2^24` with rates `λ'_i` by `U_0 + ∑_{i < 7} (U_{i+1} - U_i) · t_i`,
where `U_i ≥ floorInvSqBound(a_i)` and `t_i ≥ t0TailBound p λ'_i a_i` are rationals:

* `U_i` from the Markov branch of `acceptFloor` with a Taylor lower bound on the exponential term
  of `h` (`floorInvSqBound_le_of_markov`), or from the exponential branch as a power of two
  (`floorInvSqBound_le_two_pow`);
* `t_i` from Taylor bounds on `exp(λ'_i/8)` and on `exp r_i ≥ t0ChordPoly(E_hi)`
  (`t0TailBound_le_exp`), then a Taylor bound (first layer) or a power of two
  (`Real.exp_le_inv_two_pow_of_le`).

The first grid point is `1.05` times the mean of `S` for a uniform `t`; the last layers start
just below and above the point where the Markov branch of the floor vanishes.

**Results.** `𝔼_{s, Â} floorInvSqBound(S) ≤ (9/2)²` at ML-DSA-65
(`expect_expect_floorInvSqBound_le_mldsa65`; the rational right side is `19.88`) and
`≤ (33/5)²` at ML-DSA-87 (`expect_expect_floorInvSqBound_le_mldsa87`; `42.72`): the weight
costs `log₂(9/2) = 2.17` and `log₂(33/5) = 2.72` bits of the regularity gap.
-/

open Finset Real
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA

/-! ### The floor as a function of `‖t₀‖₂²` -/

section Floor

variable (p : Params)

/-- **The hint mean bound at `‖t₀‖₂² = S`**: `256 k · 2^12 · h(τ S / (256 k · 2^24)) / L` with
`h = absMomentBound` and `L = 2(γ₂ - β) - 1`, the bound of
`sum_expect_challengeBall_abs_centeredCoeffs_le` over `L`. -/
noncomputable def hintMeanBound (S : ℝ) : ℝ :=
  (ringDegree * p.k : ℕ) * (4096 : ℕ) *
      absMomentBound (p.tau * S / ((ringDegree * p.k : ℕ) * ((4096 : ℕ) : ℝ) ^ 2)) /
    ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ)

/-- **The hint second-moment bound at `‖t₀‖₂² = S`**: `τ S / L²` (`expect_hintBoundSqSum_le`). -/
noncomputable def hintSqMeanBound (S : ℝ) : ℝ :=
  p.tau * S / ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) ^ 2

/-- **The bound on the oracle average of the inverse square floor at `‖t₀‖₂² = S`**:
`acceptFloor(hintMeanBound + 2^-64, hintSqMeanBound + 2^-64)⁻² + 2^-1000`, the right side of
`expect_inv_sq_oracleAcceptFloor_le_mldsa65`. -/
noncomputable def floorInvSqBound (κ S : ℝ) : ℝ :=
  (acceptFloor p.omega κ (hintMeanBound p S + 2⁻¹ ^ 64) (hintSqMeanBound p S + 2⁻¹ ^ 64))⁻¹ ^ 2 +
    2⁻¹ ^ 1000

/-- The hint mean bound is monotone (`monotone_absMomentBound`). -/
theorem monotone_hintMeanBound : Monotone (hintMeanBound p) := fun S S' h => by
  unfold hintMeanBound
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (monotone_absMomentBound ?_)
    (by positivity)) (Nat.cast_nonneg _)
  gcongr

/-- The hint second-moment bound is monotone. -/
theorem monotone_hintSqMeanBound : Monotone (hintSqMeanBound p) := fun S S' h => by
  unfold hintSqMeanBound
  gcongr

/-- **The bound is monotone in `‖t₀‖₂²`** for `κ ≥ 0`: the floor is antitone in the hint
moments (`acceptFloor_anti`). -/
theorem monotone_floorInvSqBound {κ : ℝ} (hκ : 0 ≤ κ) : Monotone (floorInvSqBound p κ) :=
  fun S S' h => by
    unfold floorInvSqBound
    have h1 : hintMeanBound p S + 2⁻¹ ^ 64 ≤ hintMeanBound p S' + 2⁻¹ ^ 64 := by
      linarith [monotone_hintMeanBound p h]
    have h2 : hintSqMeanBound p S + 2⁻¹ ^ 64 ≤ hintSqMeanBound p S' + 2⁻¹ ^ 64 := by
      linarith [monotone_hintSqMeanBound p h]
    have hA := acceptFloor_anti p.omega hκ h1 h2
    have h0 := acceptFloor_pos p.omega κ (hintMeanBound p S' + 2⁻¹ ^ 64)
      (hintSqMeanBound p S' + 2⁻¹ ^ 64)
    have := pow_le_pow_left₀ (inv_nonneg.2 (acceptFloor_pos _ _ _ _).le) (inv_anti₀ h0 hA) 2
    exact add_le_add this le_rfl

/-- **The bound from the Markov branch**: if `elo ≤ exp(-κ_h u)` for the exponential term of
`h` at `u = τ S / (256 k 2^24)`, the hint mean bound with `elo` in place of that term, plus
`2^-64`, is at most `ŷ`, and `1 - ŷ/(ω + 1) > 0`, then
`floorInvSqBound ≤ (1 - ŷ/(ω + 1))⁻² + 2^-64`. -/
theorem floorInvSqBound_le_of_markov {κ S elo ŷ U : ℝ}
    (helo : elo ≤ exp (-(11 / 20 * (65 / 100) ^ 2 *
      (p.tau * S / ((ringDegree * p.k : ℕ) * ((4096 : ℕ) : ℝ) ^ 2)))))
    (hy : (ringDegree * p.k : ℕ) * (4096 : ℕ) * (183 / 100 + 104 / 1000 *
        (p.tau * S / ((ringDegree * p.k : ℕ) * ((4096 : ℕ) : ℝ) ^ 2)) - 77 / 100 * elo) /
        ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) + 2⁻¹ ^ 64 ≤ ŷ)
    (hpos : 0 < 1 - ŷ / (p.omega + 1)) (hU : (1 - ŷ / (p.omega + 1))⁻¹ ^ 2 + 2⁻¹ ^ 64 ≤ U) :
    floorInvSqBound p κ S ≤ U := by
  have hm : hintMeanBound p S + 2⁻¹ ^ 64 ≤ ŷ := by
    refine le_trans ?_ hy
    unfold hintMeanBound absMomentBound
    gcongr
  have hfl : 1 - ŷ / (p.omega + 1) ≤
      acceptFloor p.omega κ (hintMeanBound p S + 2⁻¹ ^ 64) (hintSqMeanBound p S + 2⁻¹ ^ 64) :=
    le_trans (by gcongr) (le_max_left _ _)
  have := pow_le_pow_left₀ (inv_nonneg.2 (acceptFloor_pos _ _ _ _).le) (inv_anti₀ hpos hfl) 2
  have h64 : (2⁻¹ : ℝ) ^ 1000 ≤ 2⁻¹ ^ 64 := pow_le_pow_of_le_one (by norm_num) (by norm_num)
    (by norm_num)
  unfold floorInvSqBound
  exact (add_le_add this h64).trans hU

/-- **The bound from the exponential branch**: if the hint mean bound without its exponential
term plus `2^-64`, plus `κ` times the second-moment bound plus `2^-64`, is at most `z`, and
`2z ≤ 0.6931471803 m`, then `floorInvSqBound ≤ 2^(m+1)`. -/
theorem floorInvSqBound_le_two_pow {κ S z : ℝ} {m : ℕ}
    (hz : (ringDegree * p.k : ℕ) * (4096 : ℕ) * (183 / 100 + 104 / 1000 *
        (p.tau * S / ((ringDegree * p.k : ℕ) * ((4096 : ℕ) : ℝ) ^ 2))) /
        ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) + 2⁻¹ ^ 64 +
      κ * (p.tau * S / ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) ^ 2 + 2⁻¹ ^ 64) ≤ z)
    (hm : 2 * z ≤ m * (6931471803 / 10 ^ 10)) :
    floorInvSqBound p κ S ≤ 2 ^ (m + 1) := by
  have hy : hintMeanBound p S + 2⁻¹ ^ 64 + κ * (hintSqMeanBound p S + 2⁻¹ ^ 64) ≤ z := by
    refine le_trans ?_ hz
    unfold hintMeanBound absMomentBound hintSqMeanBound
    gcongr
    have := exp_pos (-(11 / 20 * (65 / 100) ^ 2 *
      (p.tau * S / ((ringDegree * p.k : ℕ) * ((4096 : ℕ) : ℝ) ^ 2))))
    linarith
  have hfl : exp (-z) ≤
      acceptFloor p.omega κ (hintMeanBound p S + 2⁻¹ ^ 64) (hintSqMeanBound p S + 2⁻¹ ^ 64) :=
    le_trans (exp_le_exp.2 (by linarith)) (exp_le_acceptFloor _ _ _ _)
  have h1 := pow_le_pow_left₀ (inv_nonneg.2 (acceptFloor_pos _ _ _ _).le)
    (inv_anti₀ (exp_pos _) hfl) 2
  have h2 : (exp (-z))⁻¹ ^ 2 = exp (2 * z) := by
    rw [← exp_neg, neg_neg, ← exp_nat_mul]
    norm_num
  have h3 := exp_le_two_pow_of_le hm
  have h4 : (2⁻¹ : ℝ) ^ 1000 ≤ 2 ^ m :=
    (pow_le_one₀ (by norm_num) (by norm_num)).trans (one_le_pow₀ (by norm_num))
  unfold floorInvSqBound
  calc _ ≤ exp (2 * z) + 2 ^ m := add_le_add (h1.trans_eq h2) h4
    _ ≤ 2 ^ m + 2 ^ m := add_le_add h3 le_rfl
    _ = 2 ^ (m + 1) := by ring

/-- **A layer term with a power-of-two level**: `(2^a - U) · 2^-b ≤ 2^-c` for `U ≥ 0` and
`c + a ≤ b`. -/
theorem two_pow_sub_mul_inv_two_pow_le {U : ℝ} {a b c : ℕ} (hU : 0 ≤ U) (hc : c + a ≤ b) :
    (2 ^ a - U) * 2⁻¹ ^ b ≤ 2⁻¹ ^ c := by
  have h1 : (2 ^ a - U) * (2⁻¹ : ℝ) ^ b ≤ 2 ^ a * 2⁻¹ ^ b :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h2 : (2 : ℝ) ^ a * 2⁻¹ ^ b = 2⁻¹ ^ (b - a) := by
    rw [show b = (b - a) + a by omega, pow_add, Nat.add_sub_cancel, ← mul_assoc, mul_comm,
      ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow, one_mul]
  exact (h1.trans_eq h2).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))

/-- Under the acceptance floor parameters, `2τ 2^12 < q`. -/
theorem FloorParams.two_mul_tau_mul_lt_modulus {q : Params} {x₀ κ : ℝ}
    (hf : FloorParams q x₀ κ) :
    2 * (q.tau * 4096) < modulus := by
  have := hf.ct0
  have := hf.gamma2_lt
  omega

variable [nttOps : NTTRingOps] [NTTRingLaws nttOps] {p}

/-- **The hint mean over `B_τ` from `‖t₀‖₂²`**: for `τ ≤ 256`, `k > 0` and `2τ 2^12 < q`,
`𝔼_c hintBoundSum(c, t₀) ≤ hintMeanBound p ‖t₀‖₂²`
(`expect_hintBoundSum_le_expect_abs`, `sum_expect_challengeBall_abs_centeredCoeffs_le`). The ct₀
check need not pass. -/
theorem expect_hintBoundSum_le_hintMeanBound (hτ : p.tau ≤ ringDegree) (hk : 0 < p.k)
    (hq : 2 * (p.tau * 4096) < modulus) (t0 : RqVec p.k) (ht0 : polyVecNorm t0 ≤ 4096) :
    𝔼 c : ChallengeBall p.tau, hintBoundSum p.gamma2 p.beta c.1 t0 ≤
      hintMeanBound p (t0SqNorm t0) := by
  refine (expect_hintBoundSum_le_expect_abs p.gamma2 p.beta
    (fun c : ChallengeBall p.tau => c.1) t0).trans ?_
  rw [Finset.expect_sum_comm]
  exact div_le_div_of_nonneg_right (sum_expect_challengeBall_abs_centeredCoeffs_le hτ
    hk (B := 4096) (by norm_num) t0 ht0 hq le_rfl) (Nat.cast_nonneg _)

/-- **The hint second moment over `B_τ` from `‖t₀‖₂²`**:
`𝔼_c hintBoundSqSum(c, t₀) ≤ hintSqMeanBound p ‖t₀‖₂²` (`expect_hintBoundSqSum_le`). -/
theorem expect_hintBoundSqSum_le_hintSqMeanBound {x₀ κ : ℝ} (hf : FloorParams p x₀ κ)
    (t0 : RqVec p.k) (ht0 : polyVecNorm t0 ≤ 4096) :
    𝔼 c : ChallengeBall p.tau, hintBoundSqSum p.gamma2 p.beta c.1 t0 ≤
      hintSqMeanBound p (t0SqNorm t0) :=
  expect_hintBoundSqSum_le hf.tau_le t0 ht0 hf.two_mul_tau_mul_lt_modulus

end Floor

attribute [local instance] concreteNTTRingOps

/-- **The oracle average of the inverse square floor at ML-DSA-65** as a function of `‖t₀‖₂²`:
`𝔼_G (oracleAcceptFloor)⁻² ≤ floorInvSqBound mldsa65 κ ‖t₀‖₂²` with `κ = 341/500`, for
`‖t₀‖∞ ≤ 2^12`. -/
theorem expect_inv_sq_oracleAcceptFloor_le_floorInvSqBound_mldsa65 (t0 : RqVec mldsa65.k)
    (ht0 : polyVecNorm t0 ≤ 4096) :
    𝔼 G : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
        (oracleAcceptFloor mldsa65 (341 / 500) G t0)⁻¹ ^ 2 ≤
      floorInvSqBound mldsa65 (341 / 500) (t0SqNorm t0) := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_oracleAcceptFloor_le_mldsa65 t0 ht0
    (expect_hintBoundSum_le_hintMeanBound floorParams_mldsa65.tau_le floorParams_mldsa65.k_pos
      floorParams_mldsa65.two_mul_tau_mul_lt_modulus t0 ht0)
    (expect_hintBoundSqSum_le_hintSqMeanBound floorParams_mldsa65 t0 ht0)

/-- **The oracle average of the inverse square floor at ML-DSA-87** as a function of `‖t₀‖₂²`:
`𝔼_G (oracleAcceptFloor)⁻² ≤ floorInvSqBound mldsa87 κ ‖t₀‖₂²` with `κ = 747/1000`, for
`‖t₀‖∞ ≤ 2^12`. -/
theorem expect_inv_sq_oracleAcceptFloor_le_floorInvSqBound_mldsa87 (t0 : RqVec mldsa87.k)
    (ht0 : polyVecNorm t0 ≤ 4096) :
    𝔼 G : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
        (oracleAcceptFloor mldsa87 (747 / 1000) G t0)⁻¹ ^ 2 ≤
      floorInvSqBound mldsa87 (747 / 1000) (t0SqNorm t0) := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_oracleAcceptFloor_le_mldsa87 t0 ht0
    (expect_hintBoundSum_le_hintMeanBound floorParams_mldsa87.tau_le floorParams_mldsa87.k_pos
      floorParams_mldsa87.two_mul_tau_mul_lt_modulus t0 ht0)
    (expect_hintBoundSqSum_le_hintSqMeanBound floorParams_mldsa87 t0 ht0)
/-! ### ML-DSA-65 -/

section MLDSA65

/-- The grid `a_0 < … < a_7 = 256 k · 2^24` of the layered tail at ML-DSA-65. -/
noncomputable def mldsa65TailGrid : ℕ → ℝ
  | 0 => 9019430514
  | 1 => 9620725882
  | 2 => 10737417279
  | 3 => 14168653810
  | 4 => 14326083297
  | 5 => 16458537255
  | 6 => 20036480136
  | 7 => 25769803776
  | _ => 25769803776

/-- The rates `λ'_i` (units of `4096⁻²`) of the layered tail at ML-DSA-65. -/
noncomputable def mldsa65TailRate : ℕ → ℝ
  | 0 => 9 / 50
  | 1 => 21 / 50
  | 2 => 17 / 20
  | 3 => 41 / 20
  | 4 => 21 / 10
  | 5 => 27 / 10
  | 6 => 69 / 20
  | _ => 0

/-- Upper bounds `U_i` on `floorInvSqBound` at the grid points at ML-DSA-65. -/
noncomputable def mldsa65LevelBound : ℕ → ℝ
  | 0 => 19339937 / 1000000
  | 1 => 6178759 / 250000
  | 2 => 21406711 / 500000
  | 3 => 27253298267 / 1000000
  | 4 => 2 ^ 168
  | 5 => 2 ^ 184
  | 6 => 2 ^ 209
  | 7 => 2 ^ 251
  | _ => 2 ^ 251

/-- Upper bounds `t_i` on the tail factors at ML-DSA-65. -/
noncomputable def mldsa65TailFactorBound : ℕ → ℝ
  | 0 => (14045051 / 25000000) ^ 4
  | 1 => 2⁻¹ ^ 18
  | 2 => 2⁻¹ ^ 80
  | 3 => 2⁻¹ ^ 513
  | 4 => 2⁻¹ ^ 541
  | 5 => 2⁻¹ ^ 982
  | 6 => 2⁻¹ ^ 1902
  | _ => 0

/-- Upper bounds `s_i ≥ (U_(i+1) - U_i) t_i` on the layer terms at ML-DSA-65. -/
noncomputable def mldsa65LayerBound : ℕ → ℝ
  | 0 => (6178759 / 250000 - 19339937 / 1000000) * (14045051 / 25000000) ^ 4
  | 1 => (21406711 / 500000 - 6178759 / 250000) * 2⁻¹ ^ 18
  | 2 => (27253298267 / 1000000 - 21406711 / 500000) * 2⁻¹ ^ 80
  | 3 => 2⁻¹ ^ 200
  | 4 => 2⁻¹ ^ 200
  | 5 => 2⁻¹ ^ 200
  | 6 => 2⁻¹ ^ 200
  | _ => 0

/-- `mldsa65.k = 6`. -/
private theorem mldsa65_k : mldsa65.k = 6 := mldsa65_vals.1

/-- `mldsa65.l = 5`. -/
private theorem mldsa65_l : mldsa65.l = 5 := mldsa65_vals.2.1

/-- `mldsa65.eta = 4`. -/
private theorem mldsa65_eta : mldsa65.eta = 4 := rfl

/-- `mldsa65.tau = 49`. -/
private theorem mldsa65_tau : mldsa65.tau = 49 := mldsa65_tau_lambda.1

/-- `mldsa65.gamma2 = 261888`. -/
private theorem mldsa65_gamma2 : mldsa65.gamma2 = 261888 := mldsa65_vals.2.2.2.1

/-- `mldsa65.beta = 196`. -/
private theorem mldsa65_beta : mldsa65.beta = 196 := mldsa65_vals.2.2.2.2.1

/-- `mldsa65.omega = 55`. -/
private theorem mldsa65_omega : mldsa65.omega = 55 := mldsa65_vals.2.2.2.2.2

/-- `floorInvSqBound ≤ 19.339937` at `‖t₀‖₂² = 9019430514` (ML-DSA-65, Markov branch). -/
private theorem mldsa65_level_le_0 :
    floorInvSqBound mldsa65 (341 / 500) 9019430514 ≤ 19339937 / 1000000 := by
  refine floorInvSqBound_le_of_markov mldsa65 (elo := (30382571673 / 50000000000) ^ 8)
    (ŷ := 4326612741 / 100000000) ?_ ?_ ?_ ?_
  · refine pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) ?_
    refine le_exp_of_le_taylor 14 (by norm_num) ?_ ?_ <;>
      simp only [mldsa65_k, mldsa65_tau] <;>
        norm_num [ringDegree, abs_le, Finset.sum_range_succ, Nat.factorial]
  · simp only [mldsa65_k, mldsa65_tau, mldsa65_gamma2, mldsa65_beta]
    norm_num [ringDegree]
  all_goals (simp only [mldsa65_omega]; norm_num)

/-- `floorInvSqBound ≤ 24.715036` at `‖t₀‖₂² = 9620725882` (ML-DSA-65, Markov branch). -/
private theorem mldsa65_level_le_1 :
    floorInvSqBound mldsa65 (341 / 500) 9620725882 ≤ 6178759 / 250000 := by
  refine floorInvSqBound_le_of_markov mldsa65 (elo := (293901294893 / 500000000000) ^ 8)
    (ŷ := 279597607 / 6250000) ?_ ?_ ?_ ?_
  · refine pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) ?_
    refine le_exp_of_le_taylor 14 (by norm_num) ?_ ?_ <;>
      simp only [mldsa65_k, mldsa65_tau] <;>
        norm_num [ringDegree, abs_le, Finset.sum_range_succ, Nat.factorial]
  · simp only [mldsa65_k, mldsa65_tau, mldsa65_gamma2, mldsa65_beta]
    norm_num [ringDegree]
  all_goals (simp only [mldsa65_omega]; norm_num)

/-- `floorInvSqBound ≤ 42.813422` at `‖t₀‖₂² = 10737417279` (ML-DSA-65, Markov branch). -/
private theorem mldsa65_level_le_2 :
    floorInvSqBound mldsa65 (341 / 500) 10737417279 ≤ 21406711 / 500000 := by
  refine floorInvSqBound_le_of_markov mldsa65 (elo := (276322258239 / 500000000000) ^ 8)
    (ŷ := 2372074603 / 50000000) ?_ ?_ ?_ ?_
  · refine pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) ?_
    refine le_exp_of_le_taylor 14 (by norm_num) ?_ ?_ <;>
      simp only [mldsa65_k, mldsa65_tau] <;>
        norm_num [ringDegree, abs_le, Finset.sum_range_succ, Nat.factorial]
  · simp only [mldsa65_k, mldsa65_tau, mldsa65_gamma2, mldsa65_beta]
    norm_num [ringDegree]
  all_goals (simp only [mldsa65_omega]; norm_num)

/-- `floorInvSqBound ≤ 27253.298267` at `‖t₀‖₂² = 14168653810` (ML-DSA-65, Markov branch). -/
private theorem mldsa65_level_le_3 :
    floorInvSqBound mldsa65 (341 / 500) 14168653810 ≤ 27253298267 / 1000000 := by
  refine floorInvSqBound_le_of_markov mldsa65 (elo := (457237842141 / 1000000000000) ^ 8)
    (ŷ := 5566078231 / 100000000) ?_ ?_ ?_ ?_
  · refine pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) ?_
    refine le_exp_of_le_taylor 14 (by norm_num) ?_ ?_ <;>
      simp only [mldsa65_k, mldsa65_tau] <;>
        norm_num [ringDegree, abs_le, Finset.sum_range_succ, Nat.factorial]
  · simp only [mldsa65_k, mldsa65_tau, mldsa65_gamma2, mldsa65_beta]
    norm_num [ringDegree]
  all_goals (simp only [mldsa65_omega]; norm_num)

/-- `floorInvSqBound ≤ 2^168` at `‖t₀‖₂² = 14326083297` (ML-DSA-65, exponential branch). -/
private theorem mldsa65_level_le_4 :
    floorInvSqBound mldsa65 (341 / 500) 14326083297 ≤ 2 ^ 168 := by
  refine floorInvSqBound_le_two_pow mldsa65 (z := 115601 / 2000) (m := 167) ?_ (by norm_num)
  simp only [mldsa65_k, mldsa65_tau, mldsa65_gamma2, mldsa65_beta]
  norm_num [ringDegree]

/-- `floorInvSqBound ≤ 2^184` at `‖t₀‖₂² = 16458537255` (ML-DSA-65, exponential branch). -/
private theorem mldsa65_level_le_5 :
    floorInvSqBound mldsa65 (341 / 500) 16458537255 ≤ 2 ^ 184 := by
  refine floorInvSqBound_le_two_pow mldsa65 (z := 631297 / 10000) (m := 183) ?_ (by norm_num)
  simp only [mldsa65_k, mldsa65_tau, mldsa65_gamma2, mldsa65_beta]
  norm_num [ringDegree]

/-- `floorInvSqBound ≤ 2^209` at `‖t₀‖₂² = 20036480136` (ML-DSA-65, exponential branch). -/
private theorem mldsa65_level_le_6 :
    floorInvSqBound mldsa65 (341 / 500) 20036480136 ≤ 2 ^ 209 := by
  refine floorInvSqBound_le_two_pow mldsa65 (z := 720713 / 10000) (m := 208) ?_ (by norm_num)
  simp only [mldsa65_k, mldsa65_tau, mldsa65_gamma2, mldsa65_beta]
  norm_num [ringDegree]

/-- `floorInvSqBound ≤ 2^251` at `‖t₀‖₂² = 25769803776` (ML-DSA-65, exponential branch). -/
private theorem mldsa65_level_le_7 :
    floorInvSqBound mldsa65 (341 / 500) 25769803776 ≤ 2 ^ 251 := by
  refine floorInvSqBound_le_two_pow mldsa65 (z := 172799 / 2000) (m := 250) ?_ (by norm_num)
  simp only [mldsa65_k, mldsa65_tau, mldsa65_gamma2, mldsa65_beta]
  norm_num [ringDegree]

/-- The tail factor of layer 0 at ML-DSA-65: `λ' = 9/50`, `a = 9019430514`. -/
private theorem mldsa65_tail_le_0 :
    t0TailBound mldsa65 (9 / 50) 9019430514 ≤ (14045051 / 25000000) ^ 4 := by
  refine (t0TailBound_le_exp mldsa65 (El := 255688758541 / 250000000000)
    (Eh := 204551006833 / 200000000000) (r := 15373873 / 250000000)
    (ρ := 281452987357 / 250000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 531712851297 / 500000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(2306423 / 1000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa65_k, mldsa65_l, mldsa65_eta]
    norm_num [ringDegree]
  refine exp_le_pow_of_exp_div_le (by norm_num) ?_
  refine exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le]) ?_
  norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial]

/-- The tail factor of layer 1 at ML-DSA-65: `λ' = 21/50`, `a = 9620725882`. -/
private theorem mldsa65_tail_le_1 :
    t0TailBound mldsa65 (21 / 50) 9620725882 ≤ 2⁻¹ ^ 18 := by
  refine (t0TailBound_le_exp mldsa65 (El := 526951281039 / 500000000000)
    (Eh := 1053902562079 / 1000000000000) (r := 29651003 / 200000000)
    (ρ := 1312252315433 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 4639234509 / 4000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine exp_le_inv_two_pow_of_le ?_
  simp only [mldsa65_k, mldsa65_l, mldsa65_eta]
  norm_num [ringDegree]

/-- The tail factor of layer 2 at ML-DSA-65: `λ' = 17/20`, `a = 10737417279`. -/
private theorem mldsa65_tail_le_2 :
    t0TailBound mldsa65 (17 / 20) 10737417279 ≤ 2⁻¹ ^ 80 := by
  refine (t0TailBound_le_exp mldsa65 (El := 556049933361 / 500000000000)
    (Eh := 1112099866723 / 1000000000000) (r := 15894653 / 50000000)
    (ρ := 851257815369 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 171778661661 / 125000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine exp_le_inv_two_pow_of_le ?_
  simp only [mldsa65_k, mldsa65_l, mldsa65_eta]
  norm_num [ringDegree]

/-- The tail factor of layer 3 at ML-DSA-65: `λ' = 41/20`, `a = 14168653810`. -/
private theorem mldsa65_tail_le_3 :
    t0TailBound mldsa65 (41 / 20) 14168653810 ≤ 2⁻¹ ^ 513 := by
  refine (t0TailBound_le_exp mldsa65 (El := 323018926623 / 250000000000)
    (Eh := 1292075706493 / 1000000000000) (r := 2231361 / 2500000)
    (ρ := 397728391063 / 125000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 2441333484339 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine exp_le_inv_two_pow_of_le ?_
  simp only [mldsa65_k, mldsa65_l, mldsa65_eta]
  norm_num [ringDegree]

/-- The tail factor of layer 4 at ML-DSA-65: `λ' = 21/10`, `a = 14326083297`. -/
private theorem mldsa65_tail_le_4 :
    t0TailBound mldsa65 (21 / 10) 14326083297 ≤ 2⁻¹ ^ 541 := by
  refine (t0TailBound_le_exp mldsa65 (El := 162522058521 / 125000000000)
    (Eh := 1300176468169 / 1000000000000) (r := 919749427 / 1000000000)
    (ρ := 3255189765949 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 627165427069 / 250000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine exp_le_inv_two_pow_of_le ?_
  simp only [mldsa65_k, mldsa65_l, mldsa65_eta]
  norm_num [ringDegree]

/-- The tail factor of layer 5 at ML-DSA-65: `λ' = 27/10`, `a = 16458537255`. -/
private theorem mldsa65_tail_le_5 :
    t0TailBound mldsa65 (27 / 10) 16458537255 ≤ 2⁻¹ ^ 982 := by
  refine (t0TailBound_le_exp mldsa65 (El := 1401439608391 / 1000000000000)
    (Eh := 175179951049 / 125000000000) (r := 1265795559 / 1000000000)
    (ρ := 4196305272409 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 2) (r := 470764842899 / 250000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine exp_le_inv_two_pow_of_le ?_
  simp only [mldsa65_k, mldsa65_l, mldsa65_eta]
  norm_num [ringDegree]

/-- The tail factor of layer 6 at ML-DSA-65: `λ' = 69/20`, `a = 20036480136`. -/
private theorem mldsa65_tail_le_6 :
    t0TailBound mldsa65 (69 / 20) 20036480136 ≤ 2⁻¹ ^ 1902 := by
  refine (t0TailBound_le_exp mldsa65 (El := 307836059387 / 200000000000)
    (Eh := 192397537117 / 125000000000) (r := 872973267 / 500000000)
    (ρ := 1374045220721 / 250000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 2) (r := 2394018337781 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine exp_le_inv_two_pow_of_le ?_
  simp only [mldsa65_k, mldsa65_l, mldsa65_eta]
  norm_num [ringDegree]

/-- **The key and matrix average of the floor bound at ML-DSA-65**: for uniform box secrets
`e` and a uniform matrix `Â`, `𝔼_{e, Â} floorInvSqBound(‖t₀‖₂²) ≤ (9/2)²`
(`expect_expect_le_layers_chord` on the grid `mldsa65TailGrid` with the rates `mldsa65TailRate`). -/
theorem expect_expect_floorInvSqBound_le_mldsa65 (sk : SecretKey mldsa65) :
    𝔼 e : SecretCoeffs mldsa65, 𝔼 aHat : TqMatrix mldsa65.k mldsa65.l,
        floorInvSqBound mldsa65 (341 / 500) (t0SqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0) ≤
      (9 / 2) ^ 2 := by
  have hT : ∀ i < 7, t0TailBound mldsa65 (mldsa65TailRate i) (mldsa65TailGrid i) ≤
      mldsa65TailFactorBound i := by
    intro i hi
    interval_cases i <;> simp only [mldsa65TailRate, mldsa65TailGrid, mldsa65TailFactorBound]
    · exact mldsa65_tail_le_0
    · exact mldsa65_tail_le_1
    · exact mldsa65_tail_le_2
    · exact mldsa65_tail_le_3
    · exact mldsa65_tail_le_4
    · exact mldsa65_tail_le_5
    · exact mldsa65_tail_le_6
  have hU : ∀ i < 7, mldsa65LevelBound i ≤ mldsa65LevelBound (i + 1) := by
    intro i hi
    interval_cases i <;> simp only [mldsa65LevelBound]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pow_le_pow_right₀ (by norm_num) (by norm_num)
    · exact pow_le_pow_right₀ (by norm_num) (by norm_num)
    · exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hS : ∀ i < 7, (mldsa65LevelBound (i + 1) - mldsa65LevelBound i) * mldsa65TailFactorBound i ≤
      mldsa65LayerBound i := by
    intro i hi
    interval_cases i <;> simp only [mldsa65LevelBound, mldsa65TailFactorBound, mldsa65LayerBound]
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact two_pow_sub_mul_inv_two_pow_le (by positivity) (by norm_num)
    · exact two_pow_sub_mul_inv_two_pow_le (by positivity) (by norm_num)
    · exact two_pow_sub_mul_inv_two_pow_le (by positivity) (by norm_num)
    · exact two_pow_sub_mul_inv_two_pow_le (by positivity) (by norm_num)
  refine (expect_expect_le_layers_chord sk (by simp only [mldsa65_eta]; norm_num [modulus])
    (monotone_floorInvSqBound mldsa65 (by norm_num)) (a := mldsa65TailGrid) (U := mldsa65LevelBound)
    (N := 7) ?_ hU ?_ ?_ (lam := mldsa65TailRate) ?_).trans ?_
  · intro i hi
    interval_cases i <;> norm_num [mldsa65TailGrid]
  · intro i hi
    interval_cases i <;> simp only [mldsa65TailGrid, mldsa65LevelBound]
    · exact mldsa65_level_le_0
    · exact mldsa65_level_le_1
    · exact mldsa65_level_le_2
    · exact mldsa65_level_le_3
    · exact mldsa65_level_le_4
    · exact mldsa65_level_le_5
    · exact mldsa65_level_le_6
    · exact mldsa65_level_le_7
  · simp only [mldsa65_k]
    norm_num [ringDegree, mldsa65TailGrid]
  · intro i
    unfold mldsa65TailRate
    split <;> norm_num
  calc _ ≤ mldsa65LevelBound 0 + ∑ i ∈ range 7, mldsa65LayerBound i :=
        add_le_add le_rfl (Finset.sum_le_sum fun i hi => (mul_le_mul_of_nonneg_left
          (hT i (mem_range.1 hi)) (sub_nonneg.2 (hU i (mem_range.1 hi)))).trans
            (hS i (mem_range.1 hi)))
    _ ≤ _ := by norm_num [Finset.sum_range_succ, mldsa65LevelBound, mldsa65LayerBound]

end MLDSA65
/-! ### ML-DSA-87 -/

section MLDSA87

/-- The grid `a_0 < … < a_7 = 256 k · 2^24` of the layered tail at ML-DSA-87. -/
noncomputable def mldsa87TailGrid : ℕ → ℝ
  | 0 => 12025907352
  | 1 => 12827634509
  | 2 => 14316556372
  | 3 => 15887658760
  | 4 => 16064188302
  | 5 => 18455361186
  | 6 => 22467396226
  | 7 => 34359738368
  | _ => 34359738368

/-- The rates `λ'_i` (units of `4096⁻²`) of the layered tail at ML-DSA-87. -/
noncomputable def mldsa87TailRate : ℕ → ℝ
  | 0 => 9 / 50
  | 1 => 21 / 50
  | 2 => 17 / 20
  | 3 => 63 / 50
  | 4 => 131 / 100
  | 5 => 179 / 100
  | 6 => 56 / 25
  | _ => 0

/-- Upper bounds `U_i` on `floorInvSqBound` at the grid points at ML-DSA-87. -/
noncomputable def mldsa87LevelBound : ℕ → ℝ
  | 0 => 10410473 / 250000
  | 1 => 32556973 / 500000
  | 2 => 11301713 / 50000
  | 3 => 13307311271 / 500000
  | 4 => 2 ^ 229
  | 5 => 2 ^ 250
  | 6 => 2 ^ 285
  | 7 => 2 ^ 391
  | _ => 2 ^ 391

/-- Upper bounds `t_i` on the tail factors at ML-DSA-87. -/
noncomputable def mldsa87TailFactorBound : ℕ → ℝ
  | 0 => (46347157 / 100000000) ^ 4
  | 1 => 2⁻¹ ^ 25
  | 2 => 2⁻¹ ^ 106
  | 3 => 2⁻¹ ^ 250
  | 4 => 2⁻¹ ^ 269
  | 5 => 2⁻¹ ^ 590
  | 6 => 2⁻¹ ^ 1282
  | _ => 0

/-- Upper bounds `s_i ≥ (U_(i+1) - U_i) t_i` on the layer terms at ML-DSA-87. -/
noncomputable def mldsa87LayerBound : ℕ → ℝ
  | 0 => (32556973 / 500000 - 10410473 / 250000) * (46347157 / 100000000) ^ 4
  | 1 => (11301713 / 50000 - 32556973 / 500000) * 2⁻¹ ^ 25
  | 2 => (13307311271 / 500000 - 11301713 / 50000) * 2⁻¹ ^ 106
  | 3 => 2⁻¹ ^ 21
  | 4 => 2⁻¹ ^ 19
  | 5 => 2⁻¹ ^ 200
  | 6 => 2⁻¹ ^ 200
  | _ => 0

/-- `mldsa87.k = 8`. -/
private theorem mldsa87_k : mldsa87.k = 8 := mldsa87_vals.1

/-- `mldsa87.l = 7`. -/
private theorem mldsa87_l : mldsa87.l = 7 := mldsa87_vals.2.1

/-- `mldsa87.eta = 2`. -/
private theorem mldsa87_eta : mldsa87.eta = 2 := rfl

/-- `mldsa87.tau = 60`. -/
private theorem mldsa87_tau : mldsa87.tau = 60 := mldsa87_tau_lambda.1

/-- `mldsa87.gamma2 = 261888`. -/
private theorem mldsa87_gamma2 : mldsa87.gamma2 = 261888 := mldsa87_vals.2.2.2.1

/-- `mldsa87.beta = 120`. -/
private theorem mldsa87_beta : mldsa87.beta = 120 := mldsa87_vals.2.2.2.2.1

/-- `mldsa87.omega = 75`. -/
private theorem mldsa87_omega : mldsa87.omega = 75 := mldsa87_vals.2.2.2.2.2

/-- `floorInvSqBound ≤ 41.641892` at `‖t₀‖₂² = 12025907352` (ML-DSA-87, Markov branch). -/
private theorem mldsa87_level_le_0 :
    floorInvSqBound mldsa87 (747 / 1000) 12025907352 ≤ 10410473 / 250000 := by
  refine floorInvSqBound_le_of_markov mldsa87 (elo := (21734375547 / 40000000000) ^ 8)
    (ŷ := 6422262861 / 100000000) ?_ ?_ ?_ ?_
  · refine pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) ?_
    refine le_exp_of_le_taylor 14 (by norm_num) ?_ ?_ <;>
      simp only [mldsa87_k, mldsa87_tau] <;>
        norm_num [ringDegree, abs_le, Finset.sum_range_succ, Nat.factorial]
  · simp only [mldsa87_k, mldsa87_tau, mldsa87_gamma2, mldsa87_beta]
    norm_num [ringDegree]
  all_goals (simp only [mldsa87_omega]; norm_num)

/-- `floorInvSqBound ≤ 65.113946` at `‖t₀‖₂² = 12827634509` (ML-DSA-87, Markov branch). -/
private theorem mldsa87_level_le_1 :
    floorInvSqBound mldsa87 (747 / 1000) 12827634509 ≤ 32556973 / 500000 := by
  refine floorInvSqBound_le_of_markov mldsa87 (elo := (521706587653 / 1000000000000) ^ 8)
    (ŷ := 332908059 / 5000000) ?_ ?_ ?_ ?_
  · refine pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) ?_
    refine le_exp_of_le_taylor 14 (by norm_num) ?_ ?_ <;>
      simp only [mldsa87_k, mldsa87_tau] <;>
        norm_num [ringDegree, abs_le, Finset.sum_range_succ, Nat.factorial]
  · simp only [mldsa87_k, mldsa87_tau, mldsa87_gamma2, mldsa87_beta]
    norm_num [ringDegree]
  all_goals (simp only [mldsa87_omega]; norm_num)

/-- `floorInvSqBound ≤ 226.034260` at `‖t₀‖₂² = 14316556372` (ML-DSA-87, Markov branch). -/
private theorem mldsa87_level_le_2 :
    floorInvSqBound mldsa87 (747 / 1000) 14316556372 ≤ 11301713 / 50000 := by
  refine floorInvSqBound_le_of_markov mldsa87 (elo := (48375736497 / 100000000000) ^ 8)
    (ŷ := 3547246917 / 50000000) ?_ ?_ ?_ ?_
  · refine pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) ?_
    refine le_exp_of_le_taylor 14 (by norm_num) ?_ ?_ <;>
      simp only [mldsa87_k, mldsa87_tau] <;>
        norm_num [ringDegree, abs_le, Finset.sum_range_succ, Nat.factorial]
  · simp only [mldsa87_k, mldsa87_tau, mldsa87_gamma2, mldsa87_beta]
    norm_num [ringDegree]
  all_goals (simp only [mldsa87_omega]; norm_num)

/-- `floorInvSqBound ≤ 26614.622542` at `‖t₀‖₂² = 15887658760` (ML-DSA-87, Markov branch). -/
private theorem mldsa87_level_le_3 :
    floorInvSqBound mldsa87 (747 / 1000) 15887658760 ≤ 13307311271 / 500000 := by
  refine floorInvSqBound_le_of_markov mldsa87 (elo := (446702666393 / 1000000000000) ^ 8)
    (ŷ := 7553414213 / 100000000) ?_ ?_ ?_ ?_
  · refine pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) ?_
    refine le_exp_of_le_taylor 14 (by norm_num) ?_ ?_ <;>
      simp only [mldsa87_k, mldsa87_tau] <;>
        norm_num [ringDegree, abs_le, Finset.sum_range_succ, Nat.factorial]
  · simp only [mldsa87_k, mldsa87_tau, mldsa87_gamma2, mldsa87_beta]
    norm_num [ringDegree]
  all_goals (simp only [mldsa87_omega]; norm_num)

/-- `floorInvSqBound ≤ 2^229` at `‖t₀‖₂² = 16064188302` (ML-DSA-87, exponential branch). -/
private theorem mldsa87_level_le_4 :
    floorInvSqBound mldsa87 (747 / 1000) 16064188302 ≤ 2 ^ 229 := by
  refine floorInvSqBound_le_two_pow mldsa87 (z := 786943 / 10000) (m := 228) ?_ (by norm_num)
  simp only [mldsa87_k, mldsa87_tau, mldsa87_gamma2, mldsa87_beta]
  norm_num [ringDegree]

/-- `floorInvSqBound ≤ 2^250` at `‖t₀‖₂² = 18455361186` (ML-DSA-87, exponential branch). -/
private theorem mldsa87_level_le_5 :
    floorInvSqBound mldsa87 (747 / 1000) 18455361186 ≤ 2 ^ 250 := by
  refine floorInvSqBound_le_two_pow mldsa87 (z := 430217 / 5000) (m := 249) ?_ (by norm_num)
  simp only [mldsa87_k, mldsa87_tau, mldsa87_gamma2, mldsa87_beta]
  norm_num [ringDegree]

/-- `floorInvSqBound ≤ 2^285` at `‖t₀‖₂² = 22467396226` (ML-DSA-87, exponential branch). -/
private theorem mldsa87_level_le_6 :
    floorInvSqBound mldsa87 (747 / 1000) 22467396226 ≤ 2 ^ 285 := by
  refine floorInvSqBound_le_two_pow mldsa87 (z := 983741 / 10000) (m := 284) ?_ (by norm_num)
  simp only [mldsa87_k, mldsa87_tau, mldsa87_gamma2, mldsa87_beta]
  norm_num [ringDegree]

/-- `floorInvSqBound ≤ 2^391` at `‖t₀‖₂² = 34359738368` (ML-DSA-87, exponential branch). -/
private theorem mldsa87_level_le_7 :
    floorInvSqBound mldsa87 (747 / 1000) 34359738368 ≤ 2 ^ 391 := by
  refine floorInvSqBound_le_two_pow mldsa87 (z := 337311 / 2500) (m := 390) ?_ (by norm_num)
  simp only [mldsa87_k, mldsa87_tau, mldsa87_gamma2, mldsa87_beta]
  norm_num [ringDegree]

/-- The tail factor of layer 0 at ML-DSA-87: `λ' = 9/50`, `a = 12025907352`. -/
private theorem mldsa87_tail_le_0 :
    t0TailBound mldsa87 (9 / 50) 12025907352 ≤ (46347157 / 100000000) ^ 4 := by
  refine (t0TailBound_le_exp mldsa87 (El := 255688758541 / 250000000000)
    (Eh := 204551006833 / 200000000000) (r := 15373873 / 250000000)
    (ρ := 281452987357 / 250000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 531712851297 / 500000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(3076041 / 1000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa87_k, mldsa87_l, mldsa87_eta]
    norm_num [ringDegree]
  refine exp_le_pow_of_exp_div_le (by norm_num) ?_
  refine exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le]) ?_
  norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial]

/-- The tail factor of layer 1 at ML-DSA-87: `λ' = 21/50`, `a = 12827634509`. -/
private theorem mldsa87_tail_le_1 :
    t0TailBound mldsa87 (21 / 50) 12827634509 ≤ 2⁻¹ ^ 25 := by
  refine (t0TailBound_le_exp mldsa87 (El := 526951281039 / 500000000000)
    (Eh := 1053902562079 / 1000000000000) (r := 29651003 / 200000000)
    (ρ := 1312252315433 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 4639234509 / 4000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine exp_le_inv_two_pow_of_le ?_
  simp only [mldsa87_k, mldsa87_l, mldsa87_eta]
  norm_num [ringDegree]

/-- The tail factor of layer 2 at ML-DSA-87: `λ' = 17/20`, `a = 14316556372`. -/
private theorem mldsa87_tail_le_2 :
    t0TailBound mldsa87 (17 / 20) 14316556372 ≤ 2⁻¹ ^ 106 := by
  refine (t0TailBound_le_exp mldsa87 (El := 556049933361 / 500000000000)
    (Eh := 1112099866723 / 1000000000000) (r := 15894653 / 50000000)
    (ρ := 851257815369 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 171778661661 / 125000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine exp_le_inv_two_pow_of_le ?_
  simp only [mldsa87_k, mldsa87_l, mldsa87_eta]
  norm_num [ringDegree]

/-- The tail factor of layer 3 at ML-DSA-87: `λ' = 63/50`, `a = 15887658760`. -/
private theorem mldsa87_tail_le_3 :
    t0TailBound mldsa87 (63 / 50) 15887658760 ≤ 2⁻¹ ^ 250 := by
  refine (t0TailBound_le_exp mldsa87 (El := 1170580757981 / 1000000000000)
    (Eh := 585290378991 / 500000000000) (r := 497265041 / 1000000000)
    (ρ := 42882646481 / 20000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 822109123111 / 500000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine exp_le_inv_two_pow_of_le ?_
  simp only [mldsa87_k, mldsa87_l, mldsa87_eta]
  norm_num [ringDegree]

/-- The tail factor of layer 4 at ML-DSA-87: `λ' = 131/100`, `a = 16064188302`. -/
private theorem mldsa87_tail_le_4 :
    t0TailBound mldsa87 (131 / 100) 16064188302 ≤ 2⁻¹ ^ 269 := by
  refine (t0TailBound_le_exp mldsa87 (El := 117791979833 / 100000000000)
    (Eh := 1177919798331 / 1000000000000) (r := 104068133 / 200000000)
    (ρ := 2202645935677 / 1000000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 1682600755261 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine exp_le_inv_two_pow_of_le ?_
  simp only [mldsa87_k, mldsa87_l, mldsa87_eta]
  norm_num [ringDegree]

/-- The tail factor of layer 5 at ML-DSA-87: `λ' = 179/100`, `a = 18455361186`. -/
private theorem mldsa87_tail_le_5 :
    t0TailBound mldsa87 (179 / 100) 18455361186 ≤ 2⁻¹ ^ 590 := by
  refine (t0TailBound_le_exp mldsa87 (El := 625379145383 / 500000000000)
    (Eh := 1250758290767 / 1000000000000) (r := 151048359 / 200000000)
    (ρ := 1407212820919 / 500000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 2128126031383 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine exp_le_inv_two_pow_of_le ?_
  simp only [mldsa87_k, mldsa87_l, mldsa87_eta]
  norm_num [ringDegree]

/-- The tail factor of layer 6 at ML-DSA-87: `λ' = 56/25`, `a = 22467396226`. -/
private theorem mldsa87_tail_le_6 :
    t0TailBound mldsa87 (56 / 25) 22467396226 ≤ 2⁻¹ ^ 1282 := by
  refine (t0TailBound_le_exp mldsa87 (El := 1323129812337 / 1000000000000)
    (Eh := 661564906169 / 500000000000) (r := 997281437 / 1000000000)
    (ρ := 693004110079 / 200000000000) (by norm_num) (by norm_num) ?_ ?_ ?_
    (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 1355451021891 / 500000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ,
          Nat.factorial])))
    norm_num [t0ChordPoly]
  refine exp_le_inv_two_pow_of_le ?_
  simp only [mldsa87_k, mldsa87_l, mldsa87_eta]
  norm_num [ringDegree]

/-- **The key and matrix average of the floor bound at ML-DSA-87**: for uniform box secrets
`e` and a uniform matrix `Â`, `𝔼_{e, Â} floorInvSqBound(‖t₀‖₂²) ≤ (33/5)²`
(`expect_expect_le_layers_chord` on the grid `mldsa87TailGrid` with the rates `mldsa87TailRate`). -/
theorem expect_expect_floorInvSqBound_le_mldsa87 (sk : SecretKey mldsa87) :
    𝔼 e : SecretCoeffs mldsa87, 𝔼 aHat : TqMatrix mldsa87.k mldsa87.l,
        floorInvSqBound mldsa87 (747 / 1000) (t0SqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0) ≤
      (33 / 5) ^ 2 := by
  have hT : ∀ i < 7, t0TailBound mldsa87 (mldsa87TailRate i) (mldsa87TailGrid i) ≤
      mldsa87TailFactorBound i := by
    intro i hi
    interval_cases i <;> simp only [mldsa87TailRate, mldsa87TailGrid, mldsa87TailFactorBound]
    · exact mldsa87_tail_le_0
    · exact mldsa87_tail_le_1
    · exact mldsa87_tail_le_2
    · exact mldsa87_tail_le_3
    · exact mldsa87_tail_le_4
    · exact mldsa87_tail_le_5
    · exact mldsa87_tail_le_6
  have hU : ∀ i < 7, mldsa87LevelBound i ≤ mldsa87LevelBound (i + 1) := by
    intro i hi
    interval_cases i <;> simp only [mldsa87LevelBound]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pow_le_pow_right₀ (by norm_num) (by norm_num)
    · exact pow_le_pow_right₀ (by norm_num) (by norm_num)
    · exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hS : ∀ i < 7, (mldsa87LevelBound (i + 1) - mldsa87LevelBound i) * mldsa87TailFactorBound i ≤
      mldsa87LayerBound i := by
    intro i hi
    interval_cases i <;> simp only [mldsa87LevelBound, mldsa87TailFactorBound, mldsa87LayerBound]
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact two_pow_sub_mul_inv_two_pow_le (by positivity) (by norm_num)
    · exact two_pow_sub_mul_inv_two_pow_le (by positivity) (by norm_num)
    · exact two_pow_sub_mul_inv_two_pow_le (by positivity) (by norm_num)
    · exact two_pow_sub_mul_inv_two_pow_le (by positivity) (by norm_num)
  refine (expect_expect_le_layers_chord sk (by simp only [mldsa87_eta]; norm_num [modulus])
    (monotone_floorInvSqBound mldsa87 (by norm_num)) (a := mldsa87TailGrid) (U := mldsa87LevelBound)
    (N := 7) ?_ hU ?_ ?_ (lam := mldsa87TailRate) ?_).trans ?_
  · intro i hi
    interval_cases i <;> norm_num [mldsa87TailGrid]
  · intro i hi
    interval_cases i <;> simp only [mldsa87TailGrid, mldsa87LevelBound]
    · exact mldsa87_level_le_0
    · exact mldsa87_level_le_1
    · exact mldsa87_level_le_2
    · exact mldsa87_level_le_3
    · exact mldsa87_level_le_4
    · exact mldsa87_level_le_5
    · exact mldsa87_level_le_6
    · exact mldsa87_level_le_7
  · simp only [mldsa87_k]
    norm_num [ringDegree, mldsa87TailGrid]
  · intro i
    unfold mldsa87TailRate
    split <;> norm_num
  calc _ ≤ mldsa87LevelBound 0 + ∑ i ∈ range 7, mldsa87LayerBound i :=
        add_le_add le_rfl (Finset.sum_le_sum fun i hi => (mul_le_mul_of_nonneg_left
          (hT i (mem_range.1 hi)) (sub_nonneg.2 (hU i (mem_range.1 hi)))).trans
            (hS i (mem_range.1 hi)))
    _ ≤ _ := by norm_num [Finset.sum_range_succ, mldsa87LevelBound, mldsa87LayerBound]

end MLDSA87

end GordieHowe.MLDSA.Regularity
