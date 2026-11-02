-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.WeightTail
public import GordieHowe.Applications.MLDSA.Regularity.WeightLines44
public import GordieHowe.Applications.MLDSA.Regularity.Ct0Tail44

@[expose] public section

/-!
# The inverse square of the member weight at ML-DSA-44, averaged over keys and matrices

At ML-DSA-44 (FIPS 204, Table 1: `k = ℓ = 4`, `η = 2`, `τ = 39`, `γ₂ = 95232`, `β = 78`,
`ω = 80`) the ct₀-check can fail (`τ · 2^12 > γ₂`), so the acceptance floor of ML-DSA-65 and
ML-DSA-87 (`FloorParams`) does not apply. This file bounds `𝔼_{s, Â, G} w⁻²` for a lower bound
`w` on the mean member weights that may vanish, with `SampleInBall = G` a random oracle onto
`B_39`.

**Lines.** For a line `α - σ N x₀ ≤ Pr[Bin(N, x₀) ≤ ω]` (`σ ≥ 0`, every `N ≤ 256 k`) and hint
fraction bounds at most `x₀`, `α π_G - σ m_G` is at most the mean member weight in every bucket
vector (`line_le_expect_memberWeight`), where `π_G = 𝔼_c̃ 1[‖G(c̃)·t₀‖∞ < γ₂]`
(`ct0Indicator`) and `m_G = 𝔼_c̃ hintBoundSum(G(c̃), t₀)`. At ML-DSA-44 every hint fraction bound
of a shift `|b| ≤ τ 2^12` is at most `x₀ = 21/25` (`hintFractionBound_le_mldsa44`), and the four
lines of `WeightLines44.lean` and the line `(2^-3072, 0)` give the weight
`mldsa44OracleWeight G t₀ = max(mldsa44LineValue(π_G, m_G), 2^-3072 π_G)`
(`mldsa44OracleWeight_le_expect_memberWeight`). It is `0` only if every `c̃` fails the ct₀-check,
and then every mean member weight is `0` (`expect_memberWeight_eq_zero_of_mldsa44OracleWeight`).

**The oracle average.** Hoeffding's inequality over the values of `G` (`2^256` commitment hashes,
deviation `2^-64`) for `π_G` and `m_G`, and `w ≥ 2^-3072 · 2^-256` whenever `π_G > 0`, give
`𝔼_G w⁻² ≤ ĝ⁻² + 2^-1000` for `0 < ĝ ≤ mldsa44LineValue(π̂ - 2^-64, m̂ + 2^-64)`, `π̂` a lower
bound on `𝔼_{c ∈ B_39} 1[ct₀ ok]` and `m̂` an upper bound on `𝔼_c hintBoundSum`
(`expect_inv_sq_mldsa44OracleWeight_le`). With `m̂ = hintMeanBound(a) ≥ hintMeanBound(‖t₀‖₂²)`
(`expect_hintBoundSum_le_hintMeanBound`) this is a level bound for all `t₀` with `‖t₀‖₂² ≤ a`
(`expect_inv_sq_mldsa44OracleWeight_le_of_line`).

**The layered average.** Write `S = ‖t₀‖₂²` and `S_m = ‖t₀,m‖₂²`. Three layers by the largest
component: every `S_m < 2^31` (`s_m < 1/2`), where the ct₀-check fails with probability at most
`3/4000` (`one_sub_le_expect_challengeBall_ct0_mldsa44_half`); every `S_m < (31/50) 2^32`, at most
`3/250`; and every key, at most `217/625` (`one_sub_le_expect_challengeBall_ct0_mldsa44`). Each
layer is a layer cake in `S` on the event that some `S_m` reaches the layer's lower end
(`le_add_sum_layers_of_imp`, `expect_expect_indicator_mul_layers_le`), with the joint Chernoff
tails of `S` and the largest component
(`expect_expect_indicator_le_t0SqNorm_and_le_t0CompSqNorm_le`,
`expect_expect_indicator_le_t0SqNorm_and_exists_le_t0CompSqNorm_le`) bounded through
`jointTailBound_le_exp`.

**Result.** `𝔼_{s, Â, G} (mldsa44OracleWeight G t₀)⁻² ≤ (24/5)²`
(`expect_expect_expect_inv_sq_mldsa44OracleWeight_le`; the rational right side is `22.87`): the
weight costs `log₂(24/5) = 2.26` bits of the regularity gap.
-/

open Finset Real
open scoped BigOperators ENNReal

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA LatticeCrypto TransformOps

/-! ### Lines below the mean member weight -/

section Lines

/-- **An average is at least `1/|X|` times one value**: for `f ≥ 0` on a finite type `X` and
`f x₀ ≥ 1`, `1/|X| ≤ 𝔼_x f x`. -/
theorem one_div_card_le_expect {X : Type*} [Fintype X] {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) (x₀ : X)
    (h : 1 ≤ f x₀) : 1 / (Fintype.card X : ℝ) ≤ 𝔼 x, f x := by
  rw [Fintype.expect_eq_sum_div_card]
  exact div_le_div_of_nonneg_right (h.trans (Finset.single_le_sum (fun x _ => hf x)
    (Finset.mem_univ x₀))) (Nat.cast_nonneg _)

variable {p : Params} [nttOps : NTTRingOps]

/-- **The ct₀ indicator of `c·t₀`**: `1` if `‖c·t₀‖∞ < γ₂` (FIPS 204 Algorithm 7 line 28), else
`0`. -/
noncomputable def ct0Indicator (γ₂ : ℕ) {k : ℕ} (c : Rq) (t0 : RqVec k) : ℝ :=
  if ∀ x, |centeredCoeffs (c • t0) x| < γ₂ then 1 else 0

/-- The ct₀ indicator is nonnegative. -/
theorem ct0Indicator_nonneg (γ₂ : ℕ) {k : ℕ} (c : Rq) (t0 : RqVec k) :
    0 ≤ ct0Indicator γ₂ c t0 := by
  unfold ct0Indicator
  split_ifs <;> norm_num

/-- The ct₀ indicator is at most `1`. -/
theorem ct0Indicator_le_one (γ₂ : ℕ) {k : ℕ} (c : Rq) (t0 : RqVec k) :
    ct0Indicator γ₂ c t0 ≤ 1 := by
  unfold ct0Indicator
  split_ifs <;> norm_num

/-- The ct₀ indicator is `0` or `1`. -/
theorem ct0Indicator_eq_zero_or_eq_one (γ₂ : ℕ) {k : ℕ} (c : Rq) (t0 : RqVec k) :
    ct0Indicator γ₂ c t0 = 0 ∨ ct0Indicator γ₂ c t0 = 1 := by
  unfold ct0Indicator
  split_ifs <;> simp

/-- **The member weight is at most the ct₀ indicator**: `min(1, aw/β_min) ≤ 1[‖b‖∞ < γ₂]` for
`prims` with `SampleInBall = G`, since the acceptance weight vanishes when the check fails. -/
theorem toReal_memberWeight_le_ct0Indicator (prims : Primitives p)
    (G : CommitHashBytes p → ChallengeBall p.tau)
    (hG : ∀ cTilde, prims.sampleInBall cTilde = (G cTilde).1) (βmin : ℚ≥0) (t0 : RqVec p.k)
    (v : BucketVec p) (cTilde : CommitHashBytes p) :
    (memberWeight prims βmin t0 (v, cTilde) : ℝ≥0∞).toReal ≤
      ct0Indicator p.gamma2 (G cTilde).1 t0 := by
  unfold ct0Indicator
  split_ifs with h
  · have h1 : (memberWeight prims βmin t0 (v, cTilde) : ℝ≥0∞) ≤ 1 :=
      ENNReal.nnratCast_le_one.2 (NNRat.minOneDiv_le_one _ _)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1
  · have h0 : t0Weight prims t0 (v, cTilde) = 0 := by
      simp only [t0Weight, acceptWeightQ, hG]
      rw [if_neg h, zero_mul, Rat.toNNRat_zero]
    simp [memberWeight, NNRat.minOneDiv, h0]

/-- **A line below the mean member weight.** For `prims` with `SampleInBall = G`, `β_min ≤ 1`,
hint fraction bounds `hintFractionBound((G(c̃)·t₀)_x) ≤ x₀`, `σ ≥ 0` and a line
`α - σ N x₀ ≤ Pr[Bin(N, x₀) ≤ ω]` at every `N ≤ 256 k`, in every bucket vector `v`:
`α 𝔼_c̃ 1[‖G(c̃)·t₀‖∞ < γ₂] - σ 𝔼_c̃ hintBoundSum(G(c̃), t₀) ≤ 𝔼_c̃ memberWeight(t₀, (v, c̃))`
(`line_le_expect_acceptWeight`, `toReal_t0Weight_le_memberWeight`). -/
theorem line_le_expect_memberWeight (hp : SigningParams p) (prims : Primitives p)
    (G : CommitHashBytes p → ChallengeBall p.tau)
    (hG : ∀ cTilde, prims.sampleInBall cTilde = (G cTilde).1) {βmin : ℚ≥0} (hβ : (βmin : ℝ≥0∞) ≤ 1)
    (t0 : RqVec p.k) {x₀ α σ : ℝ}
    (hx : ∀ cTilde x, hintFractionBound p.gamma2 p.beta (centeredCoeffs ((G cTilde).1 • t0) x) ≤ x₀)
    (hσ : 0 ≤ σ) (hline : ∀ N ≤ p.k * ringDegree, α - σ * N * x₀ ≤ binomialCdf x₀ N p.omega)
    (v : BucketVec p) :
    α * 𝔼 cTilde, ct0Indicator p.gamma2 (G cTilde).1 t0 -
        σ * 𝔼 cTilde, hintBoundSum p.gamma2 p.beta (G cTilde).1 t0 ≤
      𝔼 cTilde, (memberWeight prims βmin t0 (v, cTilde) : ℝ≥0∞).toReal := by
  have hcard : Fintype.card (Fin p.k × Fin ringDegree) = p.k * ringDegree := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have h := line_le_expect_acceptWeight (C := CommitHashBytes p) hp.beta_lt_gamma2
    (fun cTilde => centeredCoeffs ((G cTilde).1 • t0)) hx hσ
    (fun N hN => hline N (hcard ▸ hN)) (fun x => (v x).val)
  simp only [ct0Indicator, hintBoundSum]
  refine h.trans (Finset.expect_le_expect fun cTilde _ => ?_)
  refine le_trans (le_of_eq ?_) (toReal_t0Weight_le_memberWeight prims hp hβ t0 (v, cTilde))
  rw [coe_t0Weight, ENNReal.toReal_ofReal (acceptWeight_nonneg hp.beta_lt_gamma2 _ _ _), hG]

end Lines

/-! ### The weight at ML-DSA-44 -/

section Weight44

/-- `_root_.MLDSA.mldsa44.k = 4`. -/
private theorem mldsa44_k : _root_.MLDSA.mldsa44.k = 4 := mldsa44_vals.1

/-- `_root_.MLDSA.mldsa44.l = 4`. -/
private theorem mldsa44_l : _root_.MLDSA.mldsa44.l = 4 := mldsa44_vals.2.1

/-- `_root_.MLDSA.mldsa44.eta = 2`. -/
private theorem mldsa44_eta : _root_.MLDSA.mldsa44.eta = 2 := rfl

/-- `_root_.MLDSA.mldsa44.tau = 39`. -/
private theorem mldsa44_tau : _root_.MLDSA.mldsa44.tau = 39 := rfl

/-- `_root_.MLDSA.mldsa44.lambda = 128`. -/
private theorem mldsa44_lambda : _root_.MLDSA.mldsa44.lambda = 128 := rfl

/-- `_root_.MLDSA.mldsa44.gamma2 = 95232`. -/
private theorem mldsa44_gamma2 : _root_.MLDSA.mldsa44.gamma2 = 95232 := mldsa44_vals.2.2.2.1

/-- `_root_.MLDSA.mldsa44.beta = 78`. -/
private theorem mldsa44_beta : _root_.MLDSA.mldsa44.beta = 78 := mldsa44_vals.2.2.2.2.1

/-- `_root_.MLDSA.mldsa44.omega = 80`. -/
private theorem mldsa44_omega : _root_.MLDSA.mldsa44.omega = 80 := mldsa44_vals.2.2.2.2.2

/-- ML-DSA-44 is an approved parameter set. -/
theorem isApproved_mldsa44 : _root_.MLDSA.mldsa44.isApproved := Or.inl rfl

/-- **The hint fraction bound at ML-DSA-44**: for `|b| ≤ τ 2^12 = 159744`,
`hintFractionBound(b) = max(|b| - 78, 0) / 190307 ≤ 159666/190307 < 21/25`. This holds whether or
not the ct₀-check passes. -/
theorem hintFractionBound_le_mldsa44 {b : ℤ} (hb : |b| ≤ 39 * 4096) :
    hintFractionBound _root_.MLDSA.mldsa44.gamma2 _root_.MLDSA.mldsa44.beta b ≤ 21 / 25 := by
  rw [mldsa44_gamma2, mldsa44_beta, hintFractionBound]
  have h : (|b| - (78 : ℕ)).toNat ≤ 159666 := by
    rw [Int.toNat_le]
    push_cast
    omega
  have h' : (((|b| - (78 : ℕ)).toNat : ℕ) : ℝ) ≤ 159666 := by exact_mod_cast h
  calc (((|b| - (78 : ℕ)).toNat : ℕ) : ℝ) / ((2 * (95232 - 78) - 1 : ℕ) : ℝ)
      ≤ 159666 / ((2 * (95232 - 78) - 1 : ℕ) : ℝ) := by gcongr
    _ ≤ 21 / 25 := by norm_num

/-- **The line value at ML-DSA-44**: the largest of the four lines `α_j π - σ_j m` of
`WeightLines44.lean` (`sub_le_binomialCdf_line_zero_mldsa44` and the others). -/
noncomputable def mldsa44LineValue (pr m : ℝ) : ℝ :=
  max (max (max (1 * pr - 1 / 90 * m) (11675311 / 10 ^ 28 * pr - 8608199 / 10 ^ 30 * m))
    (6150879 / 10 ^ 37 * pr - 40815103 / 10 ^ 40 * m))
    (32703147 / 10 ^ 87 * pr - 14842721 / 10 ^ 89 * m)

/-- The line value is monotone in `π` and antitone in `m`. -/
theorem mldsa44LineValue_mono {pr pr' m m' : ℝ} (hpr : pr ≤ pr') (hm : m' ≤ m) :
    mldsa44LineValue pr m ≤ mldsa44LineValue pr' m' := by
  unfold mldsa44LineValue
  gcongr

/-- The line value at `π = 0` is at most `0` for `m ≥ 0`. -/
theorem mldsa44LineValue_zero_le {m : ℝ} (hm : 0 ≤ m) : mldsa44LineValue 0 m ≤ 0 := by
  unfold mldsa44LineValue
  refine max_le (max_le (max_le ?_ ?_) ?_) ?_ <;> nlinarith

/-- The line `(1, 1/90)` is below the line value. -/
theorem mldsa44_line_zero_le (pr m : ℝ) : 1 * pr - 1 / 90 * m ≤ mldsa44LineValue pr m :=
  le_max_of_le_left (le_max_of_le_left (le_max_left _ _))

/-- The line `(11675311 · 10^-28, 8608199 · 10^-30)` is below the line value. -/
theorem mldsa44_line_one_le (pr m : ℝ) :
    11675311 / 10 ^ 28 * pr - 8608199 / 10 ^ 30 * m ≤ mldsa44LineValue pr m :=
  le_max_of_le_left (le_max_of_le_left (le_max_right _ _))

/-- The line `(6150879 · 10^-37, 40815103 · 10^-40)` is below the line value. -/
theorem mldsa44_line_two_le (pr m : ℝ) :
    6150879 / 10 ^ 37 * pr - 40815103 / 10 ^ 40 * m ≤ mldsa44LineValue pr m :=
  le_max_of_le_left (le_max_right _ _)

/-- The line `(32703147 · 10^-87, 14842721 · 10^-89)` is below the line value. -/
theorem mldsa44_line_three_le (pr m : ℝ) :
    32703147 / 10 ^ 87 * pr - 14842721 / 10 ^ 89 * m ≤ mldsa44LineValue pr m :=
  le_max_right _ _

/-- **The line `(2^-3072, 0)`**: `2^-3072 ≤ Pr[Bin(N, 21/25) ≤ 80]` for `N ≤ 1024`, from the term
`j = 0`, `(4/25)^N ≥ (1/8)^1024`. -/
theorem sub_le_binomialCdf_line_floor_mldsa44 {N : ℕ} (hN : N ≤ 1024) :
    2⁻¹ ^ 3072 - 0 * N * (21 / 25) ≤ binomialCdf (21 / 25) N 80 := by
  have h := choose_mul_pow_mul_pow_le_binomialCdf (x := 21 / 25) (by norm_num) (by norm_num)
    (Nat.zero_le 80) N
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero] at h
  refine le_trans ?_ h
  have h1 : (4 / 25 : ℝ) ^ 1024 ≤ (1 - 21 / 25) ^ N := by
    rw [show (1 : ℝ) - 21 / 25 = 4 / 25 by norm_num]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
  have h2 : (2⁻¹ : ℝ) ^ 3072 ≤ (4 / 25) ^ 1024 := by
    rw [show 3072 = 3 * 1024 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  linarith

variable [nttOps : NTTRingOps]

/-- **The member-weight lower bound at ML-DSA-44 under the oracle `G`**:
`max(mldsa44LineValue(π_G, m_G), 2^-3072 π_G)` with `π_G = 𝔼_c̃ 1[‖G(c̃)·t₀‖∞ < γ₂]` and
`m_G = 𝔼_c̃ hintBoundSum(G(c̃), t₀)` (`mldsa44OracleWeight_le_expect_memberWeight`). -/
noncomputable def mldsa44OracleWeight
    (G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau)
    (t0 : RqVec _root_.MLDSA.mldsa44.k) : ℝ :=
  max (mldsa44LineValue (𝔼 cTilde, ct0Indicator _root_.MLDSA.mldsa44.gamma2 (G cTilde).1 t0)
      (𝔼 cTilde, hintBoundSum _root_.MLDSA.mldsa44.gamma2 _root_.MLDSA.mldsa44.beta (G cTilde).1
          t0))
    (2⁻¹ ^ 3072 * 𝔼 cTilde, ct0Indicator _root_.MLDSA.mldsa44.gamma2 (G cTilde).1 t0)

/-- The weight is nonnegative. -/
theorem mldsa44OracleWeight_nonneg
    (G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau)
    (t0 : RqVec _root_.MLDSA.mldsa44.k) : 0 ≤ mldsa44OracleWeight G t0 :=
  le_max_of_le_right (mul_nonneg (by positivity)
    (Finset.expect_nonneg fun _ _ => ct0Indicator_nonneg _ _ _))

variable [NTTRingLaws nttOps]

/-- **The hint fraction bounds at ML-DSA-44 are at most `21/25`** for `c ∈ B_39` and
`‖t₀‖∞ ≤ 2^12` (`abs_centeredCoeffs_smul_le`, `hintFractionBound_le_mldsa44`). -/
theorem hintFractionBound_centeredCoeffs_le_mldsa44 (c : ChallengeBall _root_.MLDSA.mldsa44.tau)
    (t0 : RqVec _root_.MLDSA.mldsa44.k) (ht0 : polyVecNorm t0 ≤ 4096)
    (x : Fin _root_.MLDSA.mldsa44.k × Fin ringDegree) :
    hintFractionBound _root_.MLDSA.mldsa44.gamma2 _root_.MLDSA.mldsa44.beta
        (centeredCoeffs (c.1 • t0) x) ≤ 21 / 25 := by
  refine hintFractionBound_le_mldsa44 ?_
  have h : |((centeredCoeffs (c.1 • t0) x : ℤ) : ℝ)| ≤ ((39 * 4096 : ℕ) : ℝ) :=
    abs_centeredCoeffs_smul_le c t0 ht0 x
  exact_mod_cast h

/-- `hintBoundSum ∈ [0, 1024 · 21/25]` at ML-DSA-44 for `c ∈ B_39` and `‖t₀‖∞ ≤ 2^12`. -/
theorem hintBoundSum_mem_mldsa44 (c : ChallengeBall _root_.MLDSA.mldsa44.tau)
    (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096) :
    hintBoundSum _root_.MLDSA.mldsa44.gamma2 _root_.MLDSA.mldsa44.beta c.1 t0 ∈ Set.Icc 0
        (1024 * (21 / 25)) := by
  unfold hintBoundSum
  refine ⟨Finset.sum_nonneg fun x _ => hintFractionBound_nonneg _ _ _, ?_⟩
  refine (Finset.sum_le_sum fun x _ =>
    hintFractionBound_centeredCoeffs_le_mldsa44 c t0 ht0 x).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    mldsa44_k, nsmul_eq_mul]
  norm_num [ringDegree]

/-- **The weight bounds the mean member weight at ML-DSA-44**: for `prims` with
`SampleInBall = G`, `β_min ≤ 1`, `‖t₀‖∞ ≤ 2^12` and every bucket vector `v`,
`mldsa44OracleWeight G t₀ ≤ 𝔼_c̃ memberWeight(t₀, (v, c̃))` (`line_le_expect_memberWeight` at the
five lines). -/
theorem mldsa44OracleWeight_le_expect_memberWeight [NeZero (bucketCount _root_.MLDSA.mldsa44)]
    (prims : Primitives _root_.MLDSA.mldsa44)
    (G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau)
    (hG : ∀ cTilde, prims.sampleInBall cTilde = (G cTilde).1) {βmin : ℚ≥0} (hβ : (βmin : ℝ≥0∞) ≤ 1)
    (t0 : RqVec _root_.MLDSA.mldsa44.k) (ht0 : polyVecNorm t0 ≤ 4096)
    (v : BucketVec _root_.MLDSA.mldsa44) :
    mldsa44OracleWeight G t0 ≤ 𝔼 cTilde, (memberWeight prims βmin t0 (v, cTilde) : ℝ≥0∞).toReal :=
      by
  have hp := SigningParams.of_isApproved isApproved_mldsa44
  have hx : ∀ cTilde x, hintFractionBound _root_.MLDSA.mldsa44.gamma2 _root_.MLDSA.mldsa44.beta
      (centeredCoeffs ((G cTilde).1 • t0) x) ≤ 21 / 25 := fun cTilde x =>
    hintFractionBound_centeredCoeffs_le_mldsa44 (G cTilde) t0 ht0 x
  have hk : ∀ N, N ≤ _root_.MLDSA.mldsa44.k * ringDegree → N ≤ 1024 := fun N hN => by
    rw [mldsa44_k] at hN
    simpa [ringDegree] using hN
  have hl := fun {α σ : ℝ} (hσ : 0 ≤ σ)
      (hline : ∀ N ≤ _root_.MLDSA.mldsa44.k * ringDegree, α - σ * N * (21 / 25) ≤
        binomialCdf (21 / 25) N _root_.MLDSA.mldsa44.omega) =>
    line_le_expect_memberWeight hp prims G hG hβ t0 hx hσ hline v
  rw [mldsa44_omega] at hl
  unfold mldsa44OracleWeight mldsa44LineValue
  refine max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_
  · exact hl (by norm_num) fun N _ => sub_le_binomialCdf_line_zero_mldsa44 N
  · exact hl (by norm_num) fun N _ => sub_le_binomialCdf_line_one_mldsa44 N
  · exact hl (by norm_num) fun N _ => sub_le_binomialCdf_line_two_mldsa44 N
  · exact hl (by norm_num) fun N _ => sub_le_binomialCdf_line_three_mldsa44 N
  · have h := hl le_rfl fun N hN => sub_le_binomialCdf_line_floor_mldsa44 (hk N hN)
    simpa using h

omit [NTTRingLaws nttOps] in
/-- **A zero weight means zero member weights**: if `mldsa44OracleWeight G t₀ = 0`, every `c̃`
fails the ct₀-check, so the mean member weight of every bucket vector is `0`
(`toReal_memberWeight_le_ct0Indicator`). -/
theorem expect_memberWeight_eq_zero_of_mldsa44OracleWeight
    [NeZero (bucketCount _root_.MLDSA.mldsa44)]
    (prims : Primitives _root_.MLDSA.mldsa44)
    (G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau)
    (hG : ∀ cTilde, prims.sampleInBall cTilde = (G cTilde).1) (βmin : ℚ≥0)
    (t0 : RqVec _root_.MLDSA.mldsa44.k) (h : mldsa44OracleWeight G t0 = 0)
    (v : BucketVec _root_.MLDSA.mldsa44) :
    𝔼 cTilde, (memberWeight prims βmin t0 (v, cTilde) : ℝ≥0∞).toReal = 0 := by
  have hp0 : 0 ≤ 𝔼 cTilde, ct0Indicator _root_.MLDSA.mldsa44.gamma2 (G cTilde).1 t0 :=
    Finset.expect_nonneg fun _ _ => ct0Indicator_nonneg _ _ _
  have hπ : 𝔼 cTilde, ct0Indicator _root_.MLDSA.mldsa44.gamma2 (G cTilde).1 t0 = 0 := by
    have h1 : 2⁻¹ ^ 3072 * 𝔼 cTilde, ct0Indicator _root_.MLDSA.mldsa44.gamma2 (G cTilde).1 t0 ≤ 0 :=
      h ▸ le_max_right _ _
    have h2 : (0 : ℝ) < 2⁻¹ ^ 3072 := by positivity
    nlinarith
  refine le_antisymm ?_ (Finset.expect_nonneg fun _ _ => ENNReal.toReal_nonneg)
  exact (Finset.expect_le_expect fun cTilde _ =>
    toReal_memberWeight_le_ct0Indicator prims G hG βmin t0 v cTilde).trans hπ.le

omit nttOps [NTTRingLaws nttOps] in
/-- `(e₁ + e₂) · 2^6656 ≤ 2^-1000` for the two Hoeffding tails at `2^256` commitment hashes and
deviation `2^-64`. -/
private theorem hoeffding_tails_mul_le_mldsa44 :
    (exp (-(2 * ((256 ^ (_root_.MLDSA.mldsa44.lambda / 4) : ℕ) : ℝ) * (2⁻¹ ^ 64) ^ 2 / (0 - -1) ^
        2)) +
        exp (-(2 * ((256 ^ (_root_.MLDSA.mldsa44.lambda / 4) : ℕ) : ℝ) * (2⁻¹ ^ 64) ^ 2 /
          (1024 * (21 / 25) - 0) ^ 2))) * 2 ^ 6656 ≤ (2 : ℝ)⁻¹ ^ 1000 := by
  rw [mldsa44_lambda]
  have e1 : exp (-(2 * ((256 ^ (128 / 4) : ℕ) : ℝ) * (2⁻¹ ^ 64) ^ 2 / (0 - -1) ^ 2)) ≤
      2⁻¹ ^ 7657 := exp_le_inv_two_pow_of_le (by norm_num)
  have e2 : exp (-(2 * ((256 ^ (128 / 4) : ℕ) : ℝ) * (2⁻¹ ^ 64) ^ 2 /
      (1024 * (21 / 25) - 0) ^ 2)) ≤ 2⁻¹ ^ 7657 := exp_le_inv_two_pow_of_le (by norm_num)
  have h2 : (2 : ℝ)⁻¹ ^ 7657 * 2 ^ 6656 = 2⁻¹ ^ 1001 := by
    rw [show 7657 = 1001 + 6656 by norm_num, pow_add, mul_assoc, ← mul_pow,
      inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow, mul_one]
  have h3 : (2 : ℝ)⁻¹ ^ 1001 + 2⁻¹ ^ 1001 = 2⁻¹ ^ 1000 := by
    rw [pow_succ, ← two_mul, mul_left_comm, show (2 : ℝ) * 2⁻¹ = 1 by norm_num, mul_one]
  calc _ ≤ ((2 : ℝ)⁻¹ ^ 7657 + 2⁻¹ ^ 7657) * 2 ^ 6656 := by gcongr
    _ = 2⁻¹ ^ 1000 := by rw [add_mul, h2, h3]

/-- **The oracle average of the inverse square weight at ML-DSA-44.** For `G` uniform among the
functions from commitment hashes to `B_39`, `‖t₀‖∞ ≤ 2^12`, `pLow ≤ 𝔼_{c ∈ B_39} 1[‖c·t₀‖∞ < γ₂]`,
`𝔼_c hintBoundSum(c, t₀) ≤ mHi` and `0 < ĝ ≤ mldsa44LineValue(pLow - 2^-64, mHi + 2^-64)`:
`𝔼_G (mldsa44OracleWeight G t₀)⁻² ≤ ĝ⁻² + 2^-1000`. Off the two Hoeffding events (deviation
`2^-64` of `π_G` and of `m_G`, `expect_indicator_le_expect_le`) the weight is at least `ĝ`; on
them it is `0` or at least `2^-3072 · 2^-256`, since `π_G` is a multiple of `2^-256`. -/
theorem expect_inv_sq_mldsa44OracleWeight_le (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    {pLow mHi ĝ : ℝ}
    (hπ : pLow ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hm : 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, hintBoundSum _root_.MLDSA.mldsa44.gamma2
        _root_.MLDSA.mldsa44.beta c.1 t0 ≤ mHi)
    (hg0 : 0 < ĝ) (hg : ĝ ≤ mldsa44LineValue (pLow - 2⁻¹ ^ 64) (mHi + 2⁻¹ ^ 64)) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤ ĝ⁻¹ ^ 2 + 2⁻¹ ^ 1000 := by
  have := challengeBall_nonempty (τ := _root_.MLDSA.mldsa44.tau)
      (by rw [mldsa44_tau]; norm_num [ringDegree])
  set t : ℝ := 2⁻¹ ^ 64 with htdef
  have ht : 0 ≤ t := by positivity
  set N : ℝ := (Fintype.card (CommitHashBytes _root_.MLDSA.mldsa44) : ℝ) with hNdef
  have hN : N = ((256 ^ (_root_.MLDSA.mldsa44.lambda / 4) : ℕ) : ℝ) := by rw
      [hNdef, card_commitHashBytes]
  have hN256 : N = 2 ^ 256 := by rw [hN, mldsa44_lambda]; norm_num
  have hNpos : (0 : ℝ) < N := by rw [hN256]; positivity
  set f₁ : ChallengeBall _root_.MLDSA.mldsa44.tau → ℝ := fun c => -ct0Indicator
      _root_.MLDSA.mldsa44.gamma2 c.1 t0
  set f : ChallengeBall _root_.MLDSA.mldsa44.tau → ℝ := fun c => hintBoundSum
      _root_.MLDSA.mldsa44.gamma2 _root_.MLDSA.mldsa44.beta c.1 t0
  have hf₁ : ∀ c, f₁ c ∈ Set.Icc (-1) 0 := fun c =>
    ⟨neg_le_neg (ct0Indicator_le_one _ _ _), neg_nonpos.2 (ct0Indicator_nonneg _ _ _)⟩
  have hf : ∀ c, f c ∈ Set.Icc 0 (1024 * (21 / 25)) := fun c => hintBoundSum_mem_mldsa44 c t0 ht0
  set A := ĝ⁻¹ ^ 2
  set B : ℝ := 2 ^ 6656
  set I1 : (CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau) → ℝ :=
      fun G =>
    if 𝔼 c, f₁ c + t ≤ 𝔼 cTilde, f₁ (G cTilde) then 1 else 0
  set I2 : (CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau) → ℝ :=
      fun G =>
    if 𝔼 c, f c + t ≤ 𝔼 cTilde, f (G cTilde) then 1 else 0
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hpt : ∀ G, (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤ A + (I1 G + I2 G) * B := fun G => by
    set pG := 𝔼 cTilde, ct0Indicator _root_.MLDSA.mldsa44.gamma2 (G cTilde).1 t0
    set mG := 𝔼 cTilde, hintBoundSum _root_.MLDSA.mldsa44.gamma2 _root_.MLDSA.mldsa44.beta
        (G cTilde).1 t0
    have hw0 := mldsa44OracleWeight_nonneg G t0
    have hpG0 : 0 ≤ pG := Finset.expect_nonneg fun _ _ => ct0Indicator_nonneg _ _ _
    have hmG0 : 0 ≤ mG := Finset.expect_nonneg fun c _ => (hf (G c)).1
    -- On every event the inverse square weight is at most `2^6656`.
    have hwdef : mldsa44OracleWeight G t0 = max (mldsa44LineValue pG mG) (2⁻¹ ^ 3072 * pG) :=
      rfl
    have hbad : (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤ B := by
      rcases hpG0.eq_or_lt with h0 | h0
      · have hw : mldsa44OracleWeight G t0 = 0 := by
          refine le_antisymm ?_ hw0
          rw [hwdef, ← h0, mul_zero]
          exact max_le (mldsa44LineValue_zero_le hmG0) le_rfl
        rw [hw, inv_zero, zero_pow two_ne_zero]
        exact hB
      · have hex : ∃ c₀, ct0Indicator _root_.MLDSA.mldsa44.gamma2 (G c₀).1 t0 ≠ 0 := by
          by_contra hc
          push Not at hc
          have : pG = 0 := by simp [pG, hc]
          linarith
        obtain ⟨c₀, hc₀⟩ := hex
        have hc1 : ct0Indicator _root_.MLDSA.mldsa44.gamma2 (G c₀).1 t0 = 1 :=
          (ct0Indicator_eq_zero_or_eq_one _ _ _).resolve_left hc₀
        have hpN : 1 / N ≤ pG :=
          one_div_card_le_expect (fun cTilde => ct0Indicator_nonneg _ (G cTilde).1 t0) c₀ hc1.ge
        have hlow : 2⁻¹ ^ 3072 * (1 / N) ≤ mldsa44OracleWeight G t0 := by
          rw [hwdef]
          exact le_max_of_le_right (mul_le_mul_of_nonneg_left hpN (by positivity))
        have hpos : (0 : ℝ) < 2⁻¹ ^ 3072 * (1 / N) := by positivity
        calc (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤ (2⁻¹ ^ 3072 * (1 / N))⁻¹ ^ 2 := by
              gcongr
          _ = B := by
              have e : (2⁻¹ ^ 3072 * (1 / N) : ℝ) = 2⁻¹ ^ 3328 := by
                rw [hN256, one_div, ← inv_pow, ← pow_add]
              rw [e, ← inv_pow, inv_inv, ← pow_mul]
    have hI1 : 0 ≤ I1 G := by simp only [I1]; split_ifs <;> norm_num
    have hI2 : 0 ≤ I2 G := by simp only [I2]; split_ifs <;> norm_num
    by_cases h1 : 𝔼 c, f₁ c + t ≤ 𝔼 cTilde, f₁ (G cTilde)
    · have : I1 G = 1 := by simp only [I1, h1, ↓reduceIte]
      rw [this]
      exact hbad.trans (le_add_of_nonneg_of_le hA (le_mul_of_one_le_left hB (by linarith)))
    by_cases h2 : 𝔼 c, f c + t ≤ 𝔼 cTilde, f (G cTilde)
    · have : I2 G = 1 := by simp only [I2, h2, ↓reduceIte]
      rw [this]
      exact hbad.trans (le_add_of_nonneg_of_le hA (le_mul_of_one_le_left hB (by linarith)))
    -- Off both events the weight is at least `ĝ`.
    have hp' : pLow - t ≤ pG := by
      have e1 : 𝔼 c, f₁ c = -𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
          _root_.MLDSA.mldsa44.gamma2 c.1 t0 :=
        by simp only [f₁, Finset.expect_neg_distrib]
      have e2 : 𝔼 cTilde, f₁ (G cTilde) = -pG := by simp only [f₁, pG, Finset.expect_neg_distrib]
      rw [e1, e2] at h1
      linarith
    have hm' : mG ≤ mHi + t := by
      have : mG < 𝔼 c, f c + t := not_le.1 h2
      linarith
    have hgood : ĝ ≤ mldsa44OracleWeight G t0 :=
      hg.trans ((mldsa44LineValue_mono hp' hm').trans ((le_max_left _ _).trans_eq hwdef.symm))
    have : (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤ A := by
      simp only [A]
      gcongr
    exact le_add_of_le_of_nonneg this (mul_nonneg (add_nonneg hI1 hI2) hB)
  have he1 := GordieHowe.expect_indicator_le_expect_le (X := CommitHashBytes _root_.MLDSA.mldsa44)
      f₁ hf₁
    (by norm_num) ht
  have he2 := GordieHowe.expect_indicator_le_expect_le (X := CommitHashBytes _root_.MLDSA.mldsa44) f
      hf
    (by norm_num) ht
  rw [← hNdef, hN] at he1 he2
  calc 𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2
      ≤ 𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          (A + (I1 G + I2 G) * B) :=
        Finset.expect_le_expect fun G _ => hpt G
    _ = A + ((𝔼 G, I1 G) + 𝔼 G, I2 G) * B := by
        rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty,
          ← Finset.expect_mul, Finset.expect_add_distrib]
    _ ≤ A + (exp (-(2 * ((256 ^ (_root_.MLDSA.mldsa44.lambda / 4) : ℕ) : ℝ) * t ^ 2 / (0 - -1) ^ 2))
        +
          exp (-(2 * ((256 ^ (_root_.MLDSA.mldsa44.lambda / 4) : ℕ) : ℝ) * t ^ 2 /
            (1024 * (21 / 25) - 0) ^ 2))) * B := by
        gcongr
    _ ≤ A + 2⁻¹ ^ 1000 := add_le_add le_rfl hoeffding_tails_mul_le_mldsa44

omit nttOps [NTTRingLaws nttOps] in
/-- **`hintMeanBound` at ML-DSA-44 from a lower bound on its exponential term**: for
`elo ≤ exp(-(11/20)(65/100)² u)` at `u = 39 a / 2^34` and
`2^22 (1.83 + 0.104 u - 0.77 elo) / 190307 ≤ ŷ`, `hintMeanBound _root_.MLDSA.mldsa44 a ≤ ŷ`. -/
theorem hintMeanBound_mldsa44_le {a elo ŷ : ℝ}
    (helo : elo ≤ exp (-(11 / 20 * (65 / 100) ^ 2 * (39 * a / 17179869184))))
    (hy : 4194304 * (183 / 100 + 104 / 1000 * (39 * a / 17179869184) - 77 / 100 * elo) / 190307 ≤
      ŷ) :
    hintMeanBound _root_.MLDSA.mldsa44 a ≤ ŷ := by
  have e : hintMeanBound _root_.MLDSA.mldsa44 a =
      4194304 * absMomentBound (39 * a / 17179869184) / 190307 := by
    simp only [hintMeanBound, mldsa44_k, mldsa44_tau, mldsa44_gamma2, mldsa44_beta]
    norm_num [ringDegree]
  rw [e]
  refine le_trans ?_ hy
  unfold absMomentBound
  gcongr

/-- **A level bound at ML-DSA-44 from one line**: for `‖t₀‖∞ ≤ 2^12` with
`1 - Δ ≤ 𝔼_{c ∈ B_39} 1[ct₀ ok]` and `‖t₀‖₂² ≤ a`, a line `(α, σ)` below the line value,
`hintMeanBound _root_.MLDSA.mldsa44 a ≤ ŷ` through `elo` (`hintMeanBound_mldsa44_le`), and
`0 < ĝ ≤ α (1 - Δ - 2^-64) - σ (ŷ + 2^-64)`:
`𝔼_G (mldsa44OracleWeight G t₀)⁻² ≤ U` for `ĝ⁻² + 2^-64 ≤ U`
(`expect_inv_sq_mldsa44OracleWeight_le`). -/
theorem expect_inv_sq_mldsa44OracleWeight_le_of_line (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096) {Δ a elo ŷ ĝ U α σ : ℝ}
    (hΔ : 1 - Δ ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ a) (hline : ∀ pr m, α * pr - σ * m ≤ mldsa44LineValue pr m)
    (helo : elo ≤ exp (-(11 / 20 * (65 / 100) ^ 2 * (39 * a / 17179869184))))
    (hy : 4194304 * (183 / 100 + 104 / 1000 * (39 * a / 17179869184) - 77 / 100 * elo) / 190307 ≤
      ŷ)
    (hg : ĝ ≤ α * (1 - Δ - 2⁻¹ ^ 64) - σ * (ŷ + 2⁻¹ ^ 64)) (hg0 : 0 < ĝ)
    (hU : ĝ⁻¹ ^ 2 + 2⁻¹ ^ 64 ≤ U) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤ U := by
  have h64 : (2⁻¹ : ℝ) ^ 1000 ≤ 2⁻¹ ^ 64 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
  have hm : 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, hintBoundSum _root_.MLDSA.mldsa44.gamma2
      _root_.MLDSA.mldsa44.beta c.1 t0 ≤ ŷ :=
    (expect_hintBoundSum_le_hintMeanBound (by rw [mldsa44_tau]; norm_num [ringDegree])
      (by rw [mldsa44_k]; norm_num) (by rw [mldsa44_tau]; norm_num [modulus]) t0 ht0).trans
      ((monotone_hintMeanBound _root_.MLDSA.mldsa44 hS).trans (hintMeanBound_mldsa44_le helo hy))
  refine (expect_inv_sq_mldsa44OracleWeight_le t0 ht0 hΔ hm hg0
    (hg.trans (hline _ _))).trans (le_trans ?_ hU)
  linarith

/-! ### The ct₀-check and the component norms -/

omit [NTTRingLaws nttOps] in
/-- **The ct₀-check in terms of `ct0Indicator`**: `1 - Δ ≤ 𝔼_{c ∈ B_39} 1[‖c·t₀‖∞ < 95232]`
is a bound on `𝔼_c ct0Indicator _root_.MLDSA.mldsa44.gamma2 c t₀`. -/
theorem one_sub_le_expect_ct0Indicator_mldsa44 {Δ : ℝ} (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (h : 1 - Δ ≤ 𝔼 c : ChallengeBall 39,
      (if ∀ x, |centeredCoeffs (c.1 • t0) x| < 95232 then 1 else 0 : ℝ)) :
    1 - Δ ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator _root_.MLDSA.mldsa44.gamma2
        c.1 t0 := by
  refine h.trans_eq ?_
  simp only [ct0Indicator, mldsa44_gamma2]
  rfl

omit nttOps [NTTRingLaws nttOps] in
/-- The normalized component norms from a strict bound on `‖t₀,m‖₂²`:
`‖t₀,m‖₂² < b · 256 · 4096²` gives `∑_i t₀,m,i² / (256 · 4096²) ≤ b`. -/
theorem sum_div_le_of_t0CompSqNorm_lt {t0 : RqVec _root_.MLDSA.mldsa44.k} {b : ℝ}
    (h : ∀ m, ¬ (b * (256 * 4096 ^ 2) ≤ t0CompSqNorm t0 m)) (m : Fin _root_.MLDSA.mldsa44.k) :
    ∑ i, (centeredVec t0 m i : ℝ) ^ 2 / (256 * 4096 ^ 2) ≤ b := by
  rw [← Finset.sum_div, div_le_iff₀ (by norm_num)]
  exact (not_le.1 (h m)).le

end Weight44

/-! ### The tails over keys and matrices -/

section Tails

attribute [local instance] concreteNTTRingOps

/-- `2η < q` at ML-DSA-44. -/
private theorem two_mul_eta_lt_modulus_mldsa44 : 2 * _root_.MLDSA.mldsa44.eta < modulus := by
  rw [mldsa44_eta]
  norm_num [modulus]

/-- **The tail of `‖t₀‖₂²` at ML-DSA-44 from the joint tail factor**: over uniform box secrets and
a uniform matrix, `Pr[a < ‖t₀‖₂²] ≤ t` for `λ' ≥ 0` and `jointTailBound λ' 0 a 0 ≤ t`
(`expect_expect_indicator_le_t0SqNorm_and_le_t0CompSqNorm_le` with `μ' = 0`, `b = 0`). -/
theorem expect_expect_indicator_lt_t0SqNorm_le_mldsa44 (sk : SecretKey _root_.MLDSA.mldsa44)
    {lam a t : ℝ}
    (hlam : 0 ≤ lam) (h : jointTailBound _root_.MLDSA.mldsa44 lam 0 a 0 ≤ t) :
    𝔼 e : SecretCoeffs _root_.MLDSA.mldsa44, 𝔼 aHat : TqMatrix _root_.MLDSA.mldsa44.k
        _root_.MLDSA.mldsa44.l,
        (if a < t0SqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 then 1 else 0 : ℝ) ≤ t
              := by
  have hm : ∀ t0 : RqVec _root_.MLDSA.mldsa44.k, 0 ≤ t0CompSqNorm t0
      ⟨0, by rw [mldsa44_k]; norm_num⟩ :=
    fun t0 => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine le_trans (Finset.expect_le_expect fun e _ => Finset.expect_le_expect fun aHat _ => ?_)
    ((expect_expect_indicator_le_t0SqNorm_and_le_t0CompSqNorm_le sk
      two_mul_eta_lt_modulus_mldsa44 ⟨0, by rw [mldsa44_k]; norm_num⟩ hlam le_rfl a 0).trans h)
  by_cases h1 : a < t0SqNorm (keyOf (keyOfCoeffs sk e)
      (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0
  · rw [if_pos h1, if_pos ⟨h1.le, hm _⟩]
  · rw [if_neg h1]
    split_ifs <;> norm_num

/-- **The joint tail of `‖t₀‖₂²` and the largest component at ML-DSA-44 from the joint tail
factor**: over uniform box secrets and a uniform matrix,
`Pr[∃ m, b ≤ ‖t₀,m‖₂², a < ‖t₀‖₂²] ≤ 4 t` for `λ', μ' ≥ 0` and `jointTailBound λ' μ' a b ≤ t`
(`expect_expect_indicator_le_t0SqNorm_and_exists_le_t0CompSqNorm_le`). -/
theorem expect_expect_indicator_exists_and_lt_le_mldsa44 (sk : SecretKey _root_.MLDSA.mldsa44)
    {lam mu a b t : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (h : jointTailBound _root_.MLDSA.mldsa44 lam mu a b ≤ t) :
    𝔼 e : SecretCoeffs _root_.MLDSA.mldsa44, 𝔼 aHat : TqMatrix _root_.MLDSA.mldsa44.k
        _root_.MLDSA.mldsa44.l,
        (if (∃ m, b ≤ t0CompSqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 m) ∧ a < t0SqNorm
              (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 then 1 else 0 : ℝ) ≤ 4
              * t := by
  refine le_trans (Finset.expect_le_expect fun e _ => Finset.expect_le_expect fun aHat _ => ?_)
    ((expect_expect_indicator_le_t0SqNorm_and_exists_le_t0CompSqNorm_le sk
      two_mul_eta_lt_modulus_mldsa44 hlam hmu a b).trans ?_)
  · split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨h1.2.le, h1.1⟩ h2
    all_goals norm_num
  · rw [mldsa44_k, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- **The tail of the largest component at ML-DSA-44 from the joint tail factor**:
`Pr[∃ m, b ≤ ‖t₀,m‖₂²] ≤ 4 t` for `μ' ≥ 0` and `jointTailBound 0 μ' 0 b ≤ t`. -/
theorem expect_expect_indicator_exists_le_mldsa44 (sk : SecretKey _root_.MLDSA.mldsa44) {mu b t : ℝ}
    (hmu : 0 ≤ mu) (h : jointTailBound _root_.MLDSA.mldsa44 0 mu 0 b ≤ t) :
    𝔼 e : SecretCoeffs _root_.MLDSA.mldsa44, 𝔼 aHat : TqMatrix _root_.MLDSA.mldsa44.k
        _root_.MLDSA.mldsa44.l,
        (if ∃ m, b ≤ t0CompSqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 m then 1 else 0 : ℝ) ≤
              4 * t := by
  refine le_trans (Finset.expect_le_expect fun e _ => Finset.expect_le_expect fun aHat _ => ?_)
    ((expect_expect_indicator_le_t0SqNorm_and_exists_le_t0CompSqNorm_le sk
      two_mul_eta_lt_modulus_mldsa44 le_rfl hmu 0 b).trans ?_)
  · have h0 : 0 ≤ t0SqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 := Finset.sum_nonneg
              fun _ _ => sq_nonneg _
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨h0, h1⟩ h2
    all_goals norm_num
  · rw [mldsa44_k, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left h (by norm_num)

end Tails

/-! ### The layered average at ML-DSA-44 -/

section Layers

attribute [local instance] concreteNTTRingOps

/-- The grid of layer `0` (values of `‖t₀‖₂²`; the last is `256 k 4096²`). -/
noncomputable def mldsa44Grid0 : ℕ → ℝ
  | 0 => 5841155523
  | 1 => 5927054868
  | 2 => 5970004541
  | 3 => 6012954214
  | 4 => 6098853560
  | 5 => 6227702579
  | 6 => 6485400617
  | 7 => 8375186227
  | 8 => 17179869184
  | _ => 17179869184

/-- The level bounds `U_i` of layer `0`. -/
noncomputable def mldsa44Level0 : ℕ → ℝ
  | 0 => 31687331 / 1562500
  | 1 => 532337887 / 25000000
  | 2 => 2182775637 / 100000000
  | 3 => 279768487 / 12500000
  | 4 => 2355129423 / 100000000
  | 5 => 509566957 / 20000000
  | 6 => 3008448143 / 100000000
  | 7 => 2089963669 / 10000000
  | 8 => (4004908832 * 10 ^ 35)
  | _ => (4004908832 * 10 ^ 35)

/-- Upper bounds on the joint tail factors of layer `0`. -/
noncomputable def mldsa44TailFactor0 : ℕ → ℝ
  | 0 => 8437273143 / 10000000000
  | 1 => 2727036781 / 5000000000
  | 2 => 1270769 / 3200000
  | 3 => 2⁻¹ ^ 1 * (2705987397 / 5000000000)
  | 4 => 2⁻¹ ^ 3 * (8269472097 / 10000000000)
  | 5 => 2⁻¹ ^ 6 * (9631458709 / 10000000000)
  | 6 => 2⁻¹ ^ 14 * (1917238537 / 2000000000)
  | 7 => 2⁻¹ ^ 161 * (7221481869 / 10000000000)
  | _ => 0

/-- Upper bounds on the terms of layer `0` (the first is the term at `U_0`). -/
noncomputable def mldsa44LayerTerm0 : ℕ → ℝ
  | 0 => 31687331 / 1562500
  | 1 => 21380549 / 25000000
  | 2 => 7284473 / 25000000
  | 3 => 5497293 / 25000000
  | 4 => 15827527 / 50000000
  | 5 => 9959823 / 50000000
  | 6 => 13863683 / 200000000
  | 7 => 10468041 / 1000000000
  | 8 => 19788809 / 200000000000
  | _ => 0

/-- The grid of layer `1` (values of `‖t₀‖₂²`; the last is `256 k 4096²`). -/
noncomputable def mldsa44Grid1 : ℕ → ℝ
  | 0 => 8675833938
  | 1 => 17179869184
  | _ => 17179869184

/-- The level bounds `U_i` of layer `1`. -/
noncomputable def mldsa44Level1 : ℕ → ℝ
  | 0 => 6185922463 / 10000000
  | 1 => (7370340268 * 10 ^ 35)
  | _ => (7370340268 * 10 ^ 35)

/-- Upper bounds on the joint tail factors of layer `1`. -/
noncomputable def mldsa44TailFactor1 : ℕ → ℝ
  | 0 => 2⁻¹ ^ 197 * (74980981 / 100000000)
  | _ => 0

/-- Upper bounds on the terms of layer `1` (the first is the term at `U_0`). -/
noncomputable def mldsa44LayerTerm1 : ℕ → ℝ
  | 0 => 10710927 / 10000000000000000000
  | 1 => 11004987 / 10 ^ 21
  | _ => 0

/-- The grid of layer `2` (values of `‖t₀‖₂²`; the last is `256 k 4096²`). -/
noncomputable def mldsa44Grid2 : ℕ → ℝ
  | 0 => 7215545057
  | 1 => 7344394076
  | 2 => 7602092114
  | 3 => 8675833938
  | 4 => 10952166605
  | 5 => 17179869184
  | _ => 17179869184

/-- The level bounds `U_i` of layer `2`. -/
noncomputable def mldsa44Level2 : ℕ → ℝ
  | 0 => (1107433173 * 10 ^ 35)
  | 1 => (1261304599 * 10 ^ 35)
  | 2 => (1681700153 * 10 ^ 35)
  | 3 => (128717359 * 10 ^ 37)
  | 4 => (4875420533 * 10 ^ 55)
  | 5 => (228034682 * 10 ^ 153)
  | _ => (228034682 * 10 ^ 153)

/-- Upper bounds on the joint tail factors of layer `2`. -/
noncomputable def mldsa44TailFactor2 : ℕ → ℝ
  | 0 => 2⁻¹ ^ 150 * (3790191193 / 5000000000)
  | 1 => 2⁻¹ ^ 152 * (3344267771 / 5000000000)
  | 2 => 2⁻¹ ^ 159 * (5026452567 / 10000000000)
  | 3 => 2⁻¹ ^ 230 * (7895066771 / 10000000000)
  | 4 => 2⁻¹ ^ 256 * (2⁻¹ ^ 256 * (2⁻¹ ^ 40 * (3206148191 / 5000000000)))
  | _ => 0

/-- Upper bounds on the terms of layer `2` (the first is the term at `U_0`). -/
noncomputable def mldsa44LayerTerm2 : ℕ → ℝ
  | 0 => 713821 / 1250000
  | 1 => 3268961 / 100000000
  | 2 => 1970107 / 100000000
  | 3 => 30788161 / 10000000000
  | 4 => 2788553 / 31250000000
  | 5 => 7934999 / 200000000000
  | _ => 0

/-- Level `0` of layer `0`: `𝔼_G w⁻² ≤ 2.027989e+01` for `‖t₀‖₂² ≤ 5841155523` and ct₀ failure
at most `3 / 4000` (the line `zero`). -/
private theorem mldsa44_level0_le_0 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 3 / 4000 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 5841155523) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      31687331 / 1562500 := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (680340709759 / 1000000000000) ^ 8)
    (ŷ := 34973622539 / 500000000) (ĝ := 55514597 / 250000000) hΔ hS mldsa44_line_zero_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `1` of layer `0`: `𝔼_G w⁻² ≤ 2.129352e+01` for `‖t₀‖₂² ≤ 5927054868` and ct₀ failure
at most `3 / 4000` (the line `zero`). -/
private theorem mldsa44_level0_le_1 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 3 / 4000 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 5927054868) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      532337887 / 25000000 := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (338249028641 / 500000000000) ^ 8)
    (ŷ := 563429747 / 8000000) (ĝ := 2167086847 / 10000000000) hΔ hS mldsa44_line_zero_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `2` of layer `0`: `𝔼_G w⁻² ≤ 2.182776e+01` for `‖t₀‖₂² ≤ 5970004541` and ct₀ failure
at most `3 / 4000` (the line `zero`). -/
private theorem mldsa44_level0_le_2 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 3 / 4000 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 5970004541) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      2182775637 / 100000000 := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (84323109703 / 125000000000) ^ 8)
    (ŷ := 70668877421 / 1000000000) (ĝ := 535100627 / 2500000000) hΔ hS mldsa44_line_zero_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `3` of layer `0`: `𝔼_G w⁻² ≤ 2.238148e+01` for `‖t₀‖₂² ≤ 6012954214` and ct₀ failure
at most `3 / 4000` (the line `zero`). -/
private theorem mldsa44_level0_le_3 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 3 / 4000 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 6012954214) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      279768487 / 12500000 := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (672677108561 / 1000000000000) ^ 8)
    (ŷ := 70908662877 / 1000000000) (ĝ := 6605499 / 31250000) hΔ hS mldsa44_line_zero_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `4` of layer `0`: `𝔼_G w⁻² ≤ 2.355129e+01` for `‖t₀‖₂² ≤ 6098853560` and ct₀ failure
at most `3 / 4000` (the line `zero`). -/
private theorem mldsa44_level0_le_4 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 3 / 4000 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 6098853560) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      2355129423 / 100000000 := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (668877741053 / 1000000000000) ^ 8)
    (ŷ := 17846786577 / 250000000) (ĝ := 1030297427 / 5000000000) hΔ hS mldsa44_line_zero_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `5` of layer `0`: `𝔼_G w⁻² ≤ 2.547835e+01` for `‖t₀‖₂² ≤ 6227702579` and ct₀ failure
at most `3 / 4000` (the line `zero`). -/
private theorem mldsa44_level0_le_5 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 3 / 4000 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 6227702579) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      509566957 / 20000000 := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (663218888113 / 1000000000000) ^ 8)
    (ŷ := 72102272751 / 1000000000) (ĝ := 49528409 / 250000000) hΔ hS mldsa44_line_zero_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `6` of layer `0`: `𝔼_G w⁻² ≤ 3.008448e+01` for `‖t₀‖₂² ≤ 6485400617` and ct₀ failure
at most `3 / 4000` (the line `zero`). -/
private theorem mldsa44_level0_le_6 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 3 / 4000 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 6485400617) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      3008448143 / 100000000 := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0 (elo := (10188193791 / 15625000000) ^ 8)
    (ŷ := 9190488839 / 125000000) (ĝ := 1823176587 / 10000000000) hΔ hS mldsa44_line_zero_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `7` of layer `0`: `𝔼_G w⁻² ≤ 2.089964e+02` for `‖t₀‖₂² ≤ 8375186227` and ct₀ failure
at most `3 / 4000` (the line `zero`). -/
private theorem mldsa44_level0_le_7 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 3 / 4000 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 8375186227) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      2089963669 / 10000000 := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (115130199283 / 200000000000) ^ 8)
    (ŷ := 41853507857 / 500000000) (ĝ := 3458602381 / 50000000000) hΔ hS mldsa44_line_zero_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `8` of layer `0`: `𝔼_G w⁻² ≤ 4.004909e+44` for `‖t₀‖₂² ≤ 17179869184` and ct₀ failure
at most `3 / 4000` (the line `one`). -/
private theorem mldsa44_level0_le_8 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 3 / 4000 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 17179869184) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      (4004908832 * 10 ^ 35) := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (283778508979 / 500000000000) ^ 16)
    (ŷ := 129723546547 / 1000000000) (ĝ := 4996934801 / 10 ^ 32) hΔ hS mldsa44_line_one_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The joint tail factor of layer `0` at grid point `0`. -/
private theorem mldsa44_tail0_le_0 :
    jointTailBound _root_.MLDSA.mldsa44 (3 / 50) (0) 5841155523 (0) ≤
      8437273143 / 10000000000 := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 251882048861 / 250000000000)
      (Eh := 201505639089 / 200000000000)
    (r := 10082481 / 500000000) (ρ := 520319547359 / 500000000000)
    (El' := 251882048861 / 250000000000)
    (Eh' := 201505639089 / 200000000000) (r' := 10082481 / 500000000)
    (ρ' := 520319547359 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 510184824181 / 500000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 510184824181 / 500000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(42481481 / 250000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- The joint tail factor of layer `0` at grid point `1`. -/
private theorem mldsa44_tail0_le_1 :
    jointTailBound _root_.MLDSA.mldsa44 (11 / 100) (0) 5927054868 (0) ≤
      2727036781 / 5000000000 := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 1013844966011 / 1000000000000)
      (Eh := 253461241503 / 250000000000)
    (r := 18611411 / 500000000) (ρ := 107549086811 / 100000000000)
    (El' := 1013844966011 / 1000000000000)
    (Eh' := 253461241503 / 250000000000) (r' := 18611411 / 500000000)
    (ρ' := 107549086811 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 518962133717 / 500000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 518962133717 / 500000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(606222321 / 1000000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- The joint tail factor of layer `0` at grid point `2`. -/
private theorem mldsa44_tail0_le_2 :
    jointTailBound _root_.MLDSA.mldsa44 (7 / 50) (0) 5970004541 (0) ≤
      1270769 / 3200000 := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 20353080443 / 20000000000)
      (Eh := 1017654022151 / 1000000000000)
    (r := 47569183 / 1000000000) (ρ := 1096837257497 / 1000000000000)
    (El' := 20353080443 / 20000000000)
    (Eh' := 1017654022151 / 1000000000000) (r' := 47569183 / 1000000000)
    (ρ' := 1096837257497 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 1048718752121 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 1048718752121 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(923528581 / 1000000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- The joint tail factor of layer `0` at grid point `3`. -/
private theorem mldsa44_tail0_le_3 :
    jointTailBound _root_.MLDSA.mldsa44 (4 / 25) (0) 6012954214 (0) ≤
      2⁻¹ ^ 1 * (2705987397 / 5000000000) := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 510100670013 / 500000000000)
      (Eh := 1020201340027 / 1000000000000)
    (r := 54513547 / 1000000000) (ρ := 277812762839 / 250000000000)
    (El' := 510100670013 / 500000000000)
    (Eh' := 1020201340027 / 1000000000000) (r' := 54513547 / 1000000000)
    (ρ' := 277812762839 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 1056026782311 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 1056026782311 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(1307118221 / 1000000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  refine exp_le_inv_two_pow_mul_of_exp_add_le 1 ?_
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- The joint tail factor of layer `0` at grid point `4`. -/
private theorem mldsa44_tail0_le_4 :
    jointTailBound _root_.MLDSA.mldsa44 (21 / 100) (0) 6098853560 (0) ≤
      2⁻¹ ^ 3 * (8269472097 / 10000000000) := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 513298782893 / 500000000000)
      (Eh := 1026597565787 / 1000000000000)
    (r := 36019577 / 500000000) (ρ := 573965301939 / 500000000000)
    (El' := 513298782893 / 500000000000)
    (Eh' := 1026597565787 / 1000000000000) (r' := 36019577 / 500000000)
    (ρ' := 573965301939 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 537348710971 / 500000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 537348710971 / 500000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(1134727981 / 500000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  refine exp_le_inv_two_pow_mul_of_exp_add_le 3 ?_
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- The joint tail factor of layer `0` at grid point `5`. -/
private theorem mldsa44_tail0_le_5 :
    jointTailBound _root_.MLDSA.mldsa44 (29 / 100) (0) 6227702579 (0) ≤
      2⁻¹ ^ 6 * (9631458709 / 10000000000) := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 20738300857 / 20000000000)
      (Eh := 1036915042851 / 1000000000000)
    (r := 10057357 / 100000000) (ρ := 1208556208047 / 1000000000000)
    (El' := 20738300857 / 20000000000)
    (Eh' := 1036915042851 / 1000000000000) (r' := 10057357 / 100000000)
    (ρ' := 1208556208047 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 69112812049 / 62500000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 69112812049 / 62500000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(262277093 / 62500000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  refine exp_le_inv_two_pow_mul_of_exp_add_le 6 ?_
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- The joint tail factor of layer `0` at grid point `6`. -/
private theorem mldsa44_tail0_le_6 :
    jointTailBound _root_.MLDSA.mldsa44 (43 / 100) (0) 6485400617 (0) ≤
      2⁻¹ ^ 14 * (1917238537 / 2000000000) := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 211044152797 / 200000000000)
      (Eh := 527610381993 / 500000000000)
    (r := 15199089 / 100000000) (ρ := 1320498227819 / 1000000000000)
    (El' := 211044152797 / 200000000000)
    (Eh' := 527610381993 / 500000000000) (r' := 15199089 / 100000000)
    (ρ' := 1320498227819 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 58207481549 / 50000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 58207481549 / 50000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(9746321823 / 1000000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  refine exp_le_inv_two_pow_mul_of_exp_add_le 14 ?_
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- The joint tail factor of layer `0` at grid point `7`. -/
private theorem mldsa44_tail0_le_7 :
    jointTailBound _root_.MLDSA.mldsa44 (67 / 50) (0) 8375186227 (0) ≤
      2⁻¹ ^ 161 * (7221481869 / 10000000000) := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 147793161273 / 125000000000)
      (Eh := 236469058037 / 200000000000)
    (r := 133578031 / 250000000) (ρ := 279779449893 / 125000000000)
    (El' := 147793161273 / 125000000000)
    (Eh' := 236469058037 / 200000000000) (r' := 133578031 / 250000000)
    (ρ' := 279779449893 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 853137066727 / 500000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 853137066727 / 500000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(4476888841 / 40000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  refine exp_le_inv_two_pow_mul_of_exp_add_le 161 ?_
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- Level `0` of layer `1`: `𝔼_G w⁻² ≤ 6.185922e+02` for `‖t₀‖₂² ≤ 8675833938` and ct₀ failure
at most `3 / 250` (the line `zero`). -/
private theorem mldsa44_level1_le_0 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 3 / 250 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 8675833938) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      6185922463 / 10000000 := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (141087845587 / 250000000000) ^ 8)
    (ŷ := 5331337659 / 62500000) (ĝ := 4020663839 / 100000000000) hΔ hS mldsa44_line_zero_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `1` of layer `1`: `𝔼_G w⁻² ≤ 7.370340e+44` for `‖t₀‖₂² ≤ 17179869184` and ct₀ failure
at most `3 / 250` (the line `one`). -/
private theorem mldsa44_level1_le_1 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 3 / 250 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 17179869184) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      (7370340268 * 10 ^ 35) := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (283778508979 / 500000000000) ^ 16)
    (ŷ := 129723546547 / 1000000000) (ĝ := 3683462313 / 10 ^ 32) hΔ hS mldsa44_line_one_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The joint tail factor of layer `1` at grid point `0`. -/
private theorem mldsa44_tail1_le_0 :
    jointTailBound _root_.MLDSA.mldsa44 (73 / 50) (0) 8675833938 (1 / 2 * (256 * 4096 ^ 2)) ≤
      2⁻¹ ^ 197 * (74980981 / 100000000) := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 1200214150953 / 1000000000000)
      (Eh := 600107075477 / 500000000000)
    (r := 591144631 / 1000000000) (ρ := 2384180285463 / 1000000000000)
    (El' := 1200214150953 / 1000000000000)
    (Eh' := 600107075477 / 500000000000) (r' := 591144631 / 1000000000)
    (ρ' := 2384180285463 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 1806054498687 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 1806054498687 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(136837930309 / 1000000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  refine exp_le_inv_two_pow_mul_of_exp_add_le 197 ?_
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- The tail factor of the largest component at layer `1`. -/
private theorem mldsa44_tailP1_le :
    jointTailBound _root_.MLDSA.mldsa44 (0) (163 / 100) 0 (1 / 2 * (256 * 4096 ^ 2)) ≤
      2⁻¹ ^ 51 * (9747479793 / 10000000000) := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 1) (Eh := 1)
    (r := 0) (ρ := 1) (El' := 306497904309 / 250000000000)
    (Eh' := 1225991617237 / 1000000000000) (r' := 67425119 / 100000000)
    (ρ' := 2600617222497 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 1)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 490640709733 / 250000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(7075216509 / 200000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  refine exp_le_inv_two_pow_mul_of_exp_add_le 51 ?_
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- Level `0` of layer `2`: `𝔼_G w⁻² ≤ 1.107433e+44` for `‖t₀‖₂² ≤ 7215545057` and ct₀ failure
at most `217 / 625` (the line `one`). -/
private theorem mldsa44_level2_le_0 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 217 / 625 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 7215545057) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      (1107433173 * 10 ^ 35) := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (62139532059 / 100000000000) ^ 8)
    (ŷ := 77500365343 / 1000000000) (ĝ := 9502573463 / 10 ^ 32) hΔ hS mldsa44_line_one_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `1` of layer `2`: `𝔼_G w⁻² ≤ 1.261305e+44` for `‖t₀‖₂² ≤ 7344394076` and ct₀ failure
at most `217 / 625` (the line `one`). -/
private theorem mldsa44_level2_le_1 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 217 / 625 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 7344394076) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      (1261304599 * 10 ^ 35) := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (616138179381 / 1000000000000) ^ 8)
    (ŷ := 78195602337 / 1000000000) (ĝ := 8904099623 / 10 ^ 32) hΔ hS mldsa44_line_one_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `2` of layer `2`: `𝔼_G w⁻² ≤ 1.681700e+44` for `‖t₀‖₂² ≤ 7602092114` and ct₀ failure
at most `217 / 625` (the line `one`). -/
private theorem mldsa44_level2_le_2 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 217 / 625 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 7602092114) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      (1681700153 * 10 ^ 35) := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (121151390079 / 200000000000) ^ 8)
    (ŷ := 79581296397 / 1000000000) (ĝ := 7711266601 / 10 ^ 32) hΔ hS mldsa44_line_one_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `3` of layer `2`: `𝔼_G w⁻² ≤ 1.287174e+45` for `‖t₀‖₂² ≤ 8675833938` and ct₀ failure
at most `217 / 625` (the line `one`). -/
private theorem mldsa44_level2_le_3 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 217 / 625 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 8675833938) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      (128717359 * 10 ^ 37) := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (141087845587 / 250000000000) ^ 8)
    (ŷ := 5331337659 / 62500000) (ĝ := 13936427 / 500000000000000000000000000000) hΔ hS
        mldsa44_line_one_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `4` of layer `2`: `𝔼_G w⁻² ≤ 4.875421e+64` for `‖t₀‖₂² ≤ 10952166605` and ct₀ failure
at most `217 / 625` (the line `two`). -/
private theorem mldsa44_level2_le_4 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 217 / 625 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 10952166605) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      (4875420533 * 10 ^ 55) := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (485693297351 / 1000000000000) ^ 8)
    (ŷ := 97268030493 / 1000000000) (ĝ := 2264456401 / 500000000000000000000000000000000000000000)
        hΔ hS mldsa44_line_two_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level `5` of layer `2`: `𝔼_G w⁻² ≤ 2.280347e+161` for `‖t₀‖₂² ≤ 17179869184` and ct₀ failure
at most `217 / 625` (the line `three`). -/
private theorem mldsa44_level2_le_5 (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096)
    (hΔ : 1 - 217 / 625 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
        _root_.MLDSA.mldsa44.gamma2 c.1 t0)
    (hS : t0SqNorm t0 ≤ 17179869184) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
      (228034682 * 10 ^ 153) := by
  have := concreteNTTRingLaws
  exact expect_inv_sq_mldsa44OracleWeight_le_of_line t0 ht0
      (elo := (283778508979 / 500000000000) ^ 16)
    (ŷ := 129723546547 / 1000000000)
    (ĝ := 523527569 /
        250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
            hΔ hS mldsa44_line_three_le
    (pow_le_exp_of_le_exp_div (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num)
      (by norm_num [abs_le]) (by norm_num [abs_le, Finset.sum_range_succ, Nat.factorial])))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The joint tail factor of layer `2` at grid point `0`. -/
private theorem mldsa44_tail2_le_0 :
    jointTailBound _root_.MLDSA.mldsa44 (3 / 20) (133 / 50) 7215545057 (31 / 50 * (256 * 4096 ^ 2))
        ≤
      2⁻¹ ^ 150 * (3790191193 / 5000000000) := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 254731721263 / 250000000000)
      (Eh := 1018926885053 / 1000000000000)
    (r := 2041467 / 40000000) (ρ := 1104025809443 / 1000000000000)
    (El' := 1420842492137 / 1000000000000)
    (Eh' := 710421246069 / 500000000000) (r' := 1333037309 / 1000000000)
    (ρ' := 2189811596793 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 1052361487933 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 2) (r := 1947445774053 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(13031137321 / 125000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  refine exp_le_inv_two_pow_mul_of_exp_add_le 150 ?_
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- The joint tail factor of layer `2` at grid point `1`. -/
private theorem mldsa44_tail2_le_1 :
    jointTailBound _root_.MLDSA.mldsa44 (6 / 25) (64 / 25) 7344394076 (31 / 50 * (256 * 4096 ^ 2)) ≤
      2⁻¹ ^ 152 * (3344267771 / 5000000000) := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 1030454533953 / 1000000000000)
      (Eh := 515227266977 / 500000000000)
    (r := 41334041 / 500000000) (ρ := 1170384021157 / 1000000000000)
    (El' := 1419067548593 / 1000000000000)
    (Eh' := 709533774297 / 500000000000) (r' := 53075097 / 40000000)
    (ρ' := 2181418590361 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 1086181225609 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 2) (r := 970728490661 / 500000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(105760561627 / 1000000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  refine exp_le_inv_two_pow_mul_of_exp_add_le 152 ?_
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- The joint tail factor of layer `2` at grid point `2`. -/
private theorem mldsa44_tail2_le_2 :
    jointTailBound _root_.MLDSA.mldsa44 (21 / 50) (59 / 25) 7602092114 (31 / 50 * (256 * 4096 ^ 2))
        ≤
      2⁻¹ ^ 159 * (5026452567 / 10000000000) := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 526951281039 / 500000000000)
      (Eh := 1053902562079 / 1000000000000)
    (r := 29651003 / 200000000) (ρ := 1312252315433 / 1000000000000)
    (El' := 707762155307 / 500000000000)
    (Eh' := 283104862123 / 200000000000) (r' := 1314585731 / 1000000000)
    (ρ' := 432933638067 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 4639234509 / 4000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 2) (r := 1929561674567 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(2772456809 / 25000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  refine exp_le_inv_two_pow_mul_of_exp_add_le 159 ?_
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- The joint tail factor of layer `2` at grid point `3`. -/
private theorem mldsa44_tail2_le_3 :
    jointTailBound _root_.MLDSA.mldsa44 (109 / 100) (39 / 25) 8675833938
        (31 / 50 * (256 * 4096 ^ 2)) ≤
      2⁻¹ ^ 230 * (7895066771 / 10000000000) := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 1145968349873 / 1000000000000)
      (Eh := 572984174937 / 500000000000)
    (r := 105191997 / 250000000) (ρ := 97636853349 / 50000000000)
    (El' := 1392707925771 / 1000000000000)
    (Eh' := 348176981443 / 250000000000) (r' := 617805097 / 500000000)
    (ρ' := 4113975377751 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 60925234111 / 40000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 2) (r := 1854852349621 / 1000000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(39915049643 / 250000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  refine exp_le_inv_two_pow_mul_of_exp_add_le 230 ?_
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- The joint tail factor of layer `2` at grid point `4`. -/
private theorem mldsa44_tail2_le_4 :
    jointTailBound _root_.MLDSA.mldsa44 (221 / 100) (0) 10952166605 (31 / 50 * (256 * 4096 ^ 2)) ≤
      2⁻¹ ^ 256 * (2⁻¹ ^ 256 * (2⁻¹ ^ 40 * (3206148191 / 5000000000))) := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 1318177367179 / 1000000000000)
      (Eh := 65908868359 / 50000000000)
    (r := 490249899 / 500000000) (ρ := 341952004299 / 100000000000)
    (El' := 1318177367179 / 1000000000000)
    (Eh' := 65908868359 / 50000000000) (r' := 490249899 / 500000000)
    (ρ' := 341952004299 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 533157652931 / 200000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 533157652931 / 200000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(191530805719 / 500000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  refine (exp_le_inv_two_pow_mul_of_exp_add_le (r := 3206148191 / 5000000000) 552 ?_).trans_eq ?_
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
      (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])
  · rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]

/-- The tail factor of the largest component at layer `2`. -/
private theorem mldsa44_tailP2_le :
    jointTailBound _root_.MLDSA.mldsa44 (0) (141 / 50) 0 (31 / 50 * (256 * 4096 ^ 2)) ≤
      2⁻¹ ^ 149 * (4599823217 / 5000000000) := by
  refine (jointTailBound_le_exp _root_.MLDSA.mldsa44 (El := 1) (Eh := 1)
    (r := 0) (ρ := 1) (El' := 355654913937 / 250000000000)
    (Eh' := 1422619655749 / 1000000000000) (r' := 10462551 / 7812500)
    (ρ' := 879286548799 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num [t0ChordPoly]) (by norm_num) ?_
        ?_
    ?_ (by norm_num [t0ChordPoly])).trans ?_
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 1) (r := 1)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  · exact le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])
  · refine le_trans ?_ (pow_le_exp_of_le_exp_div (m := 2) (r := 390692431623 / 200000000000)
      (by norm_num) (by norm_num) (le_exp_of_le_taylor 14 (by norm_num) (by norm_num [abs_le])
        (by norm_num [abs_le, abs_of_nonneg, Finset.sum_range_succ, Nat.factorial])))
    norm_num [t0ChordPoly]
  refine (exp_le_exp (y := (-(5168117499 / 50000000)))).2 ?_ |>.trans ?_
  · simp only [mldsa44_k, mldsa44_l, mldsa44_eta]
    norm_num [ringDegree]
  refine exp_le_inv_two_pow_mul_of_exp_add_le 149 ?_
  exact exp_le_of_taylor_le 14 (by norm_num) (by norm_num [abs_le])
    (by norm_num [abs_le, abs_of_nonpos, Finset.sum_range_succ, Nat.factorial])

/-- **The key, matrix and oracle average of the inverse square weight at ML-DSA-44**: for uniform
box secrets `e`, a uniform matrix `Â` and `G` uniform among the functions from commitment hashes
to `B_39`, `𝔼_{e, Â, G} (mldsa44OracleWeight G t₀)⁻² ≤ (24/5)²`. Three layers by the largest
component norm (ct₀ failure at most `3/4000`, `3/250` and `217/625`), each a layer cake in
`‖t₀‖₂²` (`le_add_sum_layers_of_imp`, `expect_expect_indicator_mul_layers_le`) with the level
bounds `mldsa44Level0`, `mldsa44Level1`, `mldsa44Level2` and the joint tail factors
`mldsa44TailFactor0`, `mldsa44TailFactor1`, `mldsa44TailFactor2`. -/
theorem expect_expect_expect_inv_sq_mldsa44OracleWeight_le (sk : SecretKey _root_.MLDSA.mldsa44) :
    𝔼 e : SecretCoeffs _root_.MLDSA.mldsa44, 𝔼 aHat : TqMatrix _root_.MLDSA.mldsa44.k
        _root_.MLDSA.mldsa44.l,
      𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (mldsa44OracleWeight G (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0)⁻¹ ^ 2 ≤ (24 / 5) ^ 2
              := by
  have := concreteNTTRingLaws
  have hlev0 : ∀ t0 : RqVec _root_.MLDSA.mldsa44.k, polyVecNorm t0 ≤ 4096 →
      1 - 3 / 4000 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
          _root_.MLDSA.mldsa44.gamma2 c.1 t0 →
      ∀ i ≤ 8, t0SqNorm t0 ≤ mldsa44Grid0 i →
        𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
            (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
          mldsa44Level0 i := by
    intro t0 ht0 hΔ i hi hS
    interval_cases i <;> simp only [mldsa44Grid0, mldsa44Level0] at hS ⊢
    · exact mldsa44_level0_le_0 t0 ht0 hΔ hS
    · exact mldsa44_level0_le_1 t0 ht0 hΔ hS
    · exact mldsa44_level0_le_2 t0 ht0 hΔ hS
    · exact mldsa44_level0_le_3 t0 ht0 hΔ hS
    · exact mldsa44_level0_le_4 t0 ht0 hΔ hS
    · exact mldsa44_level0_le_5 t0 ht0 hΔ hS
    · exact mldsa44_level0_le_6 t0 ht0 hΔ hS
    · exact mldsa44_level0_le_7 t0 ht0 hΔ hS
    · exact mldsa44_level0_le_8 t0 ht0 hΔ hS
  have hga0 : ∀ i < 8, mldsa44Grid0 i ≤ mldsa44Grid0 (i + 1) := by
    intro i hi
    interval_cases i <;> norm_num [mldsa44Grid0]
  have hU0 : ∀ i < 8, mldsa44Level0 i ≤ mldsa44Level0 (i + 1) := by
    intro i hi
    interval_cases i <;> norm_num [mldsa44Level0]
  have hU00 : 0 ≤ mldsa44Level0 0 := by norm_num [mldsa44Level0]
  have htop0 : mldsa44Grid0 8 = 17179869184 := by simp only [mldsa44Grid0]
  have hlev1 : ∀ t0 : RqVec _root_.MLDSA.mldsa44.k, polyVecNorm t0 ≤ 4096 →
      1 - 3 / 250 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
          _root_.MLDSA.mldsa44.gamma2 c.1 t0 →
      ∀ i ≤ 1, t0SqNorm t0 ≤ mldsa44Grid1 i →
        𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
            (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
          mldsa44Level1 i := by
    intro t0 ht0 hΔ i hi hS
    interval_cases i <;> simp only [mldsa44Grid1, mldsa44Level1] at hS ⊢
    · exact mldsa44_level1_le_0 t0 ht0 hΔ hS
    · exact mldsa44_level1_le_1 t0 ht0 hΔ hS
  have hga1 : ∀ i < 1, mldsa44Grid1 i ≤ mldsa44Grid1 (i + 1) := by
    intro i hi
    interval_cases i
    norm_num [mldsa44Grid1]
  have hU1 : ∀ i < 1, mldsa44Level1 i ≤ mldsa44Level1 (i + 1) := by
    intro i hi
    interval_cases i
    norm_num [mldsa44Level1]
  have hU10 : 0 ≤ mldsa44Level1 0 := by norm_num [mldsa44Level1]
  have htop1 : mldsa44Grid1 1 = 17179869184 := by simp only [mldsa44Grid1]
  have hlev2 : ∀ t0 : RqVec _root_.MLDSA.mldsa44.k, polyVecNorm t0 ≤ 4096 →
      1 - 217 / 625 ≤ 𝔼 c : ChallengeBall _root_.MLDSA.mldsa44.tau, ct0Indicator
          _root_.MLDSA.mldsa44.gamma2 c.1 t0 →
      ∀ i ≤ 5, t0SqNorm t0 ≤ mldsa44Grid2 i →
        𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
            (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
          mldsa44Level2 i := by
    intro t0 ht0 hΔ i hi hS
    interval_cases i <;> simp only [mldsa44Grid2, mldsa44Level2] at hS ⊢
    · exact mldsa44_level2_le_0 t0 ht0 hΔ hS
    · exact mldsa44_level2_le_1 t0 ht0 hΔ hS
    · exact mldsa44_level2_le_2 t0 ht0 hΔ hS
    · exact mldsa44_level2_le_3 t0 ht0 hΔ hS
    · exact mldsa44_level2_le_4 t0 ht0 hΔ hS
    · exact mldsa44_level2_le_5 t0 ht0 hΔ hS
  have hga2 : ∀ i < 5, mldsa44Grid2 i ≤ mldsa44Grid2 (i + 1) := by
    intro i hi
    interval_cases i <;> norm_num [mldsa44Grid2]
  have hU2 : ∀ i < 5, mldsa44Level2 i ≤ mldsa44Level2 (i + 1) := by
    intro i hi
    interval_cases i <;> norm_num [mldsa44Level2]
  have hU20 : 0 ≤ mldsa44Level2 0 := by norm_num [mldsa44Level2]
  have htop2 : mldsa44Grid2 5 = 17179869184 := by simp only [mldsa44Grid2]
  -- Every key lies in one layer.
  have hpt : ∀ t0 : RqVec _root_.MLDSA.mldsa44.k, polyVecNorm t0 ≤ 4096 → t0SqNorm t0 ≤ 17179869184
      →
      𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          (mldsa44OracleWeight G t0)⁻¹ ^ 2 ≤
        (if True then 1 else 0 : ℝ) *
        (mldsa44Level0 0 + ∑ i ∈ range 8, (mldsa44Level0 (i + 1) - mldsa44Level0 i) *
          (if mldsa44Grid0 i < t0SqNorm t0 then 1 else 0)) +
        (if ∃ m, 1 / 2 * (256 * 4096 ^ 2) ≤ t0CompSqNorm t0 m then 1 else 0 : ℝ) *
        (mldsa44Level1 0 + ∑ i ∈ range 1, (mldsa44Level1 (i + 1) - mldsa44Level1 i) *
          (if mldsa44Grid1 i < t0SqNorm t0 then 1 else 0)) +
        (if ∃ m, 31 / 50 * (256 * 4096 ^ 2) ≤ t0CompSqNorm t0 m then 1 else 0 : ℝ) *
        (mldsa44Level2 0 + ∑ i ∈ range 5, (mldsa44Level2 (i + 1) - mldsa44Level2 i) *
          (if mldsa44Grid2 i < t0SqNorm t0 then 1 else 0)) := by
    intro t0 ht0 hS
    have hnn : ∀ (U a : ℕ → ℝ) (N : ℕ), (∀ i < N, U i ≤ U (i + 1)) → 0 ≤ U 0 →
        0 ≤ U 0 + ∑ i ∈ range N, (U (i + 1) - U i) * (if a i < t0SqNorm t0 then 1 else 0) :=
      fun U a N hU hU0 => add_nonneg hU0 (Finset.sum_nonneg fun i hi => mul_nonneg
        (sub_nonneg.2 (hU i (Finset.mem_range.1 hi))) (by split_ifs <;> norm_num))
    have h0 := hnn mldsa44Level0 mldsa44Grid0 8 hU0 hU00
    have h1 := hnn mldsa44Level1 mldsa44Grid1 1 hU1 hU10
    have h2 := hnn mldsa44Level2 mldsa44Grid2 5 hU2 hU20
    have hΔ2 := one_sub_le_expect_ct0Indicator_mldsa44 t0
      (one_sub_le_expect_challengeBall_ct0_mldsa44 t0 ht0)
    rw [if_pos trivial, one_mul]
    by_cases hE2 : ∃ m, 31 / 50 * (256 * 4096 ^ 2) ≤ t0CompSqNorm t0 m
    · have hY := le_add_sum_layers_of_imp hga2 hU2 (hS.trans_eq htop2.symm)
        (fun i hi hle => hlev2 t0 ht0 hΔ2 i hi hle)
      rw [if_pos hE2, one_mul]
      have : 0 ≤ (if ∃ m, 1 / 2 * (256 * 4096 ^ 2) ≤ t0CompSqNorm t0 m then 1 else 0 : ℝ) *
          (mldsa44Level1 0 + ∑ i ∈ range 1, (mldsa44Level1 (i + 1) - mldsa44Level1 i) *
          (if mldsa44Grid1 i < t0SqNorm t0 then 1 else 0)) :=
        mul_nonneg (by split_ifs <;> norm_num) h1
      linarith
    have hΔ1 := one_sub_le_expect_ct0Indicator_mldsa44 t0
      (one_sub_le_expect_challengeBall_ct0_mldsa44_thirtyOneFiftieths t0 ht0
        (sum_div_le_of_t0CompSqNorm_lt (fun m hm => hE2 ⟨m, hm⟩)))
    rw [if_neg hE2, zero_mul, add_zero]
    by_cases hE1 : ∃ m, 1 / 2 * (256 * 4096 ^ 2) ≤ t0CompSqNorm t0 m
    · have hY := le_add_sum_layers_of_imp hga1 hU1 (hS.trans_eq htop1.symm)
        (fun i hi hle => hlev1 t0 ht0 hΔ1 i hi hle)
      rw [if_pos hE1, one_mul]
      linarith
    have hΔ0 := one_sub_le_expect_ct0Indicator_mldsa44 t0
      (one_sub_le_expect_challengeBall_ct0_mldsa44_half t0 ht0
        (sum_div_le_of_t0CompSqNorm_lt (fun m hm => hE1 ⟨m, hm⟩)))
    have hY := le_add_sum_layers_of_imp hga0 hU0 (hS.trans_eq htop0.symm)
      (fun i hi hle => hlev0 t0 ht0 hΔ0 i hi hle)
    rw [if_neg hE1, zero_mul, add_zero]
    exact hY
  -- The three layers in expectation.
  have hlay0 := expect_expect_indicator_mul_layers_le
    (E := fun _ _ => True)
    (fun e aHat => t0SqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0) (a := mldsa44Grid0)
              (t := fun i => mldsa44TailFactor0 i) (N := 8)
    (P := 1)
    hU0 hU00 (by simp) (by
      intro i hi
      interval_cases i
      · simp only [true_and, mldsa44Grid0, mldsa44TailFactor0]
        exact expect_expect_indicator_lt_t0SqNorm_le_mldsa44 sk (by norm_num) mldsa44_tail0_le_0
      · simp only [true_and, mldsa44Grid0, mldsa44TailFactor0]
        exact expect_expect_indicator_lt_t0SqNorm_le_mldsa44 sk (by norm_num) mldsa44_tail0_le_1
      · simp only [true_and, mldsa44Grid0, mldsa44TailFactor0]
        exact expect_expect_indicator_lt_t0SqNorm_le_mldsa44 sk (by norm_num) mldsa44_tail0_le_2
      · simp only [true_and, mldsa44Grid0, mldsa44TailFactor0]
        exact expect_expect_indicator_lt_t0SqNorm_le_mldsa44 sk (by norm_num) mldsa44_tail0_le_3
      · simp only [true_and, mldsa44Grid0, mldsa44TailFactor0]
        exact expect_expect_indicator_lt_t0SqNorm_le_mldsa44 sk (by norm_num) mldsa44_tail0_le_4
      · simp only [true_and, mldsa44Grid0, mldsa44TailFactor0]
        exact expect_expect_indicator_lt_t0SqNorm_le_mldsa44 sk (by norm_num) mldsa44_tail0_le_5
      · simp only [true_and, mldsa44Grid0, mldsa44TailFactor0]
        exact expect_expect_indicator_lt_t0SqNorm_le_mldsa44 sk (by norm_num) mldsa44_tail0_le_6
      · simp only [true_and, mldsa44Grid0, mldsa44TailFactor0]
        exact expect_expect_indicator_lt_t0SqNorm_le_mldsa44 sk (by norm_num) mldsa44_tail0_le_7)
  have hsum0 : mldsa44Level0 0 * (1) + ∑ i ∈ range 8, (mldsa44Level0 (i + 1) - mldsa44Level0 i) *
      (mldsa44TailFactor0 i) ≤ ∑ i ∈ range (8 + 1), mldsa44LayerTerm0 i := by
    have hP : mldsa44Level0 0 * (1) ≤ mldsa44LayerTerm0 0 := by
      norm_num [mldsa44Level0, mldsa44LayerTerm0]
    have hT : ∀ i < 8, (mldsa44Level0 (i + 1) - mldsa44Level0 i) * (mldsa44TailFactor0 i) ≤
        mldsa44LayerTerm0 (i + 1) := by
      intro i hi
      interval_cases i <;> norm_num [mldsa44Level0, mldsa44TailFactor0, mldsa44LayerTerm0]
    have := Finset.sum_le_sum fun i hi => hT i (Finset.mem_range.1 hi)
    rw [Finset.sum_range_succ' mldsa44LayerTerm0]
    exact (add_le_add hP this).trans_eq (add_comm _ _)
  have hlay1 := expect_expect_indicator_mul_layers_le
    (E := fun e aHat => ∃ m, 1 / 2 * (256 * 4096 ^ 2) ≤ t0CompSqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 m)
    (fun e aHat => t0SqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0) (a := mldsa44Grid1)
              (t := fun i => 4 * mldsa44TailFactor1 i) (N := 1)
    (P := 4 * (2⁻¹ ^ 51 * (9747479793 / 10000000000)))
    hU1 hU10 (expect_expect_indicator_exists_le_mldsa44 sk (by norm_num) mldsa44_tailP1_le) (by
      intro i hi
      interval_cases i
      · simp only [mldsa44Grid1, mldsa44TailFactor1]
        exact expect_expect_indicator_exists_and_lt_le_mldsa44 sk (by norm_num) (by norm_num)
          mldsa44_tail1_le_0)
  have hsum1 : mldsa44Level1 0 * (4 * (2⁻¹ ^ 51 * (9747479793 / 10000000000))) + ∑ i ∈ range 1,
      (mldsa44Level1 (i + 1) - mldsa44Level1 i) *
      (4 * mldsa44TailFactor1 i) ≤ ∑ i ∈ range (1 + 1), mldsa44LayerTerm1 i := by
    have hP : mldsa44Level1 0 * (4 * (2⁻¹ ^ 51 * (9747479793 / 10000000000))) ≤ mldsa44LayerTerm1 0
        := by
      norm_num [mldsa44Level1, mldsa44LayerTerm1]
    have hT : ∀ i < 1, (mldsa44Level1 (i + 1) - mldsa44Level1 i) * (4 * mldsa44TailFactor1 i) ≤
        mldsa44LayerTerm1 (i + 1) := by
      intro i hi
      interval_cases i
      norm_num [mldsa44Level1, mldsa44TailFactor1, mldsa44LayerTerm1]
    have := Finset.sum_le_sum fun i hi => hT i (Finset.mem_range.1 hi)
    rw [Finset.sum_range_succ' mldsa44LayerTerm1]
    exact (add_le_add hP this).trans_eq (add_comm _ _)
  have hlay2 := expect_expect_indicator_mul_layers_le
    (E := fun e aHat => ∃ m, 31 / 50 * (256 * 4096 ^ 2) ≤ t0CompSqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 m)
    (fun e aHat => t0SqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0) (a := mldsa44Grid2)
              (t := fun i => 4 * mldsa44TailFactor2 i) (N := 5)
    (P := 4 * (2⁻¹ ^ 149 * (4599823217 / 5000000000)))
    hU2 hU20 (expect_expect_indicator_exists_le_mldsa44 sk (by norm_num) mldsa44_tailP2_le) (by
      intro i hi
      interval_cases i
      · simp only [mldsa44Grid2, mldsa44TailFactor2]
        exact expect_expect_indicator_exists_and_lt_le_mldsa44 sk (by norm_num) (by norm_num)
          mldsa44_tail2_le_0
      · simp only [mldsa44Grid2, mldsa44TailFactor2]
        exact expect_expect_indicator_exists_and_lt_le_mldsa44 sk (by norm_num) (by norm_num)
          mldsa44_tail2_le_1
      · simp only [mldsa44Grid2, mldsa44TailFactor2]
        exact expect_expect_indicator_exists_and_lt_le_mldsa44 sk (by norm_num) (by norm_num)
          mldsa44_tail2_le_2
      · simp only [mldsa44Grid2, mldsa44TailFactor2]
        exact expect_expect_indicator_exists_and_lt_le_mldsa44 sk (by norm_num) (by norm_num)
          mldsa44_tail2_le_3
      · simp only [mldsa44Grid2, mldsa44TailFactor2]
        exact expect_expect_indicator_exists_and_lt_le_mldsa44 sk (by norm_num) (by norm_num)
          mldsa44_tail2_le_4)
  have hsum2 : mldsa44Level2 0 * (4 * (2⁻¹ ^ 149 * (4599823217 / 5000000000))) + ∑ i ∈ range 5,
      (mldsa44Level2 (i + 1) - mldsa44Level2 i) *
      (4 * mldsa44TailFactor2 i) ≤ ∑ i ∈ range (5 + 1), mldsa44LayerTerm2 i := by
    have hP : mldsa44Level2 0 * (4 * (2⁻¹ ^ 149 * (4599823217 / 5000000000))) ≤ mldsa44LayerTerm2 0
        := by
      norm_num [mldsa44Level2, mldsa44LayerTerm2]
    have hT : ∀ i < 5, (mldsa44Level2 (i + 1) - mldsa44Level2 i) * (4 * mldsa44TailFactor2 i) ≤
        mldsa44LayerTerm2 (i + 1) := by
      intro i hi
      interval_cases i <;> norm_num [mldsa44Level2, mldsa44TailFactor2, mldsa44LayerTerm2]
    have := Finset.sum_le_sum fun i hi => hT i (Finset.mem_range.1 hi)
    rw [Finset.sum_range_succ' mldsa44LayerTerm2]
    exact (add_le_add hP this).trans_eq (add_comm _ _)
  have ht0 : ∀ (e : SecretCoeffs _root_.MLDSA.mldsa44)
      (aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l), polyVecNorm
      (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 ≤ 4096 :=
    fun e aHat => by
      rw [matrixKey_t0]
      exact polyVecNorm_edgeT0Of_le _
  have hS : ∀ (e : SecretCoeffs _root_.MLDSA.mldsa44)
      (aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l),
      t0SqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 ≤ 17179869184 := fun e
              aHat =>
    (t0SqNorm_keyOf_le _ _).trans (by rw [mldsa44_k]; norm_num [ringDegree])
  calc _ ≤ 𝔼 e : SecretCoeffs _root_.MLDSA.mldsa44, 𝔼 aHat : TqMatrix _root_.MLDSA.mldsa44.k
         _root_.MLDSA.mldsa44.l,
        ((if True then 1 else 0 : ℝ) *
            (mldsa44Level0 0 + ∑ i ∈ range 8, (mldsa44Level0 (i + 1) - mldsa44Level0 i) *
          (if mldsa44Grid0 i < t0SqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 then 1 else 0)) +
        (if ∃ m, 1 / 2 * (256 * 4096 ^ 2) ≤ t0CompSqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 m then 1 else 0 : ℝ) *
              (mldsa44Level1 0 + ∑ i ∈ range 1, (mldsa44Level1 (i + 1) - mldsa44Level1 i) *
          (if mldsa44Grid1 i < t0SqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 then 1 else 0)) +
        (if ∃ m, 31 / 50 * (256 * 4096 ^ 2) ≤ t0CompSqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 m then 1 else 0 : ℝ) *
              (mldsa44Level2 0 + ∑ i ∈ range 5, (mldsa44Level2 (i + 1) - mldsa44Level2 i) *
          (if mldsa44Grid2 i < t0SqNorm (keyOf (keyOfCoeffs sk e)
          (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0 then 1 else 0))) :=
        Finset.expect_le_expect fun e _ => Finset.expect_le_expect fun aHat _ =>
          hpt _ (ht0 e aHat) (hS e aHat)
    _ ≤ ∑ i ∈ range (8 + 1), mldsa44LayerTerm0 i + ∑ i ∈ range (1 + 1), mldsa44LayerTerm1 i +
        ∑ i ∈ range (5 + 1), mldsa44LayerTerm2 i := by
        simp only [Finset.expect_add_distrib]
        exact add_le_add (add_le_add (hlay0.trans hsum0) (hlay1.trans hsum1)) (hlay2.trans hsum2)
    _ ≤ (24 / 5) ^ 2 := by
        norm_num [Finset.sum_range_succ, mldsa44LayerTerm0, mldsa44LayerTerm1, mldsa44LayerTerm2]

end Layers

end GordieHowe.MLDSA.Regularity
