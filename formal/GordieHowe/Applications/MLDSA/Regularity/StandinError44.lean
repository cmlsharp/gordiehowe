-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.StandinError
public import GordieHowe.Applications.MLDSA.Regularity.WeightTail44
public import GordieHowe.Applications.MLDSA.Regularity.InstancesSeven

@[expose] public section

/-!
# The stand-in error of the ML-DSA-44 signer, averaged over keys

At ML-DSA-44 the ct₀ check can fail (`τ 2^12 = 159744 > γ₂ = 95232`), so no acceptance floor holds
for every typical key, and the route of `StandinError.lean` (a floor for typical keys, MLWE for the
atypical ones) does not close. This file averages over the keys instead: `ExpandS` (FIPS 204
Algorithm 33) is a random oracle onto the `η`-box, so the secret is a uniform box secret
(`oracleSecretLaw`), and `Â` and `SampleInBall = G` are uniform.

* **A weight in the denominator** (`tvDist_le_indicator_add_mul_inv`): for one key, one matrix and
  one oracle, and any `w ≥ 0` at most the mean member weight at `β_min = 1` of every bucket vector,
  `tvDist ≤ 1[w = 0] + n w⁻¹`, with `n` the numerator of `tvDist_le_numerator_div`. At `β_min = 1`
  the member weight is at most the acceptance weight (`toReal_flatWeight_one_le`), so `w` is at
  most the mean acceptance weight.
* **Cauchy–Schwarz and Jensen** (`expect_tvDist_standin_le_of_weight`): for a weight `W G t₀` with
  `𝔼_Â n² ≤ ε²` for every key and oracle, `𝔼_{e, Â, G} W⁻² ≤ B` and `Pr_{e, Â, G}[W = 0] ≤ z`, the
  averaged stand-in error is at most `z + ε √B`.
* **A vanishing weight is rare** (`expect_indicator_mldsa44OracleWeight_eq_zero_le`): the weight
  `mldsa44OracleWeight` vanishes only if every commitment hash fails the ct₀ check, which has
  probability at most `(217/625)^|C|` over `G`
  (`one_sub_le_expect_challengeBall_ct0_mldsa44`).
* **ML-DSA-44** (`expect_tvDist_standin_le_mldsa44`, `sum_expect_tvDist_standin_le_mldsa44`): with
  `ε = 11 · 2^-101` (`expect_sq_sum_expect_abs_realMass_sub_le_mldsa44_box_seven`), `B = (24/5)²`
  (`expect_expect_expect_inv_sq_mldsa44OracleWeight_le`) and `z = 2^-1000`, the averaged stand-in
  error is at most `11 · 2^-101 · (24/5) + 2^-1000 ≤ 2^-95`, with no MLWE term.
-/

open Finset Real
open scoped BigOperators ENNReal

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA
open LatticeCrypto TransformOps
open PMF (tvDist tvDist_le_one)

/-! ### The secret law of a random-oracle `ExpandS` -/

section SecretLaw

/-- **The secret law of `ExpandS` as a random oracle**: the law of `(s₁, s₂) = ExpandS(ρ')`
(FIPS 204 Algorithm 33) when `ExpandS` is a uniform random oracle onto the coefficient arrays of
the `η`-box, a uniform box secret read by `secretOfCoeffs`. -/
noncomputable def oracleSecretLaw (p : Params) : PMF (RqVec p.l × RqVec p.k) :=
  (PMF.uniformOfFintype (SecretCoeffs p)).map secretOfCoeffs

/-- An average under `oracleSecretLaw` is an average over uniform box secrets. -/
theorem sum_oracleSecretLaw_mul {p : Params} (f : RqVec p.l × RqVec p.k → ℝ) :
    ∑ s, (oracleSecretLaw p s).toReal * f s = 𝔼 e : SecretCoeffs p, f (secretOfCoeffs e) := by
  rw [oracleSecretLaw, PMF.sum_toReal_map_mul, Fintype.expect_eq_sum_div_card, Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [PMF.toReal_uniformOfFintype_apply]
  ring

/-- The secrets of `oracleSecretLaw` lie in the `η`-box. -/
theorem oracleSecretLaw_bounded {p : Params} (s : RqVec p.l × RqVec p.k)
    (hs : oracleSecretLaw p s ≠ 0) :
    polyVecBounded s.1 p.eta ∧ polyVecBounded s.2 p.eta := by
  obtain ⟨e, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ((PMF.mem_support_iff _ _).2 hs)
  exact secretOfCoeffs_bounded e

end SecretLaw

/-! ### The plain-law distance from a weight that may vanish -/

section PlainLaw

variable {p : Params} [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Nonempty (MaskBox p)]

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- **At `β_min = 1` the member weight is at most the acceptance weight**: `min(1, aw/1) ≤ aw`. -/
theorem toReal_flatWeight_one_le (prims : Primitives p) (t0 : RqVec p.k)
    (vc : BucketVec p × CommitHashBytes p) :
    (flatWeight prims (Cutoff.const 1) t0 vc : ℝ≥0∞).toReal ≤ (t0Weight prims t0 vc :
        ℝ≥0∞).toReal :=
  ENNReal.toReal_mono (ENNReal.nnratCast_ne_top _) (by
    rw [coe_flatWeight, ENNReal.nnratCast_one, div_one]
    exact min_le_right _ _)

/-- **The plain-law distance from a weight that may vanish.** With `P` the normalized real
accepted mass of `(w₁, c̃)` and `Q` the normalized acceptance weight, each where its total is
positive (as in `tvDist_le_numerator_div`), and `w ≥ 0` at most the mean member weight at
`β_min = 1` of every bucket vector: `tvDist P Q ≤ 1[w = 0] + n w⁻¹` with
`n = ∑_v 𝔼_c̃ |realMass - ρ_z standinMass| / (K |V|)`. -/
theorem tvDist_le_indicator_add_mul_inv (hp : SigningParams p) (prims : Primitives p)
    (h_laws : SigningLaws prims) (sk : SecretKey p) (hs2 : polyVecBounded sk.s2 p.eta)
    (aHat : TqMatrix p.k p.l) (P Q : PMF (BucketVec p × CommitHashBytes p))
    (hP : 0 < ∑ vc' : BucketVec p × CommitHashBytes p, (realMass prims sk aHat vc'.1 vc'.2).toReal →
      ∀ vc, (P vc).toReal = (realMass prims sk aHat vc.1 vc.2).toReal /
        ∑ vc' : BucketVec p × CommitHashBytes p, (realMass prims sk aHat vc'.1 vc'.2).toReal)
    (hQ : 0 < ∑ vc', (t0Weight prims sk.t0 vc' : ℝ≥0∞).toReal →
      ∀ vc, (Q vc).toReal = (t0Weight prims sk.t0 vc : ℝ≥0∞).toReal /
        ∑ vc', (t0Weight prims sk.t0 vc' : ℝ≥0∞).toReal)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v, w ≤ 𝔼 c, (flatWeight prims (Cutoff.const 1) sk.t0 (v, c) :
        ℝ≥0∞).toReal) :
    tvDist P Q ≤ (if w = 0 then 1 else 0) +
      (∑ v, 𝔼 c, |(realMass prims sk aHat v c).toReal -
          (zAcceptFraction p * standinMass prims sk v c).toReal|) /
        ((standinScale p).toReal * Fintype.card (BucketVec p)) * w⁻¹ := by
  have hn0 : 0 ≤ (∑ v, 𝔼 c, |(realMass prims sk aHat v c).toReal -
      (zAcceptFraction p * standinMass prims sk v c).toReal|) /
        ((standinScale p).toReal * Fintype.card (BucketVec p)) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => Finset.expect_nonneg fun _ _ => abs_nonneg _)
      (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))
  split_ifs with hw'
  · rw [hw', inv_zero, mul_zero, add_zero]
    exact tvDist_le_one P Q
  have h : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hw')
  rw [zero_add, ← div_eq_mul_inv]
  have hA : w ≤ 𝔼 vc, (t0Weight prims sk.t0 vc : ℝ≥0∞).toReal := by
    rw [← Finset.univ_product_univ, Finset.expect_product]
    refine (Finset.expect_const Finset.univ_nonempty w).symm.le.trans
      (Finset.expect_le_expect fun v _ => (hw v).trans
        (Finset.expect_le_expect fun c _ => toReal_flatWeight_one_le prims _ _))
  have hApos : 0 < 𝔼 vc, (t0Weight prims sk.t0 vc : ℝ≥0∞).toReal := h.trans_le hA
  have hsum : 0 < ∑ vc', (t0Weight prims sk.t0 vc' : ℝ≥0∞).toReal := by
    rw [Fintype.expect_eq_sum_div_card] at hApos
    exact (div_pos_iff_of_pos_right (by exact_mod_cast Fintype.card_pos)).1 hApos
  exact (tvDist_le_numerator_div hp prims h_laws sk hs2 aHat P Q hP (hQ hsum) hApos).trans
    (div_le_div_of_nonneg_left hn0 h hA)

end PlainLaw

/-! ### The average over keys, matrices and oracles -/

section Average

variable {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)]

attribute [local instance] concreteNTTRingOps

/-- **The averaged stand-in error from a weight that may vanish.** Let `W G t₀ ≥ 0` be at most the
mean member weight at `β_min = 1` of every bucket vector whenever `‖t₀‖∞ ≤ 2^12`. Suppose that
* for every key with `s₁, s₂` in the `η`-box and every oracle `G`,
  `𝔼_Â (∑_v 𝔼_c̃ |realMass - ρ_z standinMass|)² ≤ (K |V| ε)²`;
* over uniform box secrets `e`, a uniform matrix `Â` and a uniform oracle `G`,
  `𝔼 (W G t₀)⁻² ≤ B` and `Pr[W G t₀ = 0] ≤ z`, for every key.

Then for keys `key s` with secret `s`, real laws `R s` and stand-in laws `Q`,
`𝔼_{e, Â, G} tvDist(R s G Â, Q G t₀) ≤ z + ε √B` with `s = secretOfCoeffs e`
(`tvDist_le_indicator_add_mul_inv`, Cauchy–Schwarz over `Â`, Jensen for `√` over `G` and `e`). -/
theorem expect_tvDist_standin_le_of_weight (hp : p.isApproved)
    (W : (CommitHashBytes p → ChallengeBall p.tau) → RqVec p.k → ℝ) (hW0 : ∀ G t0, 0 ≤ W G t0)
    (hW : ∀ G t0, polyVecNorm t0 ≤ 4096 → ∀ v,
      W G t0 ≤ 𝔼 c, (flatWeight (oraclePrims G) (Cutoff.const 1) t0 (v, c) : ℝ≥0∞).toReal)
    {ε B z : ℝ} (hε : 0 ≤ ε)
    (hnum : ∀ sk₀ : SecretKey p, polyVecBounded sk₀.s1 p.eta → polyVecBounded sk₀.s2 p.eta →
      ∀ G : CommitHashBytes p → ChallengeBall p.tau,
        𝔼 aHat : TqMatrix p.k p.l, (∑ v : BucketVec p, 𝔼 c,
          |(realMass (oraclePrims G) (matrixKey sk₀ aHat) aHat v c).toReal -
            (zAcceptFraction p * standinMass (oraclePrims G) (matrixKey sk₀ aHat) v c).toReal|) ^
              2 ≤
          ((standinScale p).toReal * Fintype.card (BucketVec p) * ε) ^ 2)
    (hB : ∀ sk : SecretKey p, 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
      𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
        (W G (matrixKey (keyOfCoeffs sk e) aHat).t0)⁻¹ ^ 2 ≤ B)
    (hz : ∀ sk : SecretKey p, 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
      𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
        (if W G (matrixKey (keyOfCoeffs sk e) aHat).t0 = 0 then (1 : ℝ) else 0) ≤ z)
    (key : RqVec p.l × RqVec p.k → SecretKey p) (h1 : ∀ s, (key s).s1 = s.1)
    (h2 : ∀ s, (key s).s2 = s.2)
    (R : RqVec p.l × RqVec p.k → (CommitHashBytes p → ChallengeBall p.tau) →
      TqMatrix p.k p.l → PMF (BucketVec p × CommitHashBytes p))
    (hR : ∀ s, IsRealCommitLaw (key s) (R s))
    (Q : (CommitHashBytes p → ChallengeBall p.tau) → RqVec p.k →
      PMF (BucketVec p × CommitHashBytes p)) (hQ : IsStandinCommitLaw Q) :
    𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
        𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
          tvDist (R (secretOfCoeffs e) G aHat)
            (Q G (matrixKey (key (secretOfCoeffs e)) aHat).t0) ≤
      z + ε * √B := by
  have hsp := SigningParams.of_isApproved hp
  have := challengeBall_nonempty (tau_le_ringDegree hp)
  set sk' : SecretKey p := key 0
  set K := (standinScale p).toReal
  have hK : 0 < K := standinScale_pos hsp
  have hV : (0 : ℝ) < Fintype.card (BucketVec p) := by exact_mod_cast Fintype.card_pos
  have ht0 : ∀ (sk₀ : SecretKey p) aHat, polyVecNorm (matrixKey sk₀ aHat).t0 ≤ 4096 :=
    polyVecNorm_matrixKey_t0_le
  have ht0eq : ∀ (e : SecretCoeffs p) aHat, (matrixKey (key (secretOfCoeffs e)) aHat).t0 =
      (matrixKey (keyOfCoeffs sk' e) aHat).t0 := fun e aHat => by
    rw [matrixKey_t0, matrixKey_t0, h1, h2]
    rfl
  have hbox : ∀ e : SecretCoeffs p, polyVecBounded (key (secretOfCoeffs e)).s1 p.eta ∧
      polyVecBounded (key (secretOfCoeffs e)).s2 p.eta := fun e => by
    rw [h1, h2]
    exact secretOfCoeffs_bounded e
  set N : SecretCoeffs p → (CommitHashBytes p → ChallengeBall p.tau) → TqMatrix p.k p.l → ℝ :=
    fun e G aHat => (∑ v, 𝔼 c,
      |(realMass (oraclePrims G) (matrixKey (key (secretOfCoeffs e)) aHat) aHat v c).toReal -
        (zAcceptFraction p * standinMass (oraclePrims G)
          (matrixKey (key (secretOfCoeffs e)) aHat) v c).toReal|) /
      (K * Fintype.card (BucketVec p))
  set w : SecretCoeffs p → (CommitHashBytes p → ChallengeBall p.tau) → TqMatrix p.k p.l → ℝ :=
    fun e G aHat => W G (matrixKey (keyOfCoeffs sk' e) aHat).t0
  -- The pointwise bound.
  have hpt : ∀ e aHat G, tvDist (R (secretOfCoeffs e) G aHat)
      (Q G (matrixKey (key (secretOfCoeffs e)) aHat).t0) ≤
        (if w e G aHat = 0 then 1 else 0) + N e G aHat * (w e G aHat)⁻¹ := fun e aHat G => by
    have hw : ∀ v, w e G aHat ≤ 𝔼 c, (flatWeight (oraclePrims G) (Cutoff.const 1)
        (matrixKey (key (secretOfCoeffs e)) aHat).t0 (v, c) : ℝ≥0∞).toReal := fun v => by
      rw [ht0eq]
      exact hW G _ (ht0 _ aHat) v
    exact tvDist_le_indicator_add_mul_inv hsp (oraclePrims G)
      (signingLaws_concreteWithSampleInBall p hp (sampleInBallShape_oraclePrims G))
      (matrixKey (key (secretOfCoeffs e)) aHat) (hbox e).2 aHat _ _ (hR _ G aHat)
      (hQ G _ (ht0 _ aHat)) (hW0 _ _) hw
  -- Cauchy–Schwarz over the matrix.
  have hCS : ∀ e G, 𝔼 aHat, N e G aHat * (w e G aHat)⁻¹ ≤
      ε * √(𝔼 aHat, (w e G aHat)⁻¹ ^ 2) := fun e G => by
    refine (Real.expect_mul_le_sqrt_mul_sqrt _ _ _).trans
      (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    have h := hnum (key (secretOfCoeffs e)) (hbox e).1 (hbox e).2 G
    have hN2 : 𝔼 aHat, N e G aHat ^ 2 ≤ ε ^ 2 := by
      simp only [N, div_pow]
      rw [← Finset.expect_div, div_le_iff₀ (by positivity)]
      refine h.trans_eq ?_
      ring
    calc √(𝔼 aHat, N e G aHat ^ 2) ≤ √(ε ^ 2) := Real.sqrt_le_sqrt hN2
      _ = ε := Real.sqrt_sq hε
  have hY0 : ∀ e G, 0 ≤ 𝔼 aHat, (w e G aHat)⁻¹ ^ 2 := fun e G =>
    Finset.expect_nonneg fun _ _ => sq_nonneg _
  calc 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
        𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
          tvDist (R (secretOfCoeffs e) G aHat) (Q G (matrixKey (key (secretOfCoeffs e)) aHat).t0)
      ≤ 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
        𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
          ((if w e G aHat = 0 then (1 : ℝ) else 0) + N e G aHat * (w e G aHat)⁻¹) :=
        Finset.expect_le_expect fun e _ => Finset.expect_le_expect fun aHat _ =>
          Finset.expect_le_expect fun G _ => hpt e aHat G
    _ = 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
          𝔼 G : CommitHashBytes p → ChallengeBall p.tau, (if w e G aHat = 0 then (1 : ℝ) else 0) +
        𝔼 e : SecretCoeffs p, 𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
          𝔼 aHat : TqMatrix p.k p.l, N e G aHat * (w e G aHat)⁻¹ := by
        simp only [Finset.expect_add_distrib]
        congr 1
        exact Finset.expect_congr rfl fun e _ => Finset.expect_comm _ _ _
    _ ≤ z + 𝔼 e : SecretCoeffs p, 𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
          ε * √(𝔼 aHat, (w e G aHat)⁻¹ ^ 2) :=
        add_le_add (hz sk') (Finset.expect_le_expect fun e _ =>
          Finset.expect_le_expect fun G _ => hCS e G)
    _ ≤ z + ε * √B := by
        refine add_le_add le_rfl ?_
        simp_rw [← Finset.mul_expect]
        refine mul_le_mul_of_nonneg_left ?_ hε
        calc 𝔼 e : SecretCoeffs p, 𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
              √(𝔼 aHat, (w e G aHat)⁻¹ ^ 2)
            ≤ 𝔼 e : SecretCoeffs p, √(𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
                𝔼 aHat, (w e G aHat)⁻¹ ^ 2) :=
              Finset.expect_le_expect fun e _ =>
                Real.expect_sqrt_le_sqrt_expect _ fun G => hY0 e G
          _ ≤ √(𝔼 e : SecretCoeffs p, 𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
                𝔼 aHat, (w e G aHat)⁻¹ ^ 2) :=
              Real.expect_sqrt_le_sqrt_expect _ fun e =>
                Finset.expect_nonneg fun G _ => hY0 e G
          _ ≤ √B := by
              refine Real.sqrt_le_sqrt (le_trans (le_of_eq ?_) (hB sk'))
              exact Finset.expect_congr rfl fun e _ => Finset.expect_comm _ _ _

end Average

/-! ### ML-DSA-44 -/

section Instance

attribute [local instance] concreteNTTRingOps

/-- **The weight vanishes rarely at ML-DSA-44**: for `‖t₀‖∞ ≤ 2^12` and `G` uniform onto `B_39`,
`Pr_G[mldsa44OracleWeight G t₀ = 0] ≤ (217/625)^|C|`. A zero weight needs every commitment hash to
fail the ct₀ check, and each `G(c̃)` fails it independently with probability at most `217/625`
(`one_sub_le_expect_challengeBall_ct0_mldsa44`). -/
theorem expect_indicator_mldsa44OracleWeight_eq_zero_le (t0 : RqVec _root_.MLDSA.mldsa44.k)
    (ht0 : polyVecNorm t0 ≤ 4096) :
    𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (if mldsa44OracleWeight G t0 = 0 then (1 : ℝ) else 0) ≤
      (217 / 625) ^ Fintype.card (CommitHashBytes _root_.MLDSA.mldsa44) := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty (tau_le_ringDegree isApproved_mldsa44)
  set φ : ChallengeBall _root_.MLDSA.mldsa44.tau → ℝ := fun c =>
    1 - ct0Indicator _root_.MLDSA.mldsa44.gamma2 c.1 t0
  have hφ0 : ∀ c, 0 ≤ φ c := fun c => sub_nonneg.2 (ct0Indicator_le_one _ _ _)
  have hC : (0 : ℝ) < Fintype.card (CommitHashBytes _root_.MLDSA.mldsa44) := by
    exact_mod_cast Fintype.card_pos
  have hpt : ∀ G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      (if mldsa44OracleWeight G t0 = 0 then (1 : ℝ) else 0) ≤ ∏ cTilde, φ (G cTilde) := by
    intro G
    split_ifs with h
    · have h1 : 2⁻¹ ^ 3072 * 𝔼 cTilde, ct0Indicator _root_.MLDSA.mldsa44.gamma2 (G cTilde).1 t0 ≤
          0 := h ▸ le_max_right _ _
      have hπ : 𝔼 cTilde, ct0Indicator _root_.MLDSA.mldsa44.gamma2 (G cTilde).1 t0 ≤ 0 :=
        nonpos_of_mul_nonpos_right h1 (by positivity)
      have hs : ∑ cTilde, ct0Indicator _root_.MLDSA.mldsa44.gamma2 (G cTilde).1 t0 = 0 := by
        refine le_antisymm ?_ (Finset.sum_nonneg fun _ _ => ct0Indicator_nonneg _ _ _)
        rw [Fintype.expect_eq_sum_div_card, div_le_iff₀ hC, zero_mul] at hπ
        exact hπ
      have hz := (Fintype.sum_eq_zero_iff_of_nonneg fun _ => ct0Indicator_nonneg _ _ _).1 hs
      refine le_of_eq (Finset.prod_eq_one fun cTilde _ => ?_).symm
      have hc : ct0Indicator _root_.MLDSA.mldsa44.gamma2 (G cTilde).1 t0 = 0 := congrFun hz cTilde
      change 1 - ct0Indicator _root_.MLDSA.mldsa44.gamma2 (G cTilde).1 t0 = 1
      rw [hc, sub_zero]
    · exact Finset.prod_nonneg fun cTilde _ => hφ0 _
  have hmean : 𝔼 c, φ c ≤ 217 / 625 := by
    have h := one_sub_le_expect_ct0Indicator_mldsa44 t0
      (one_sub_le_expect_challengeBall_ct0_mldsa44 t0 ht0)
    simp only [φ]
    rw [Finset.expect_sub_distrib, Finset.expect_const Finset.univ_nonempty]
    linarith
  calc 𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        (if mldsa44OracleWeight G t0 = 0 then (1 : ℝ) else 0)
      ≤ 𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          ∏ cTilde, φ (G cTilde) := Finset.expect_le_expect fun G _ => hpt G
    _ = ∏ _cTilde : CommitHashBytes _root_.MLDSA.mldsa44, 𝔼 c, φ c :=
        PMF.expect_prod_apply fun _ c => φ c
    _ = (𝔼 c, φ c) ^ Fintype.card (CommitHashBytes _root_.MLDSA.mldsa44) := by
        rw [Finset.prod_const, Finset.card_univ]
    _ ≤ _ := pow_le_pow_left₀ (Finset.expect_nonneg fun c _ => hφ0 c) hmean _

/-- `(217/625)^|C| ≤ 2^-1000` at ML-DSA-44, with `|C| = 256^32` commitment hashes. -/
theorem pow_card_commitHashBytes_le_mldsa44 :
    (217 / 625 : ℝ) ^ Fintype.card (CommitHashBytes _root_.MLDSA.mldsa44) ≤ 1 / 2 ^ 1000 := by
  rw [card_commitHashBytes, show _root_.MLDSA.mldsa44.lambda = 128 from rfl]
  calc (217 / 625 : ℝ) ^ (256 ^ (128 / 4)) ≤ (1 / 2) ^ (256 ^ (128 / 4)) :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ ≤ (1 / 2) ^ 1000 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
    _ = 1 / 2 ^ 1000 := by rw [one_div_pow]

/-- **The stand-in error at ML-DSA-44, averaged over keys.** For uniform box secrets `e` (`ExpandS`
a random oracle), keys `key s` with secret `s = secretOfCoeffs e`, a uniform matrix `Â`,
`SampleInBall` a uniform random oracle `G` onto `B_39`, real laws `R s` and stand-in laws `Q`:
`𝔼_{e, Â, G} tvDist(R s G Â, Q G t₀) ≤ 11 · 2^-101 · (24/5) + 2^-1000`
(`expect_tvDist_standin_le_of_weight` with `mldsa44OracleWeight`). -/
theorem expect_tvDist_standin_le_mldsa44
    (key : RqVec _root_.MLDSA.mldsa44.l × RqVec _root_.MLDSA.mldsa44.k →
      SecretKey _root_.MLDSA.mldsa44)
    (h1 : ∀ s, (key s).s1 = s.1) (h2 : ∀ s, (key s).s2 = s.2)
    (R : RqVec _root_.MLDSA.mldsa44.l × RqVec _root_.MLDSA.mldsa44.k →
      (CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau) →
        TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l →
          PMF (BucketVec _root_.MLDSA.mldsa44 × CommitHashBytes _root_.MLDSA.mldsa44))
    (hR : ∀ s, IsRealCommitLaw (key s) (R s))
    (Q : (CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau) →
      RqVec _root_.MLDSA.mldsa44.k →
        PMF (BucketVec _root_.MLDSA.mldsa44 × CommitHashBytes _root_.MLDSA.mldsa44))
    (hQ : IsStandinCommitLaw Q) :
    𝔼 e : SecretCoeffs _root_.MLDSA.mldsa44,
      𝔼 aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
        𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          tvDist (R (secretOfCoeffs e) G aHat)
            (Q G (matrixKey (key (secretOfCoeffs e)) aHat).t0) ≤
      11 / 2 ^ 101 * (24 / 5) + 1 / 2 ^ 1000 := by
  have := concreteNTTRingLaws
  have hz : ∀ sk : SecretKey _root_.MLDSA.mldsa44, 𝔼 e : SecretCoeffs _root_.MLDSA.mldsa44,
      𝔼 aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
        𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          (if mldsa44OracleWeight G (matrixKey (keyOfCoeffs sk e) aHat).t0 = 0 then (1 : ℝ)
            else 0) ≤ 1 / 2 ^ 1000 := fun sk => by
    refine (Finset.expect_le_expect fun e _ => Finset.expect_le_expect fun aHat _ =>
      (expect_indicator_mldsa44OracleWeight_eq_zero_le _ ?_).trans
        pow_card_commitHashBytes_le_mldsa44).trans_eq ?_
    · exact polyVecNorm_matrixKey_t0_le _ _
    · rw [Finset.expect_const Finset.univ_nonempty, Finset.expect_const Finset.univ_nonempty]
  have h := expect_tvDist_standin_le_of_weight isApproved_mldsa44 mldsa44OracleWeight
    mldsa44OracleWeight_nonneg
    (fun G t0 ht0 v => mldsa44OracleWeight_le_expect_flatWeight (oraclePrims G) G
      (fun _ => rfl) ENNReal.nnratCast_one.le t0 ht0 v)
    (ε := 11 / 2 ^ 101) (B := (24 / 5) ^ 2) (by positivity)
    (fun sk₀ hs1 hs2 G => expect_sq_sum_expect_abs_realMass_sub_le_mldsa44_box_seven sk₀ hs1 hs2
      (sampleInBallShape_oraclePrims G))
    expect_expect_expect_inv_sq_mldsa44OracleWeight_le hz key h1 h2 R hR Q hQ
  rw [Real.sqrt_sq (by norm_num)] at h
  exact h.trans_eq (add_comm _ _)

/-- **The stand-in error at ML-DSA-44, over the secret law of a random-oracle `ExpandS`.** For
keys `key s` with secret `s`, `(s₁, s₂) ← oracleSecretLaw`, `Â` uniform, `SampleInBall` a
uniform random oracle onto `B_39`, real laws `R s` and stand-in laws `Q`:
`𝔼_{s, Â, G} tvDist(R s G Â, Q G t₀) ≤ 2^-95` (`expect_tvDist_standin_le_mldsa44`:
`11 · 2^-101 · (24/5) + 2^-1000 ≤ 2^-95`). -/
theorem sum_expect_tvDist_standin_le_mldsa44
    (key : RqVec _root_.MLDSA.mldsa44.l × RqVec _root_.MLDSA.mldsa44.k →
      SecretKey _root_.MLDSA.mldsa44)
    (h1 : ∀ s, (key s).s1 = s.1) (h2 : ∀ s, (key s).s2 = s.2)
    (R : RqVec _root_.MLDSA.mldsa44.l × RqVec _root_.MLDSA.mldsa44.k →
      (CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau) →
        TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l →
          PMF (BucketVec _root_.MLDSA.mldsa44 × CommitHashBytes _root_.MLDSA.mldsa44))
    (hR : ∀ s, IsRealCommitLaw (key s) (R s))
    (Q : (CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau) →
      RqVec _root_.MLDSA.mldsa44.k →
        PMF (BucketVec _root_.MLDSA.mldsa44 × CommitHashBytes _root_.MLDSA.mldsa44))
    (hQ : IsStandinCommitLaw Q) :
    ∑ s, (oracleSecretLaw _root_.MLDSA.mldsa44 s).toReal *
        𝔼 aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          𝔼 G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
            tvDist (R s G aHat) (Q G (matrixKey (key s) aHat).t0) ≤ 1 / 2 ^ 95 := by
  rw [sum_oracleSecretLaw_mul]
  refine (expect_tvDist_standin_le_mldsa44 key h1 h2 R hR Q hQ).trans ?_
  have h : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 ^ 100 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have h' : (11 : ℝ) / 2 ^ 101 * (24 / 5) + 1 / 2 ^ 100 ≤ 1 / 2 ^ 95 := by norm_num
  exact (add_le_add le_rfl h).trans h'

end Instance

end GordieHowe.MLDSA.Regularity
