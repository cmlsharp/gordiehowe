-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.SignerRegularity
public import GordieHowe.Applications.MLDSA.Regularity.Envelope
public import GordieHowe.Applications.MLDSA.Regularity.HintExpansion
public import GordieHowe.Applications.MLDSA.Signing.SampleInBallShape

@[expose] public section

/-!
# The regularity bound at ML-DSA-44, ML-DSA-65 and ML-DSA-87

At the concrete primitives with `SampleInBall = G` of
challenge shape and the concrete NTT, for every key `sk₀` with `s₁, s₂` in the
`η`-box and every commitment hash `c̃`, averaged over the matrix `Â` (with `t₀` recomputed from
`Â s₁ + s₂`):

    𝔼_Â ∑_v |realMass v c̃ - ρ_z standinMass v c̃| ≤ K |V| · Λ √Env,

with `K = standinScale`, `|V| = 16^(256k)`, `Λ ≤ 11` (resp. `12`) and `Env = 2^-246`
(resp. `2^-406`): the relative column error is at most `11 · 2^-123` at ML-DSA-65 and
`12 · 2^-203` at ML-DSA-87. At ML-DSA-44 (`|V| = 44^(256k)`, `Λ ≤ 11`) the envelope is the hybrid
one, `Env = 2^-127 ≤ 2^-126` (`envelope_mldsa44`, `averagedSecondMoment_signerCells_le_hybrid`),
and the relative column error is at most `11 · 2^-63`.

At ML-DSA-65 and ML-DSA-87 the bound holds in `ℓ²` form,
`𝔼_Â (∑_v |realMass v c̃ - ρ_z standinMass v c̃|)² ≤ (K |V| R)²`
(`sum_sq_sum_abs_realMass_sub_le_mldsa65`, `sum_sq_sum_abs_realMass_sub_le_mldsa87`), also with
the commitment hash averaged inside (`expect_sq_sum_expect_abs_realMass_sub_le_mldsa65`, `_mldsa87`),
and then `𝔼_Â ringRegGap ≤ R / β_min · √(𝔼_Â (w Â)⁻²)` for every positive lower bound `w Â` on the
mean member weights (`expect_ringRegGap_le_sqrt_mldsa65`, `_mldsa87`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA
open LatticeCrypto TransformOps

attribute [local instance] concreteNTTRingOps

/-- **The signing laws with `SampleInBall = G`**: at every approved parameter set, the concrete
primitives with `SampleInBall` replaced by any `G` of challenge shape satisfy the signing laws:
the transform and `hide_low` laws are those of the concrete primitives (`signingLaws_concrete`),
and the challenge product bound is `norm_challenge_coeffScalarVecMul_le` (`β = τη`). -/
theorem signingLaws_concreteWithSampleInBall (p : Params) (hp : p.isApproved)
    {G : CommitHashBytes p → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall p G)) :
    SigningLaws (concreteWithSampleInBall p G) where
  transform := concreteNTTRingLaws
  hide_low := (signingLaws_concrete p hp).hide_low
  sampleInBall_smul_bound cTilde k s hs := by
    have := concreteNTTRingLaws
    exact norm_challenge_coeffScalarVecMul_le concreteNTTRingOps _ s (hG.norm_le_one cTilde)
      (hG.weight_le cTilde) hs

theorem mldsa65_vals : mldsa65.k = 6 ∧ mldsa65.l = 5 ∧ mldsa65.gamma1 = 524288 ∧
    mldsa65.gamma2 = 261888 ∧ mldsa65.beta = 196 ∧ mldsa65.omega = 55 := by
  simp only [mldsa65, ParameterSet.params, modulus]; decide

theorem bucketCount_mldsa65 : bucketCount mldsa65 = 16 := by
  simp only [bucketCount, mldsa65, ParameterSet.params, modulus]

instance : NeZero (bucketCount mldsa65) := ⟨by rw [bucketCount_mldsa65]; decide⟩

instance : Nonempty (CoeffIndex mldsa65) := ⟨(⟨0, by rw [mldsa65_vals.1]; decide⟩, ⟨0, by decide⟩)⟩

instance : Nonempty (MaskBox mldsa65) := maskBox_nonempty (by rw [mldsa65_vals.2.2.1]; decide)

theorem cellSize_mldsa65 : cellSize mldsa65 = 523383 := by
  obtain ⟨-, -, -, h2, hb, -⟩ := mldsa65_vals
  rw [cellSize, h2, hb]
  norm_num

theorem sum_hintKernel_le_mldsa65 :
    ∑ a : Coeff, hintKernel ((modulus : ℝ) / cellSize mldsa65) a ≤ 610 := by
  have hp := SigningParams.of_isApproved (p := mldsa65) (Or.inr (Or.inl rfl))
  have hf := isKernelBound_hintKernel hp
  refine sum_le_610 hf.nonneg hf.le_one hf.mul_abs_valMinAbs_le ?_
  rw [cellSize_mldsa65, show ((modulus : ℕ) : ℝ) = 8380417 by norm_num [modulus]]
  norm_num

theorem smallSupportDelta_le :
    (∀ t, 0 ≤ smallSupportDelta t) ∧ smallSupportDelta 1 ≤ 1 / (2 ^ 256) ^ 2 ∧
      smallSupportDelta 2 ≤ 1 / 2 ^ 210 ∧ smallSupportDelta 3 ≤ 1 / 2 ^ 155 ∧
      smallSupportDelta 4 ≤ 1 / 2 ^ 52 := by
  refine ⟨fun t => ?_, ?_, ?_, ?_, ?_⟩
  · unfold smallSupportDelta; split_ifs <;> positivity
  · simp only [smallSupportDelta, le_refl, if_true]
    rw [← pow_mul]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
  · simp [smallSupportDelta]
  · simp [smallSupportDelta]
  · simp [smallSupportDelta]

open Classical in
/-- **The averaged second moment at ML-DSA-65**: at most `2^-246`. -/
theorem averagedSecondMoment_signerCells_le_mldsa65
    (sk₀ : SecretKey mldsa65) (cTilde : CommitHashBytes mldsa65)
    {G : CommitHashBytes mldsa65 → ChallengePoly}
    (ha : ∀ x, |cs2Shift (concreteWithSampleInBall mldsa65 G) sk₀ cTilde x| ≤ mldsa65.beta)
    (hs1 : polyVecNorm ((concreteWithSampleInBall mldsa65 G).sampleInBall cTilde • sk₀.s1) ≤ mldsa65.beta)
    (t : ZMod 1537) (τ : Fin mldsa65.k → Rq) :
    averagedSecondMoment maskSlotEquiv
        (zBox mldsa65 ((concreteWithSampleInBall mldsa65 G).sampleInBall cTilde • sk₀.s1)) slotRoot
        (cellKernels (fun ic r => signerCells G sk₀ cTilde t τ ic r) (cellSize mldsa65))
        (keySlot (fun b => sk₀.s1.get b)) 0 ≤ 1 / 2 ^ 246 := by
  have hp := SigningParams.of_isApproved (p := mldsa65) (Or.inr (Or.inl rfl))
  refine (averagedSecondMoment_signerCells_le hp sk₀ cTilde ha hs1
    t τ (by norm_num) sum_hintKernel_le_mldsa65 (by rw [cellSize_mldsa65]; norm_num)).trans ?_
  obtain ⟨hk, hl, hg1, hg2, hb, -⟩ := mldsa65_vals
  obtain ⟨hδ0, hδ1, hδ2, hδ3, hδ4⟩ := smallSupportDelta_le
  have hG : 2 * (mldsa65.gamma1 - mldsa65.beta) - 1 = 1048183 := by rw [hg1, hb]
  have hT : (modulus : ℝ) ^ 2 / (Fintype.card (Fin (bucketCount mldsa65)) * cellSize mldsa65 ^ 2) =
      8380417 ^ 2 / (16 * 523383 ^ 2) := by
    rw [Fintype.card_fin, bucketCount_mldsa65, cellSize_mldsa65,
      show ((modulus : ℕ) : ℝ) = 8380417 by norm_num [modulus]]
    norm_num
  rw [hk, hl, hG, hT, show ringDegree = 256 from rfl]
  exact envelope_mldsa65 hδ0 hδ1 hδ2 hδ3 hδ4 (by norm_num) le_rfl

theorem card_coeffIndex_mldsa65 : Fintype.card (CoeffIndex mldsa65) = 1536 := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mldsa65_vals.1]
  rfl

theorem toReal_uniformScale (p : Params) :
    (uniformScale p).toReal = (cellSize p / modulus) ^ Fintype.card (CoeffIndex p) := by
  rw [uniformScale, ENNReal.toReal_ofReal (by positivity), cellSize]

/-- **Regularity at ML-DSA-65, `ℓ²` form.** At the concrete primitives with `SampleInBall = G` of
challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box and every
commitment hash `c̃`, over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â (∑_v |realMass v c̃ - ρ_z standinMass v c̃|)² ≤ (K |V| · 11 · 2^-123)²`. -/
theorem sum_sq_sum_abs_realMass_sub_le_mldsa65 (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    (cTilde : CommitHashBytes mldsa65) {G : CommitHashBytes mldsa65 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa65 G)) :
    ∑ aHat : TqMatrix mldsa65.k mldsa65.l, (∑ v : BucketVec mldsa65,
        |(realMass (concreteWithSampleInBall mldsa65 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v cTilde).toReal -
          (zAcceptFraction mldsa65 * standinMass (concreteWithSampleInBall mldsa65 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal|) ^ 2 ≤
      Fintype.card (TqMatrix mldsa65.k mldsa65.l) *
        ((standinScale mldsa65).toReal * Fintype.card (BucketVec mldsa65) *
          (11 / 2 ^ 123)) ^ 2 := by
  have := concreteNTTRingLaws
  have hp := SigningParams.of_isApproved (p := mldsa65) (Or.inr (Or.inl rfl))
  have hlaws := signingLaws_concreteWithSampleInBall mldsa65 (Or.inr (Or.inl rfl)) hG
  have hs1' := SigningLaws.polyVecNorm_sampleInBall_smul_le (concreteWithSampleInBall mldsa65 G) hlaws
    cTilde sk₀.s1 hs1
  have ha := fun x => SigningLaws.abs_cs2Shift_le (concreteWithSampleInBall mldsa65 G) sk₀ hlaws hs2 cTilde x
  have hω : mldsa65.omega < 1537 := by rw [mldsa65_vals.2.2.2.2.2]; norm_num
  have hN : Fintype.card (CoeffIndex mldsa65) < 1537 := by rw [card_coeffIndex_mldsa65]; norm_num
  have h := sum_sq_sum_abs_realMass_sub_le (M := 1537) hp hω hN sk₀ cTilde hs1' (cellSize_pos hp)
    (by positivity) fun t τ =>
      averagedSecondMoment_signerCells_le_mldsa65 sk₀ cTilde ha hs1' t τ
  refine h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ 2) (Nat.cast_nonneg _))
  · exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)) (mul_nonneg (pow_nonneg (div_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (cellSize_pos hp).le) (Nat.cast_nonneg _)) _)
        (Real.sqrt_nonneg _))
  have hΛ : ∑ t : ZMod 1537, ‖ZMod.countCoeff 1537 mldsa65.omega t‖ ≤ 11 := by
    rw [mldsa65_vals.2.2.2.2.2]; exact sum_norm_countCoeff_le_mldsa65
  have hsq : √(1 / 2 ^ 246 : ℝ) = 1 / 2 ^ 123 := by
    rw [show (1 / 2 ^ 246 : ℝ) = (1 / 2 ^ 123) ^ 2 by norm_num, Real.sqrt_sq (by positivity)]
  have hV : (Fintype.card (BucketVec mldsa65) : ℝ) = 16 ^ (mldsa65.k * ringDegree) := by
    rw [card_bucketVec, bucketCount_mldsa65]
    push_cast
    try rfl
  rw [standinScale, ENNReal.toReal_mul, toReal_uniformScale, hV, hsq, bucketCount_mldsa65,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hρ : 0 ≤ (zAcceptFraction mldsa65).toReal := ENNReal.toReal_nonneg
  have hL := cellSize_pos hp
  generalize mldsa65.k * ringDegree = n
  generalize (zAcceptFraction mldsa65).toReal = ρ at hρ ⊢
  generalize cellSize mldsa65 = L at hL ⊢
  have hq : (0 : ℝ) < (modulus : ℕ) := by norm_num [modulus]
  generalize ((modulus : ℕ) : ℝ) = qq at hq ⊢
  have hpow : (((16 : ℕ) : ℝ) * L / qq) ^ n = (L / qq) ^ n * 16 ^ n := by
    rw [← mul_pow]; congr 1; push_cast; ring
  rw [hpow]
  generalize ∑ t : ZMod 1537, ‖ZMod.countCoeff 1537 mldsa65.omega t‖ = Λ at hΛ ⊢
  have hX : 0 ≤ (L / qq) ^ n * 16 ^ n * (1 / 2 ^ 123 : ℝ) := by positivity
  calc ρ * Λ * ((L / qq) ^ n * 16 ^ n * (1 / 2 ^ 123))
      ≤ ρ * 11 * ((L / qq) ^ n * 16 ^ n * (1 / 2 ^ 123)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛ hρ) hX
    _ = _ := by ring

/-- **Regularity at ML-DSA-65.** At the concrete primitives with `SampleInBall = G` of
challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box and every
commitment hash `c̃`, averaged over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â ∑_v |realMass v c̃ - ρ_z standinMass v c̃| ≤ K |V| · 11 · 2^-123`. -/
theorem sum_abs_realMass_sub_le_mldsa65 (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    (cTilde : CommitHashBytes mldsa65) {G : CommitHashBytes mldsa65 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa65 G)) :
    ∑ aHat : TqMatrix mldsa65.k mldsa65.l, ∑ v : BucketVec mldsa65,
        |(realMass (concreteWithSampleInBall mldsa65 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v cTilde).toReal -
          (zAcceptFraction mldsa65 * standinMass (concreteWithSampleInBall mldsa65 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal| ≤
      Fintype.card (TqMatrix mldsa65.k mldsa65.l) *
        ((standinScale mldsa65).toReal * Fintype.card (BucketVec mldsa65)) * (11 / 2 ^ 123) := by
  have h := sum_sq_sum_abs_realMass_sub_le_mldsa65 sk₀ hs1 hs2 cTilde hG
  rw [← Finset.card_univ (α := TqMatrix mldsa65.k mldsa65.l)] at h
  have h1 := Finset.sum_le_card_mul_of_sum_sq_le
    (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)) (by norm_num)) h
  rw [Finset.card_univ] at h1
  exact h1.trans_eq (by ring)

/-- **The mean square column error at ML-DSA-65**: with `SampleInBall = G` of challenge shape and
the concrete NTT, for every key with `s₁, s₂` in the `η`-box, averaged over the matrix `Â` (with
`t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â (∑_v 𝔼_c̃ |realMass v c̃ - ρ_z standinMass v c̃|)² ≤ (K |V| · 11 · 2^-123)²`. -/
theorem expect_sq_sum_expect_abs_realMass_sub_le_mldsa65 (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {G : CommitHashBytes mldsa65 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa65 G)) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, (∑ v : BucketVec mldsa65, 𝔼 c,
        |(realMass (concreteWithSampleInBall mldsa65 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction mldsa65 * standinMass (concreteWithSampleInBall mldsa65 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal|) ^ 2 ≤
      ((standinScale mldsa65).toReal * Fintype.card (BucketVec mldsa65) * (11 / 2 ^ 123)) ^ 2 :=
  Finset.expect_sq_sum_expect_le _ fun c =>
    sum_sq_sum_abs_realMass_sub_le_mldsa65 sk₀ hs1 hs2 c hG

/-- **The mean regularity gap at ML-DSA-65 by Cauchy–Schwarz over the matrix.** With
`SampleInBall = G` of challenge shape and the concrete NTT, for keys with `s₁, s₂` in the
`η`-box, `t₀` recomputed from the uniform matrix `Â`, and any positive lower bound `w Â` on the
mean member weights of every bucket vector,
`𝔼_Â ringRegGap ≤ 11 · 2^-123 / β_min · √(𝔼_Â (w Â)⁻²)`. -/
theorem expect_ringRegGap_le_sqrt_mldsa65 (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {G : CommitHashBytes mldsa65 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa65 G))
    {βmin : ℚ≥0} (hβ0 : (βmin : ENNReal) ≠ 0) (hβt : (βmin : ENNReal) ≠ ⊤)
    {w : TqMatrix mldsa65.k mldsa65.l → ℝ}
    (hw0 : ∀ aHat, 0 < w aHat)
    (hw : ∀ (aHat : TqMatrix mldsa65.k mldsa65.l) v, w aHat ≤ 𝔼 c,
      (memberWeight (concreteWithSampleInBall mldsa65 G) βmin
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 (v, c) : ENNReal).toReal) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, ringRegGap (concreteWithSampleInBall mldsa65 G)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) aHat βmin ≤
      11 / 2 ^ 123 / (βmin : ENNReal).toReal *
        √(𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, (w aHat ^ 2)⁻¹) :=
  expect_ringRegGap_le_sqrt
    (SigningParams.of_isApproved (p := mldsa65) (Or.inr (Or.inl rfl))) _
    (fun aHat => keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) hβ0 hβt hw0 hw
    (by norm_num)
    (expect_sq_sum_expect_abs_realMass_sub_le_mldsa65 sk₀ hs1 hs2 hG)

/-- **The `μ`-free numerator at ML-DSA-65**: with `SampleInBall = G`
of challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box, summed
over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`) and averaged over the commitment
hash:
`∑_Â ∑_v 𝔼_c̃ |realMass v c̃ - ρ_z standinMass v c̃| ≤ |T_q^(k×ℓ)| · K |V| · 11 · 2^-123`. -/
theorem sum_expect_abs_realMass_sub_le_mldsa65 (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {G : CommitHashBytes mldsa65 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa65 G)) :
    ∑ aHat : TqMatrix mldsa65.k mldsa65.l, ∑ v : BucketVec mldsa65, 𝔼 c,
        |(realMass (concreteWithSampleInBall mldsa65 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction mldsa65 * standinMass (concreteWithSampleInBall mldsa65 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal| ≤
      Fintype.card (TqMatrix mldsa65.k mldsa65.l) *
        ((standinScale mldsa65).toReal * Fintype.card (BucketVec mldsa65) * (11 / 2 ^ 123)) := by
  rw [← Finset.expect_const (Finset.univ_nonempty (α := CommitHashBytes mldsa65))
    ((Fintype.card (TqMatrix mldsa65.k mldsa65.l) : ℝ) *
      ((standinScale mldsa65).toReal * Fintype.card (BucketVec mldsa65) * (11 / 2 ^ 123)))]
  calc _ = 𝔼 c : CommitHashBytes mldsa65, ∑ aHat : TqMatrix mldsa65.k mldsa65.l, ∑ v : BucketVec mldsa65,
        |(realMass (concreteWithSampleInBall mldsa65 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction mldsa65 * standinMass (concreteWithSampleInBall mldsa65 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal| := by
        rw [Finset.expect_sum_comm]
        refine Finset.sum_congr rfl fun aHat _ => ?_
        rw [Finset.expect_sum_comm]
    _ ≤ _ := Finset.expect_le_expect fun c _ =>
        (sum_abs_realMass_sub_le_mldsa65 sk₀ hs1 hs2 c hG).trans_eq (by ring)

/-- **The averaged regularity gap at ML-DSA-65.** For keys with `s₁, s₂` in the `η`-box, `t₀`
recomputed from the uniform matrix `Â`, and mean member weights at least `μ > 0`,
`𝔼_Â ringRegGap ≤ 11 · 2^-123 / (μ β_min)`. -/
theorem expect_ringRegGap_le_mldsa65 (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {βmin : ℚ≥0} (hβ0 : (βmin : ENNReal) ≠ 0) (hβt : (βmin : ENNReal) ≠ ⊤) {μ : ℝ} (hμ : 0 < μ)
    (hmw : ∀ (aHat : TqMatrix mldsa65.k mldsa65.l) v, μ ≤ 𝔼 c,
      (memberWeight (concretePrimitives mldsa65) βmin
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 (v, c) : ENNReal).toReal) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, ringRegGap (concretePrimitives mldsa65)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) aHat βmin ≤
      11 / 2 ^ 123 / (μ * (βmin : ENNReal).toReal) := by
  have hp := SigningParams.of_isApproved (p := mldsa65) (Or.inr (Or.inl rfl))
  set sk := fun aHat : TqMatrix mldsa65.k mldsa65.l =>
    keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))
  set K := (standinScale mldsa65).toReal
  set V : ℝ := ((Fintype.card (BucketVec mldsa65) : ℕ) : ℝ)
  set T : ℝ := ((Fintype.card (TqMatrix mldsa65.k mldsa65.l) : ℕ) : ℝ)
  set Cs : ℝ := ((Fintype.card (CommitHashBytes mldsa65) : ℕ) : ℝ)
  have hK : 0 < K := standinScale_pos hp
  have hV : 0 < V := Nat.cast_pos.mpr (Fintype.card_pos (α := BucketVec mldsa65))
  have hT : 0 < T := Nat.cast_pos.mpr (Fintype.card_pos (α := TqMatrix mldsa65.k mldsa65.l))
  have hCs : 0 < Cs := Nat.cast_pos.mpr (Fintype.card_pos (α := CommitHashBytes mldsa65))
  have hβ : 0 < (βmin : ENNReal).toReal := ENNReal.toReal_pos hβ0 hβt
  set D := μ * ((standinScale mldsa65 * βmin).toReal * V)
  have hD : 0 < D := by simp only [D]; rw [ENNReal.toReal_mul]; positivity
  set E : TqMatrix mldsa65.k mldsa65.l → BucketVec mldsa65 → CommitHashBytes mldsa65 → ℝ :=
    fun aHat v c => |(realMass (concretePrimitives mldsa65) (sk aHat) aHat v c).toReal -
      (zAcceptFraction mldsa65 * standinMass (concretePrimitives mldsa65) (sk aHat) v c).toReal|
  have hstep : ∀ aHat, ringRegGap (concretePrimitives mldsa65) (sk aHat) aHat βmin ≤
      (∑ v, 𝔼 c, E aHat v c) / D := fun aHat =>
    ringRegGap_le hp _ (sk aHat) aHat hβ0 hβt hμ (hmw aHat)
  have hsum : ∑ aHat, ∑ v, 𝔼 c, E aHat v c ≤ T * (K * V * (11 / 2 ^ 123)) := by
    have h := sum_expect_abs_realMass_sub_le_mldsa65 sk₀ hs1 hs2
      (G := (concretePrimitives mldsa65).sampleInBall)
      (by rw [concreteWithSampleInBall_concrete]; exact sampleInBallShape_concrete mldsa65)
    rw [concreteWithSampleInBall_concrete] at h
    exact h
  calc 𝔼 aHat, ringRegGap (concretePrimitives mldsa65) (sk aHat) aHat βmin
      ≤ 𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, (∑ v, 𝔼 c, E aHat v c) / D :=
        Finset.expect_le_expect fun aHat _ => hstep aHat
    _ = (∑ aHat, ∑ v, 𝔼 c, E aHat v c) / T / D := by
        rw [Finset.expect_eq_sum_div_card, ← Finset.sum_div, Finset.card_univ]
        ring
    _ ≤ T * (K * V * (11 / 2 ^ 123)) / T / D := by gcongr
    _ = 11 / 2 ^ 123 / (μ * (βmin : ENNReal).toReal) := by
        simp only [D]
        rw [ENNReal.toReal_mul]
        field_simp
        exact div_self hK.ne'


theorem mldsa44_vals : _root_.MLDSA.mldsa44.k = 4 ∧ _root_.MLDSA.mldsa44.l = 4 ∧ _root_.MLDSA.mldsa44.gamma1 = 131072 ∧
    _root_.MLDSA.mldsa44.gamma2 = 95232 ∧ _root_.MLDSA.mldsa44.beta = 78 ∧ _root_.MLDSA.mldsa44.omega = 80 := by
  simp only [_root_.MLDSA.mldsa44, ParameterSet.params, modulus]; decide

theorem bucketCount_mldsa44 : bucketCount _root_.MLDSA.mldsa44 = 44 := by
  simp only [bucketCount, _root_.MLDSA.mldsa44, ParameterSet.params, modulus]

instance : NeZero (bucketCount _root_.MLDSA.mldsa44) := ⟨by rw [bucketCount_mldsa44]; decide⟩

instance : Nonempty (CoeffIndex _root_.MLDSA.mldsa44) := ⟨(⟨0, by rw [mldsa44_vals.1]; decide⟩, ⟨0, by decide⟩)⟩

instance : Nonempty (MaskBox _root_.MLDSA.mldsa44) := maskBox_nonempty (by rw [mldsa44_vals.2.2.1]; decide)

theorem cellSize_mldsa44 : cellSize _root_.MLDSA.mldsa44 = 190307 := by
  obtain ⟨-, -, -, h2, hb, -⟩ := mldsa44_vals
  rw [cellSize, h2, hb]
  norm_num

theorem sum_hintKernel_le_mldsa44 :
    ∑ a : Coeff, hintKernel ((modulus : ℝ) / cellSize _root_.MLDSA.mldsa44) a ≤ 1620 := by
  have hp := SigningParams.of_isApproved (p := _root_.MLDSA.mldsa44) (Or.inl rfl)
  have hf := isKernelBound_hintKernel hp
  refine sum_le_1620 hf.nonneg hf.le_one hf.mul_abs_valMinAbs_le ?_
  rw [cellSize_mldsa44, show ((modulus : ℕ) : ℝ) = 8380417 by norm_num [modulus]]

theorem smallSupportDelta_one_le_mldsa44 : smallSupportDelta 1 ≤ 1 / 2 ^ 512 := by
  simp only [smallSupportDelta, le_refl, if_true]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))

open Classical in
/-- **The averaged second moment at ML-DSA-44**: at most `2^-127`, by the hybrid route
(`averagedSecondMoment_signerCells_le_hybrid`, `envelope_mldsa44`). -/
theorem averagedSecondMoment_signerCells_le_mldsa44
    (sk₀ : SecretKey _root_.MLDSA.mldsa44) (cTilde : CommitHashBytes _root_.MLDSA.mldsa44)
    {G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengePoly}
    (ha : ∀ x, |cs2Shift (concreteWithSampleInBall _root_.MLDSA.mldsa44 G) sk₀ cTilde x| ≤ _root_.MLDSA.mldsa44.beta)
    (hs1 : polyVecNorm ((concreteWithSampleInBall _root_.MLDSA.mldsa44 G).sampleInBall cTilde • sk₀.s1) ≤ _root_.MLDSA.mldsa44.beta)
    (t : ZMod 1025) (τ : Fin _root_.MLDSA.mldsa44.k → Rq) :
    averagedSecondMoment maskSlotEquiv
        (zBox _root_.MLDSA.mldsa44 ((concreteWithSampleInBall _root_.MLDSA.mldsa44 G).sampleInBall cTilde • sk₀.s1)) slotRoot
        (cellKernels (fun ic r => signerCells G sk₀ cTilde t τ ic r) (cellSize _root_.MLDSA.mldsa44))
        (keySlot (fun b => sk₀.s1.get b)) 0 ≤ 1 / 2 ^ 127 := by
  have hp := SigningParams.of_isApproved (p := _root_.MLDSA.mldsa44) (Or.inl rfl)
  refine (averagedSecondMoment_signerCells_le_hybrid hp sk₀ cTilde ha hs1
    t τ (by norm_num) sum_hintKernel_le_mldsa44 (by rw [cellSize_mldsa44])).trans ?_
  obtain ⟨hk, hl, hg1, hg2, hb, -⟩ := mldsa44_vals
  obtain ⟨hδ0, -, hδ2, hδ3, hδ4⟩ := smallSupportDelta_le
  have hG : 2 * (_root_.MLDSA.mldsa44.gamma1 - _root_.MLDSA.mldsa44.beta) - 1 = 261987 := by rw [hg1, hb]
  have hT : (modulus : ℝ) ^ 2 / (Fintype.card (Fin (bucketCount _root_.MLDSA.mldsa44)) * cellSize _root_.MLDSA.mldsa44 ^ 2) =
      8380417 ^ 2 / (44 * 190307 ^ 2) := by
    rw [Fintype.card_fin, bucketCount_mldsa44, cellSize_mldsa44,
      show ((modulus : ℕ) : ℝ) = 8380417 by norm_num [modulus]]
    norm_num
  have hS₂ : (modulus : ℝ) / cellSize _root_.MLDSA.mldsa44 = 8380417 / 190307 := by
    rw [cellSize_mldsa44, show ((modulus : ℕ) : ℝ) = 8380417 by norm_num [modulus]]
  rw [hk, hl, hG, hT, hS₂, show ringDegree = 256 from rfl]
  exact envelope_mldsa44 hδ0 smallSupportDelta_one_le_mldsa44 hδ2 hδ3 hδ4 (by norm_num)
    le_rfl (by positivity) le_rfl

theorem card_coeffIndex_mldsa44 : Fintype.card (CoeffIndex _root_.MLDSA.mldsa44) = 1024 := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mldsa44_vals.1]
  rfl

/-- **Regularity at ML-DSA-44.** At the concrete primitives with `SampleInBall = G` of
challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box and every
commitment hash `c̃`, averaged over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â ∑_v |realMass v c̃ - ρ_z standinMass v c̃| ≤ K |V| · 11 · 2^-63`. -/
theorem sum_abs_realMass_sub_le_mldsa44 (sk₀ : SecretKey _root_.MLDSA.mldsa44)
    (hs1 : polyVecBounded sk₀.s1 _root_.MLDSA.mldsa44.eta) (hs2 : polyVecBounded sk₀.s2 _root_.MLDSA.mldsa44.eta)
    (cTilde : CommitHashBytes _root_.MLDSA.mldsa44) {G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall _root_.MLDSA.mldsa44 G)) :
    ∑ aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l, ∑ v : BucketVec _root_.MLDSA.mldsa44,
        |(realMass (concreteWithSampleInBall _root_.MLDSA.mldsa44 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v cTilde).toReal -
          (zAcceptFraction _root_.MLDSA.mldsa44 * standinMass (concreteWithSampleInBall _root_.MLDSA.mldsa44 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal| ≤
      Fintype.card (TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l) *
        ((standinScale _root_.MLDSA.mldsa44).toReal * Fintype.card (BucketVec _root_.MLDSA.mldsa44)) * (11 / 2 ^ 63) := by
  have := concreteNTTRingLaws
  have hp := SigningParams.of_isApproved (p := _root_.MLDSA.mldsa44) (Or.inl rfl)
  have hlaws := signingLaws_concreteWithSampleInBall _root_.MLDSA.mldsa44 (Or.inl rfl) hG
  have hs1' := SigningLaws.polyVecNorm_sampleInBall_smul_le (concreteWithSampleInBall _root_.MLDSA.mldsa44 G) hlaws
    cTilde sk₀.s1 hs1
  have ha := fun x => SigningLaws.abs_cs2Shift_le (concreteWithSampleInBall _root_.MLDSA.mldsa44 G) sk₀ hlaws hs2 cTilde x
  have hω : _root_.MLDSA.mldsa44.omega < 1025 := by rw [mldsa44_vals.2.2.2.2.2]; norm_num
  have hN : Fintype.card (CoeffIndex _root_.MLDSA.mldsa44) < 1025 := by rw [card_coeffIndex_mldsa44]; norm_num
  have h := sum_abs_realMass_sub_le (M := 1025) (Env := 1 / 2 ^ 126) hp hω hN sk₀ cTilde hs1' (cellSize_pos hp)
    (by positivity) fun t τ =>
      (averagedSecondMoment_signerCells_le_mldsa44 sk₀ cTilde ha hs1' t τ).trans
        (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (show 126 ≤ 127 by norm_num)))
  refine h.trans ?_
  have hΛ : ∑ t : ZMod 1025, ‖ZMod.countCoeff 1025 _root_.MLDSA.mldsa44.omega t‖ ≤ 11 := by
    rw [mldsa44_vals.2.2.2.2.2]; exact sum_norm_countCoeff_le_mldsa44
  have hsq : √(1 / 2 ^ 126 : ℝ) = 1 / 2 ^ 63 := by
    rw [show (1 / 2 ^ 126 : ℝ) = (1 / 2 ^ 63) ^ 2 by norm_num, Real.sqrt_sq (by positivity)]
  have hV : (Fintype.card (BucketVec _root_.MLDSA.mldsa44) : ℝ) = 44 ^ (_root_.MLDSA.mldsa44.k * ringDegree) := by
    rw [card_bucketVec, bucketCount_mldsa44]
    push_cast
    try rfl
  rw [standinScale, ENNReal.toReal_mul, toReal_uniformScale, hV, hsq, bucketCount_mldsa44,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hρ : 0 ≤ (zAcceptFraction _root_.MLDSA.mldsa44).toReal := ENNReal.toReal_nonneg
  have hL := cellSize_pos hp
  have hT : (0 : ℝ) ≤ Fintype.card (TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l) := Nat.cast_nonneg _
  generalize _root_.MLDSA.mldsa44.k * ringDegree = n
  generalize (zAcceptFraction _root_.MLDSA.mldsa44).toReal = ρ at hρ ⊢
  generalize cellSize _root_.MLDSA.mldsa44 = L at hL ⊢
  have hq : (0 : ℝ) < (modulus : ℕ) := by norm_num [modulus]
  generalize ((modulus : ℕ) : ℝ) = qq at hq ⊢
  have hpow : (((44 : ℕ) : ℝ) * L / qq) ^ n = (L / qq) ^ n * 44 ^ n := by
    rw [← mul_pow]; congr 1; push_cast; ring
  rw [hpow]
  generalize Fintype.card (TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l) = T
  generalize ∑ t : ZMod 1025, ‖ZMod.countCoeff 1025 _root_.MLDSA.mldsa44.omega t‖ = Λ at hΛ ⊢
  have hX : 0 ≤ (L / qq) ^ n * 44 ^ n * (1 / 2 ^ 63 : ℝ) := by positivity
  calc (T : ℝ) * (ρ * Λ * ((L / qq) ^ n * 44 ^ n * (1 / 2 ^ 63)))
      ≤ T * (ρ * 11 * ((L / qq) ^ n * 44 ^ n * (1 / 2 ^ 63))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛ hρ) hX)
          (Nat.cast_nonneg T)
    _ = _ := by ring

/-- **The `μ`-free numerator at ML-DSA-44**: with `SampleInBall = G`
of challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box, summed
over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`) and averaged over the commitment
hash:
`∑_Â ∑_v 𝔼_c̃ |realMass v c̃ - ρ_z standinMass v c̃| ≤ |T_q^(k×ℓ)| · K |V| · 11 · 2^-63`. -/
theorem sum_expect_abs_realMass_sub_le_mldsa44 (sk₀ : SecretKey _root_.MLDSA.mldsa44)
    (hs1 : polyVecBounded sk₀.s1 _root_.MLDSA.mldsa44.eta) (hs2 : polyVecBounded sk₀.s2 _root_.MLDSA.mldsa44.eta)
    {G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall _root_.MLDSA.mldsa44 G)) :
    ∑ aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l, ∑ v : BucketVec _root_.MLDSA.mldsa44, 𝔼 c,
        |(realMass (concreteWithSampleInBall _root_.MLDSA.mldsa44 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction _root_.MLDSA.mldsa44 * standinMass (concreteWithSampleInBall _root_.MLDSA.mldsa44 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal| ≤
      Fintype.card (TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l) *
        ((standinScale _root_.MLDSA.mldsa44).toReal * Fintype.card (BucketVec _root_.MLDSA.mldsa44) * (11 / 2 ^ 63)) := by
  rw [← Finset.expect_const (Finset.univ_nonempty (α := CommitHashBytes _root_.MLDSA.mldsa44))
    ((Fintype.card (TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l) : ℝ) *
      ((standinScale _root_.MLDSA.mldsa44).toReal * Fintype.card (BucketVec _root_.MLDSA.mldsa44) * (11 / 2 ^ 63)))]
  calc _ = 𝔼 c : CommitHashBytes _root_.MLDSA.mldsa44, ∑ aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l, ∑ v : BucketVec _root_.MLDSA.mldsa44,
        |(realMass (concreteWithSampleInBall _root_.MLDSA.mldsa44 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction _root_.MLDSA.mldsa44 * standinMass (concreteWithSampleInBall _root_.MLDSA.mldsa44 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal| := by
        rw [Finset.expect_sum_comm]
        refine Finset.sum_congr rfl fun aHat _ => ?_
        rw [Finset.expect_sum_comm]
    _ ≤ _ := Finset.expect_le_expect fun c _ =>
        (sum_abs_realMass_sub_le_mldsa44 sk₀ hs1 hs2 c hG).trans_eq (by ring)

/-- **The averaged regularity gap at ML-DSA-44.** For keys with `s₁, s₂` in the `η`-box, `t₀`
recomputed from the uniform matrix `Â`, and mean member weights at least `μ > 0`,
`𝔼_Â ringRegGap ≤ 11 · 2^-63 / (μ β_min)`. -/
theorem expect_ringRegGap_le_mldsa44 (sk₀ : SecretKey _root_.MLDSA.mldsa44)
    (hs1 : polyVecBounded sk₀.s1 _root_.MLDSA.mldsa44.eta) (hs2 : polyVecBounded sk₀.s2 _root_.MLDSA.mldsa44.eta)
    {βmin : ℚ≥0} (hβ0 : (βmin : ENNReal) ≠ 0) (hβt : (βmin : ENNReal) ≠ ⊤) {μ : ℝ} (hμ : 0 < μ)
    (hmw : ∀ (aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l) v, μ ≤ 𝔼 c,
      (memberWeight (concretePrimitives _root_.MLDSA.mldsa44) βmin
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 (v, c) : ENNReal).toReal) :
    𝔼 aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l, ringRegGap (concretePrimitives _root_.MLDSA.mldsa44)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) aHat βmin ≤
      11 / 2 ^ 63 / (μ * (βmin : ENNReal).toReal) := by
  have hp := SigningParams.of_isApproved (p := _root_.MLDSA.mldsa44) (Or.inl rfl)
  set sk := fun aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l =>
    keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))
  set K := (standinScale _root_.MLDSA.mldsa44).toReal
  set V : ℝ := ((Fintype.card (BucketVec _root_.MLDSA.mldsa44) : ℕ) : ℝ)
  set T : ℝ := ((Fintype.card (TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l) : ℕ) : ℝ)
  set Cs : ℝ := ((Fintype.card (CommitHashBytes _root_.MLDSA.mldsa44) : ℕ) : ℝ)
  have hK : 0 < K := standinScale_pos hp
  have hV : 0 < V := Nat.cast_pos.mpr (Fintype.card_pos (α := BucketVec _root_.MLDSA.mldsa44))
  have hT : 0 < T := Nat.cast_pos.mpr (Fintype.card_pos (α := TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l))
  have hCs : 0 < Cs := Nat.cast_pos.mpr (Fintype.card_pos (α := CommitHashBytes _root_.MLDSA.mldsa44))
  have hβ : 0 < (βmin : ENNReal).toReal := ENNReal.toReal_pos hβ0 hβt
  set D := μ * ((standinScale _root_.MLDSA.mldsa44 * βmin).toReal * V)
  have hD : 0 < D := by simp only [D]; rw [ENNReal.toReal_mul]; positivity
  set E : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l → BucketVec _root_.MLDSA.mldsa44 → CommitHashBytes _root_.MLDSA.mldsa44 → ℝ :=
    fun aHat v c => |(realMass (concretePrimitives _root_.MLDSA.mldsa44) (sk aHat) aHat v c).toReal -
      (zAcceptFraction _root_.MLDSA.mldsa44 * standinMass (concretePrimitives _root_.MLDSA.mldsa44) (sk aHat) v c).toReal|
  have hstep : ∀ aHat, ringRegGap (concretePrimitives _root_.MLDSA.mldsa44) (sk aHat) aHat βmin ≤
      (∑ v, 𝔼 c, E aHat v c) / D := fun aHat =>
    ringRegGap_le hp _ (sk aHat) aHat hβ0 hβt hμ (hmw aHat)
  have hsum : ∑ aHat, ∑ v, 𝔼 c, E aHat v c ≤ T * (K * V * (11 / 2 ^ 63)) := by
    have h := sum_expect_abs_realMass_sub_le_mldsa44 sk₀ hs1 hs2
      (G := (concretePrimitives _root_.MLDSA.mldsa44).sampleInBall)
      (by rw [concreteWithSampleInBall_concrete]; exact sampleInBallShape_concrete _root_.MLDSA.mldsa44)
    rw [concreteWithSampleInBall_concrete] at h
    exact h
  calc 𝔼 aHat, ringRegGap (concretePrimitives _root_.MLDSA.mldsa44) (sk aHat) aHat βmin
      ≤ 𝔼 aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l, (∑ v, 𝔼 c, E aHat v c) / D :=
        Finset.expect_le_expect fun aHat _ => hstep aHat
    _ = (∑ aHat, ∑ v, 𝔼 c, E aHat v c) / T / D := by
        rw [Finset.expect_eq_sum_div_card, ← Finset.sum_div, Finset.card_univ]
        ring
    _ ≤ T * (K * V * (11 / 2 ^ 63)) / T / D := by gcongr
    _ = 11 / 2 ^ 63 / (μ * (βmin : ENNReal).toReal) := by
        simp only [D]
        rw [ENNReal.toReal_mul]
        field_simp
        exact div_self hK.ne'


theorem mldsa87_vals : mldsa87.k = 8 ∧ mldsa87.l = 7 ∧ mldsa87.gamma1 = 524288 ∧
    mldsa87.gamma2 = 261888 ∧ mldsa87.beta = 120 ∧ mldsa87.omega = 75 := by
  simp only [mldsa87, ParameterSet.params, modulus]; decide

theorem bucketCount_mldsa87 : bucketCount mldsa87 = 16 := by
  simp only [bucketCount, mldsa87, ParameterSet.params, modulus]

instance : NeZero (bucketCount mldsa87) := ⟨by rw [bucketCount_mldsa87]; decide⟩

instance : Nonempty (CoeffIndex mldsa87) := ⟨(⟨0, by rw [mldsa87_vals.1]; decide⟩, ⟨0, by decide⟩)⟩

instance : Nonempty (MaskBox mldsa87) := maskBox_nonempty (by rw [mldsa87_vals.2.2.1]; decide)

theorem cellSize_mldsa87 : cellSize mldsa87 = 523535 := by
  obtain ⟨-, -, -, h2, hb, -⟩ := mldsa87_vals
  rw [cellSize, h2, hb]
  norm_num

theorem sum_hintKernel_le_mldsa87 :
    ∑ a : Coeff, hintKernel ((modulus : ℝ) / cellSize mldsa87) a ≤ 610 := by
  have hp := SigningParams.of_isApproved (p := mldsa87) (Or.inr (Or.inr rfl))
  have hf := isKernelBound_hintKernel hp
  refine sum_le_610 hf.nonneg hf.le_one hf.mul_abs_valMinAbs_le ?_
  rw [cellSize_mldsa87, show ((modulus : ℕ) : ℝ) = 8380417 by norm_num [modulus]]
  norm_num

open Classical in
/-- **The averaged second moment at ML-DSA-87**: at most `2^-406`. -/
theorem averagedSecondMoment_signerCells_le_mldsa87
    (sk₀ : SecretKey mldsa87) (cTilde : CommitHashBytes mldsa87)
    {G : CommitHashBytes mldsa87 → ChallengePoly}
    (ha : ∀ x, |cs2Shift (concreteWithSampleInBall mldsa87 G) sk₀ cTilde x| ≤ mldsa87.beta)
    (hs1 : polyVecNorm ((concreteWithSampleInBall mldsa87 G).sampleInBall cTilde • sk₀.s1) ≤ mldsa87.beta)
    (t : ZMod 2049) (τ : Fin mldsa87.k → Rq) :
    averagedSecondMoment maskSlotEquiv
        (zBox mldsa87 ((concreteWithSampleInBall mldsa87 G).sampleInBall cTilde • sk₀.s1)) slotRoot
        (cellKernels (fun ic r => signerCells G sk₀ cTilde t τ ic r) (cellSize mldsa87))
        (keySlot (fun b => sk₀.s1.get b)) 0 ≤ 1 / 2 ^ 406 := by
  have hp := SigningParams.of_isApproved (p := mldsa87) (Or.inr (Or.inr rfl))
  refine (averagedSecondMoment_signerCells_le hp sk₀ cTilde ha hs1
    t τ (by norm_num) sum_hintKernel_le_mldsa87 (by rw [cellSize_mldsa87]; norm_num)).trans ?_
  obtain ⟨hk, hl, hg1, hg2, hb, -⟩ := mldsa87_vals
  obtain ⟨hδ0, hδ1, hδ2, hδ3, hδ4⟩ := smallSupportDelta_le
  have hG : 2 * (mldsa87.gamma1 - mldsa87.beta) - 1 = 1048335 := by rw [hg1, hb]
  have hT : (modulus : ℝ) ^ 2 / (Fintype.card (Fin (bucketCount mldsa87)) * cellSize mldsa87 ^ 2) =
      8380417 ^ 2 / (16 * 523535 ^ 2) := by
    rw [Fintype.card_fin, bucketCount_mldsa87, cellSize_mldsa87,
      show ((modulus : ℕ) : ℝ) = 8380417 by norm_num [modulus]]
    norm_num
  rw [hk, hl, hG, hT, show ringDegree = 256 from rfl]
  exact envelope_mldsa87 hδ0 hδ1 hδ2 hδ3 hδ4 (by norm_num) le_rfl

theorem card_coeffIndex_mldsa87 : Fintype.card (CoeffIndex mldsa87) = 2048 := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mldsa87_vals.1]
  rfl

/-- **Regularity at ML-DSA-87, `ℓ²` form.** At the concrete primitives with `SampleInBall = G` of
challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box and every
commitment hash `c̃`, over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â (∑_v |realMass v c̃ - ρ_z standinMass v c̃|)² ≤ (K |V| · 12 · 2^-203)²`. -/
theorem sum_sq_sum_abs_realMass_sub_le_mldsa87 (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    (cTilde : CommitHashBytes mldsa87) {G : CommitHashBytes mldsa87 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa87 G)) :
    ∑ aHat : TqMatrix mldsa87.k mldsa87.l, (∑ v : BucketVec mldsa87,
        |(realMass (concreteWithSampleInBall mldsa87 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v cTilde).toReal -
          (zAcceptFraction mldsa87 * standinMass (concreteWithSampleInBall mldsa87 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal|) ^ 2 ≤
      Fintype.card (TqMatrix mldsa87.k mldsa87.l) *
        ((standinScale mldsa87).toReal * Fintype.card (BucketVec mldsa87) *
          (12 / 2 ^ 203)) ^ 2 := by
  have := concreteNTTRingLaws
  have hp := SigningParams.of_isApproved (p := mldsa87) (Or.inr (Or.inr rfl))
  have hlaws := signingLaws_concreteWithSampleInBall mldsa87 (Or.inr (Or.inr rfl)) hG
  have hs1' := SigningLaws.polyVecNorm_sampleInBall_smul_le (concreteWithSampleInBall mldsa87 G) hlaws
    cTilde sk₀.s1 hs1
  have ha := fun x => SigningLaws.abs_cs2Shift_le (concreteWithSampleInBall mldsa87 G) sk₀ hlaws hs2 cTilde x
  have hω : mldsa87.omega < 2049 := by rw [mldsa87_vals.2.2.2.2.2]; norm_num
  have hN : Fintype.card (CoeffIndex mldsa87) < 2049 := by rw [card_coeffIndex_mldsa87]; norm_num
  have h := sum_sq_sum_abs_realMass_sub_le (M := 2049) hp hω hN sk₀ cTilde hs1' (cellSize_pos hp)
    (by positivity) fun t τ =>
      averagedSecondMoment_signerCells_le_mldsa87 sk₀ cTilde ha hs1' t τ
  refine h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ 2) (Nat.cast_nonneg _))
  · exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)) (mul_nonneg (pow_nonneg (div_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (cellSize_pos hp).le) (Nat.cast_nonneg _)) _)
        (Real.sqrt_nonneg _))
  have hΛ : ∑ t : ZMod 2049, ‖ZMod.countCoeff 2049 mldsa87.omega t‖ ≤ 12 := by
    rw [mldsa87_vals.2.2.2.2.2]; exact sum_norm_countCoeff_le_mldsa87
  have hsq : √(1 / 2 ^ 406 : ℝ) = 1 / 2 ^ 203 := by
    rw [show (1 / 2 ^ 406 : ℝ) = (1 / 2 ^ 203) ^ 2 by rw [div_pow, one_pow, ← pow_mul],
      Real.sqrt_sq (by positivity)]
  have hV : (Fintype.card (BucketVec mldsa87) : ℝ) = 16 ^ (mldsa87.k * ringDegree) := by
    rw [card_bucketVec, bucketCount_mldsa87]
    push_cast
    try rfl
  rw [standinScale, ENNReal.toReal_mul, toReal_uniformScale, hV, hsq, bucketCount_mldsa87,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hρ : 0 ≤ (zAcceptFraction mldsa87).toReal := ENNReal.toReal_nonneg
  have hL := cellSize_pos hp
  generalize mldsa87.k * ringDegree = n
  generalize (zAcceptFraction mldsa87).toReal = ρ at hρ ⊢
  generalize cellSize mldsa87 = L at hL ⊢
  have hq : (0 : ℝ) < (modulus : ℕ) := by norm_num [modulus]
  generalize ((modulus : ℕ) : ℝ) = qq at hq ⊢
  have hpow : (((16 : ℕ) : ℝ) * L / qq) ^ n = (L / qq) ^ n * 16 ^ n := by
    rw [← mul_pow]; congr 1; push_cast; ring
  rw [hpow]
  generalize ∑ t : ZMod 2049, ‖ZMod.countCoeff 2049 mldsa87.omega t‖ = Λ at hΛ ⊢
  have hX : 0 ≤ (L / qq) ^ n * 16 ^ n * (1 / 2 ^ 203 : ℝ) := by positivity
  calc ρ * Λ * ((L / qq) ^ n * 16 ^ n * (1 / 2 ^ 203))
      ≤ ρ * 12 * ((L / qq) ^ n * 16 ^ n * (1 / 2 ^ 203)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛ hρ) hX
    _ = _ := by ring

/-- **Regularity at ML-DSA-87.** At the concrete primitives with `SampleInBall = G` of
challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box and every
commitment hash `c̃`, averaged over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â ∑_v |realMass v c̃ - ρ_z standinMass v c̃| ≤ K |V| · 12 · 2^-203`. -/
theorem sum_abs_realMass_sub_le_mldsa87 (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    (cTilde : CommitHashBytes mldsa87) {G : CommitHashBytes mldsa87 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa87 G)) :
    ∑ aHat : TqMatrix mldsa87.k mldsa87.l, ∑ v : BucketVec mldsa87,
        |(realMass (concreteWithSampleInBall mldsa87 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v cTilde).toReal -
          (zAcceptFraction mldsa87 * standinMass (concreteWithSampleInBall mldsa87 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal| ≤
      Fintype.card (TqMatrix mldsa87.k mldsa87.l) *
        ((standinScale mldsa87).toReal * Fintype.card (BucketVec mldsa87)) * (12 / 2 ^ 203) := by
  have h := sum_sq_sum_abs_realMass_sub_le_mldsa87 sk₀ hs1 hs2 cTilde hG
  rw [← Finset.card_univ (α := TqMatrix mldsa87.k mldsa87.l)] at h
  have h1 := Finset.sum_le_card_mul_of_sum_sq_le
    (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)) (by norm_num)) h
  rw [Finset.card_univ] at h1
  exact h1.trans_eq (by ring)

/-- **The mean square column error at ML-DSA-87**: with `SampleInBall = G` of challenge shape and
the concrete NTT, for every key with `s₁, s₂` in the `η`-box, averaged over the matrix `Â` (with
`t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â (∑_v 𝔼_c̃ |realMass v c̃ - ρ_z standinMass v c̃|)² ≤ (K |V| · 12 · 2^-203)²`. -/
theorem expect_sq_sum_expect_abs_realMass_sub_le_mldsa87 (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {G : CommitHashBytes mldsa87 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa87 G)) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, (∑ v : BucketVec mldsa87, 𝔼 c,
        |(realMass (concreteWithSampleInBall mldsa87 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction mldsa87 * standinMass (concreteWithSampleInBall mldsa87 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal|) ^ 2 ≤
      ((standinScale mldsa87).toReal * Fintype.card (BucketVec mldsa87) * (12 / 2 ^ 203)) ^ 2 :=
  Finset.expect_sq_sum_expect_le _ fun c =>
    sum_sq_sum_abs_realMass_sub_le_mldsa87 sk₀ hs1 hs2 c hG

/-- **The mean regularity gap at ML-DSA-87 by Cauchy–Schwarz over the matrix.** With
`SampleInBall = G` of challenge shape and the concrete NTT, for keys with `s₁, s₂` in the
`η`-box, `t₀` recomputed from the uniform matrix `Â`, and any positive lower bound `w Â` on the
mean member weights of every bucket vector,
`𝔼_Â ringRegGap ≤ 12 · 2^-203 / β_min · √(𝔼_Â (w Â)⁻²)`. -/
theorem expect_ringRegGap_le_sqrt_mldsa87 (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {G : CommitHashBytes mldsa87 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa87 G))
    {βmin : ℚ≥0} (hβ0 : (βmin : ENNReal) ≠ 0) (hβt : (βmin : ENNReal) ≠ ⊤)
    {w : TqMatrix mldsa87.k mldsa87.l → ℝ}
    (hw0 : ∀ aHat, 0 < w aHat)
    (hw : ∀ (aHat : TqMatrix mldsa87.k mldsa87.l) v, w aHat ≤ 𝔼 c,
      (memberWeight (concreteWithSampleInBall mldsa87 G) βmin
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 (v, c) : ENNReal).toReal) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, ringRegGap (concreteWithSampleInBall mldsa87 G)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) aHat βmin ≤
      12 / 2 ^ 203 / (βmin : ENNReal).toReal *
        √(𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, (w aHat ^ 2)⁻¹) :=
  expect_ringRegGap_le_sqrt
    (SigningParams.of_isApproved (p := mldsa87) (Or.inr (Or.inr rfl))) _
    (fun aHat => keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) hβ0 hβt hw0 hw
    (by norm_num)
    (expect_sq_sum_expect_abs_realMass_sub_le_mldsa87 sk₀ hs1 hs2 hG)

/-- **The `μ`-free numerator at ML-DSA-87**: with `SampleInBall = G`
of challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box, summed
over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`) and averaged over the commitment
hash:
`∑_Â ∑_v 𝔼_c̃ |realMass v c̃ - ρ_z standinMass v c̃| ≤ |T_q^(k×ℓ)| · K |V| · 12 · 2^-203`. -/
theorem sum_expect_abs_realMass_sub_le_mldsa87 (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {G : CommitHashBytes mldsa87 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa87 G)) :
    ∑ aHat : TqMatrix mldsa87.k mldsa87.l, ∑ v : BucketVec mldsa87, 𝔼 c,
        |(realMass (concreteWithSampleInBall mldsa87 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction mldsa87 * standinMass (concreteWithSampleInBall mldsa87 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal| ≤
      Fintype.card (TqMatrix mldsa87.k mldsa87.l) *
        ((standinScale mldsa87).toReal * Fintype.card (BucketVec mldsa87) * (12 / 2 ^ 203)) := by
  rw [← Finset.expect_const (Finset.univ_nonempty (α := CommitHashBytes mldsa87))
    ((Fintype.card (TqMatrix mldsa87.k mldsa87.l) : ℝ) *
      ((standinScale mldsa87).toReal * Fintype.card (BucketVec mldsa87) * (12 / 2 ^ 203)))]
  calc _ = 𝔼 c : CommitHashBytes mldsa87, ∑ aHat : TqMatrix mldsa87.k mldsa87.l, ∑ v : BucketVec mldsa87,
        |(realMass (concreteWithSampleInBall mldsa87 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction mldsa87 * standinMass (concreteWithSampleInBall mldsa87 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal| := by
        rw [Finset.expect_sum_comm]
        refine Finset.sum_congr rfl fun aHat _ => ?_
        rw [Finset.expect_sum_comm]
    _ ≤ _ := Finset.expect_le_expect fun c _ =>
        (sum_abs_realMass_sub_le_mldsa87 sk₀ hs1 hs2 c hG).trans_eq (by ring)

/-- **The averaged regularity gap at ML-DSA-87.** For keys with `s₁, s₂` in the `η`-box, `t₀`
recomputed from the uniform matrix `Â`, and mean member weights at least `μ > 0`,
`𝔼_Â ringRegGap ≤ 12 · 2^-203 / (μ β_min)`. -/
theorem expect_ringRegGap_le_mldsa87 (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {βmin : ℚ≥0} (hβ0 : (βmin : ENNReal) ≠ 0) (hβt : (βmin : ENNReal) ≠ ⊤) {μ : ℝ} (hμ : 0 < μ)
    (hmw : ∀ (aHat : TqMatrix mldsa87.k mldsa87.l) v, μ ≤ 𝔼 c,
      (memberWeight (concretePrimitives mldsa87) βmin
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 (v, c) : ENNReal).toReal) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, ringRegGap (concretePrimitives mldsa87)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) aHat βmin ≤
      12 / 2 ^ 203 / (μ * (βmin : ENNReal).toReal) := by
  have hp := SigningParams.of_isApproved (p := mldsa87) (Or.inr (Or.inr rfl))
  set sk := fun aHat : TqMatrix mldsa87.k mldsa87.l =>
    keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))
  set K := (standinScale mldsa87).toReal
  set V : ℝ := ((Fintype.card (BucketVec mldsa87) : ℕ) : ℝ)
  set T : ℝ := ((Fintype.card (TqMatrix mldsa87.k mldsa87.l) : ℕ) : ℝ)
  set Cs : ℝ := ((Fintype.card (CommitHashBytes mldsa87) : ℕ) : ℝ)
  have hK : 0 < K := standinScale_pos hp
  have hV : 0 < V := Nat.cast_pos.mpr (Fintype.card_pos (α := BucketVec mldsa87))
  have hT : 0 < T := Nat.cast_pos.mpr (Fintype.card_pos (α := TqMatrix mldsa87.k mldsa87.l))
  have hCs : 0 < Cs := Nat.cast_pos.mpr (Fintype.card_pos (α := CommitHashBytes mldsa87))
  have hβ : 0 < (βmin : ENNReal).toReal := ENNReal.toReal_pos hβ0 hβt
  set D := μ * ((standinScale mldsa87 * βmin).toReal * V)
  have hD : 0 < D := by simp only [D]; rw [ENNReal.toReal_mul]; positivity
  set E : TqMatrix mldsa87.k mldsa87.l → BucketVec mldsa87 → CommitHashBytes mldsa87 → ℝ :=
    fun aHat v c => |(realMass (concretePrimitives mldsa87) (sk aHat) aHat v c).toReal -
      (zAcceptFraction mldsa87 * standinMass (concretePrimitives mldsa87) (sk aHat) v c).toReal|
  have hstep : ∀ aHat, ringRegGap (concretePrimitives mldsa87) (sk aHat) aHat βmin ≤
      (∑ v, 𝔼 c, E aHat v c) / D := fun aHat =>
    ringRegGap_le hp _ (sk aHat) aHat hβ0 hβt hμ (hmw aHat)
  have hsum : ∑ aHat, ∑ v, 𝔼 c, E aHat v c ≤ T * (K * V * (12 / 2 ^ 203)) := by
    have h := sum_expect_abs_realMass_sub_le_mldsa87 sk₀ hs1 hs2
      (G := (concretePrimitives mldsa87).sampleInBall)
      (by rw [concreteWithSampleInBall_concrete]; exact sampleInBallShape_concrete mldsa87)
    rw [concreteWithSampleInBall_concrete] at h
    exact h
  calc 𝔼 aHat, ringRegGap (concretePrimitives mldsa87) (sk aHat) aHat βmin
      ≤ 𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, (∑ v, 𝔼 c, E aHat v c) / D :=
        Finset.expect_le_expect fun aHat _ => hstep aHat
    _ = (∑ aHat, ∑ v, 𝔼 c, E aHat v c) / T / D := by
        rw [Finset.expect_eq_sum_div_card, ← Finset.sum_div, Finset.card_univ]
        ring
    _ ≤ T * (K * V * (12 / 2 ^ 203)) / T / D := by gcongr
    _ = 12 / 2 ^ 203 / (μ * (βmin : ENNReal).toReal) := by
        simp only [D]
        rw [ENNReal.toReal_mul]
        field_simp
        exact div_self hK.ne'

end GordieHowe.MLDSA.Regularity
