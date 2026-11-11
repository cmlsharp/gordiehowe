-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.Instances
public import GordieHowe.Applications.MLDSA.Regularity.EnvelopeFive

@[expose] public section

/-!
# The regularity bound at ML-DSA-65 and ML-DSA-87 with small supports up to five

The instances of `Instances.lean` with the small-support bounds `cellSupportDelta` up to five
roots (cell size at least `523383`, Hadamard form of Lemma 2) and the envelopes
`envelope_five_mldsa65` (`2^-296`) and `envelope_five_mldsa87` (`2^-488`): the relative column
error is at most `11 · 2^-148` at ML-DSA-65 and `12 · 2^-244` at ML-DSA-87, and
`𝔼_Â signerRegGap ≤ 11 · 2^-148 / (μ β_min)`, resp. `12 · 2^-244 / (μ β_min)`. The `ℓ²` forms
(`sum_sq_sum_abs_realMass_sub_le_mldsa65_five`, `expect_sq_sum_expect_abs_realMass_sub_le_mldsa65_five`
and their ML-DSA-87 versions) give `𝔼_Â signerRegGap ≤ R / β_min · √(𝔼_Â (w Â)⁻²)` for every positive
lower bound `w Â` on the mean member weights (`expect_signerRegGap_le_sqrt_mldsa65_five`,
`expect_signerRegGap_le_sqrt_mldsa87_five`).
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA
open LatticeCrypto TransformOps

section Generic

variable {p : Params} [NeZero (bucketCount p)] [nttOps : NTTRingOps] {M : ℕ} [NeZero M]
  {G : CommitHashBytes p → ChallengePoly}

open Classical in
/-- **The averaged second moment of the signer's cells**, closed by the second-moment bound with
the small supports up to five of the spectral recursion: for `L ≥ 523383` it is at most
`∑_t C(256, t) supportTerm t` with `G = 2(γ₁ - β) - 1`, `m = bucketCount`, `T₂ = q² / (m L²)`. -/
theorem averagedSecondMoment_signerCells_le_five [Nonempty (CoeffIndex p)] (hp : SigningParams p)
    (sk₀ : SecretKey p) (cTilde : CommitHashBytes p)
    (ha : ∀ x, |cs2Shift (concreteWithSampleInBall p G) sk₀ cTilde x| ≤ p.beta)
    (hs1 : polyVecNorm ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1) ≤ p.beta)
    (t : ZMod M) (τ : Fin p.k → Rq) {S₁ : ℝ} (hS₁ : 1 ≤ S₁)
    (hfS : ∑ a : Coeff, hintKernel ((modulus : ℝ) / cellSize p) a ≤ S₁)
    (hL₀ : 523383 ≤ cellSize p) :
    averagedSecondMoment maskSlotEquiv
        (zBox p ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1)) slotRoot
        (cellKernels (fun ic r => signerCells G sk₀ cTilde t τ ic r) (cellSize p))
        (keySlot (fun b => sk₀.s1.get b)) 0 ≤
      ∑ t ∈ range (ringDegree + 1), (ringDegree.choose t : ℝ) *
        (if t = 0 then 0 else supportTerm ringDegree p.k p.l (2 * (p.gamma1 - p.beta) - 1) 5
          cellSupportDelta S₁
          ((modulus : ℝ) ^ 2 / (Fintype.card (Fin (bucketCount p)) * cellSize p ^ 2)) t) := by
  have hβ := hp.beta_lt_gamma1
  have hL := cellSize_pos hp
  have hC : (modulus : ℝ) / cellSize p ≤ 8380417 / 523383 := by
    rw [show (modulus : ℝ) = 8380417 by norm_num [modulus]]
    gcongr
  have hδ : SmallSupportBounds slotRoot (hintKernel ((modulus : ℝ) / cellSize p)) 5
      cellSupportDelta :=
    smallSupportBounds_five_of_isKernelBound slotRoot_injective slotRoot_pow
      (isKernelBound_hintKernel hp) hC
  exact averagedSecondMoment_le maskSlotEquiv _ (by omega) (card_zBox hp hs1) slotRoot_injective
    slotRoot_ne_zero (kernelBounds_signerCells hp sk₀ cTilde ha t τ hS₁ hfS) hδ _ 0

end Generic

attribute [local instance] concreteNTTRingOps

theorem cellSupportDelta_le :
    (∀ t, 0 ≤ cellSupportDelta t) ∧ cellSupportDelta 1 ≤ 1 / (2 ^ 256) ^ 2 ∧
      cellSupportDelta 2 ≤ 1 / (2 ^ 179) ^ 2 ∧ cellSupportDelta 3 ≤ 1 / 2 ^ 214 ∧
      cellSupportDelta 4 ≤ 1 / 2 ^ 99 ∧ cellSupportDelta 5 ≤ 1 / 2 ^ 7 := by
  refine ⟨fun t => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold cellSupportDelta; split_ifs <;> positivity
  all_goals simp [cellSupportDelta]

open Classical in
/-- **The averaged second moment at ML-DSA-65**: at most `2^-296`. -/
theorem averagedSecondMoment_signerCells_le_mldsa65_five
    (sk₀ : SecretKey mldsa65) (cTilde : CommitHashBytes mldsa65)
    {G : CommitHashBytes mldsa65 → ChallengePoly}
    (ha : ∀ x, |cs2Shift (concreteWithSampleInBall mldsa65 G) sk₀ cTilde x| ≤ mldsa65.beta)
    (hs1 : polyVecNorm ((concreteWithSampleInBall mldsa65 G).sampleInBall cTilde • sk₀.s1) ≤ mldsa65.beta)
    (t : ZMod 1537) (τ : Fin mldsa65.k → Rq) :
    averagedSecondMoment maskSlotEquiv
        (zBox mldsa65 ((concreteWithSampleInBall mldsa65 G).sampleInBall cTilde • sk₀.s1)) slotRoot
        (cellKernels (fun ic r => signerCells G sk₀ cTilde t τ ic r) (cellSize mldsa65))
        (keySlot (fun b => sk₀.s1.get b)) 0 ≤ 1 / 2 ^ 296 := by
  have hp := SigningParams.of_isApproved (p := mldsa65) (Or.inr (Or.inl rfl))
  refine (averagedSecondMoment_signerCells_le_five hp sk₀ cTilde ha hs1
    t τ (by norm_num) sum_hintKernel_le_mldsa65 cellSize_mldsa65.ge).trans ?_
  obtain ⟨hk, hl, hg1, hg2, hb, -⟩ := mldsa65_vals
  obtain ⟨hδ0, hδ1, hδ2, hδ3, hδ4, hδ5⟩ := cellSupportDelta_le
  have hG : 2 * (mldsa65.gamma1 - mldsa65.beta) - 1 = 1048183 := by rw [hg1, hb]
  have hT : (modulus : ℝ) ^ 2 / (Fintype.card (Fin (bucketCount mldsa65)) * cellSize mldsa65 ^ 2) =
      8380417 ^ 2 / (16 * 523383 ^ 2) := by
    rw [Fintype.card_fin, bucketCount_mldsa65, cellSize_mldsa65,
      show ((modulus : ℕ) : ℝ) = 8380417 by norm_num [modulus]]
    norm_num
  rw [hk, hl, hG, hT, show ringDegree = 256 from rfl]
  exact envelope_five_mldsa65 hδ0 hδ1 hδ2 hδ3 hδ4 hδ5 (by norm_num) le_rfl

/-- **Regularity at ML-DSA-65, `ℓ²` form.** At the concrete primitives with `SampleInBall = G` of
challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box and every
commitment hash `c̃`, over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â (∑_v |realMass v c̃ - ρ_z standinMass v c̃|)² ≤ (K |V| · 11 · 2^-148)²`. -/
theorem sum_sq_sum_abs_realMass_sub_le_mldsa65_five (sk₀ : SecretKey mldsa65)
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
          (11 / 2 ^ 148)) ^ 2 := by
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
      averagedSecondMoment_signerCells_le_mldsa65_five sk₀ cTilde ha hs1' t τ
  refine h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ 2) (Nat.cast_nonneg _))
  · exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)) (mul_nonneg (pow_nonneg (div_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (cellSize_pos hp).le) (Nat.cast_nonneg _)) _)
        (Real.sqrt_nonneg _))
  have hΛ : ∑ t : ZMod 1537, ‖ZMod.countCoeff 1537 mldsa65.omega t‖ ≤ 11 := by
    rw [mldsa65_vals.2.2.2.2.2]; exact sum_norm_countCoeff_le_mldsa65
  have hsq : √(1 / 2 ^ 296 : ℝ) = 1 / 2 ^ 148 := by
    rw [show (1 / 2 ^ 296 : ℝ) = (1 / 2 ^ 148) ^ 2 by
      rw [div_pow, one_pow, ← pow_mul], Real.sqrt_sq (by positivity)]
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
  have hX : 0 ≤ (L / qq) ^ n * 16 ^ n * (1 / 2 ^ 148 : ℝ) := by positivity
  calc ρ * Λ * ((L / qq) ^ n * 16 ^ n * (1 / 2 ^ 148))
      ≤ ρ * 11 * ((L / qq) ^ n * 16 ^ n * (1 / 2 ^ 148)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛ hρ) hX
    _ = _ := by ring

/-- **Regularity at ML-DSA-65.** At the concrete primitives with `SampleInBall = G` of
challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box and every
commitment hash `c̃`, averaged over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â ∑_v |realMass v c̃ - ρ_z standinMass v c̃| ≤ K |V| · 11 · 2^-148`. -/
theorem sum_abs_realMass_sub_le_mldsa65_five (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    (cTilde : CommitHashBytes mldsa65) {G : CommitHashBytes mldsa65 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa65 G)) :
    ∑ aHat : TqMatrix mldsa65.k mldsa65.l, ∑ v : BucketVec mldsa65,
        |(realMass (concreteWithSampleInBall mldsa65 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v cTilde).toReal -
          (zAcceptFraction mldsa65 * standinMass (concreteWithSampleInBall mldsa65 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal| ≤
      Fintype.card (TqMatrix mldsa65.k mldsa65.l) *
        ((standinScale mldsa65).toReal * Fintype.card (BucketVec mldsa65)) * (11 / 2 ^ 148) := by
  have h := sum_sq_sum_abs_realMass_sub_le_mldsa65_five sk₀ hs1 hs2 cTilde hG
  rw [← Finset.card_univ (α := TqMatrix mldsa65.k mldsa65.l)] at h
  have h1 := Finset.sum_le_card_mul_of_sum_sq_le
    (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)) (by norm_num)) h
  rw [Finset.card_univ] at h1
  exact h1.trans_eq (by ring)

/-- **The mean square column error at ML-DSA-65**: with `SampleInBall = G` of challenge shape and
the concrete NTT, for every key with `s₁, s₂` in the `η`-box, averaged over the matrix `Â` (with
`t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â (∑_v 𝔼_c̃ |realMass v c̃ - ρ_z standinMass v c̃|)² ≤ (K |V| · 11 · 2^-148)²`. -/
theorem expect_sq_sum_expect_abs_realMass_sub_le_mldsa65_five (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {G : CommitHashBytes mldsa65 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa65 G)) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, (∑ v : BucketVec mldsa65, 𝔼 c,
        |(realMass (concreteWithSampleInBall mldsa65 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction mldsa65 * standinMass (concreteWithSampleInBall mldsa65 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal|) ^ 2 ≤
      ((standinScale mldsa65).toReal * Fintype.card (BucketVec mldsa65) * (11 / 2 ^ 148)) ^ 2 :=
  Finset.expect_sq_sum_expect_le _ fun c =>
    sum_sq_sum_abs_realMass_sub_le_mldsa65_five sk₀ hs1 hs2 c hG

/-- **The mean regularity gap at ML-DSA-65 by Cauchy–Schwarz over the matrix.** With
`SampleInBall = G` of challenge shape and the concrete NTT, for keys with `s₁, s₂` in the
`η`-box, `t₀` recomputed from the uniform matrix `Â`, and any positive lower bound `w Â` on the
mean member weights of every bucket vector,
`𝔼_Â signerRegGap ≤ 11 · 2^-148 / β_min · √(𝔼_Â (w Â)⁻²)`. -/
theorem expect_signerRegGap_le_sqrt_mldsa65_five (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {G : CommitHashBytes mldsa65 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa65 G))
    {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    {w : TqMatrix mldsa65.k mldsa65.l → ℝ}
    (hw0 : ∀ aHat, 0 < w aHat)
    (hw : ∀ (aHat : TqMatrix mldsa65.k mldsa65.l) v, w aHat ≤ 𝔼 c,
      (flatWeight (concreteWithSampleInBall mldsa65 G) (Cutoff.const βmin)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 (v, c) : ℝ≥0∞).toReal) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, signerRegGap (concreteWithSampleInBall mldsa65 G)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) aHat (Cutoff.const βmin) ≤
      11 / 2 ^ 148 / (βmin : ℝ≥0∞).toReal *
        √(𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, (w aHat ^ 2)⁻¹) :=
  expect_signerRegGap_le_sqrt
    (SigningParams.of_isApproved (p := mldsa65) (Or.inr (Or.inl rfl))) _
    (fun aHat => keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) hβ0 hβt hw0 hw
    (by norm_num)
    (expect_sq_sum_expect_abs_realMass_sub_le_mldsa65_five sk₀ hs1 hs2 hG)

/-- **The `μ`-free numerator at ML-DSA-65 (supports up to five)**: with `SampleInBall = G`
of challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box, summed
over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`) and averaged over the commitment
hash:
`∑_Â ∑_v 𝔼_c̃ |realMass v c̃ - ρ_z standinMass v c̃| ≤ |T_q^(k×ℓ)| · K |V| · 11 · 2^-148`. -/
theorem sum_expect_abs_realMass_sub_le_mldsa65_five (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {G : CommitHashBytes mldsa65 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa65 G)) :
    ∑ aHat : TqMatrix mldsa65.k mldsa65.l, ∑ v : BucketVec mldsa65, 𝔼 c,
        |(realMass (concreteWithSampleInBall mldsa65 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction mldsa65 * standinMass (concreteWithSampleInBall mldsa65 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal| ≤
      Fintype.card (TqMatrix mldsa65.k mldsa65.l) *
        ((standinScale mldsa65).toReal * Fintype.card (BucketVec mldsa65) * (11 / 2 ^ 148)) := by
  rw [← Finset.expect_const (Finset.univ_nonempty (α := CommitHashBytes mldsa65))
    ((Fintype.card (TqMatrix mldsa65.k mldsa65.l) : ℝ) *
      ((standinScale mldsa65).toReal * Fintype.card (BucketVec mldsa65) * (11 / 2 ^ 148)))]
  calc _ = 𝔼 c : CommitHashBytes mldsa65, ∑ aHat : TqMatrix mldsa65.k mldsa65.l, ∑ v : BucketVec mldsa65,
        |(realMass (concreteWithSampleInBall mldsa65 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction mldsa65 * standinMass (concreteWithSampleInBall mldsa65 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal| := by
        rw [Finset.expect_sum_comm]
        refine Finset.sum_congr rfl fun aHat _ => ?_
        rw [Finset.expect_sum_comm]
    _ ≤ _ := Finset.expect_le_expect fun c _ =>
        (sum_abs_realMass_sub_le_mldsa65_five sk₀ hs1 hs2 c hG).trans_eq (by ring)

/-- **The averaged regularity gap at ML-DSA-65.** For keys with `s₁, s₂` in the `η`-box, `t₀`
recomputed from the uniform matrix `Â`, and mean member weights at least `μ > 0`,
`𝔼_Â signerRegGap ≤ 11 · 2^-148 / (μ β_min)`. -/
theorem expect_signerRegGap_le_mldsa65_five (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {μ : ℝ} (hμ : 0 < μ)
    (hmw : ∀ (aHat : TqMatrix mldsa65.k mldsa65.l) v, μ ≤ 𝔼 c,
      (flatWeight (concretePrimitives mldsa65) (Cutoff.const βmin)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 (v, c) : ℝ≥0∞).toReal) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, signerRegGap (concretePrimitives mldsa65)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) aHat (Cutoff.const βmin) ≤
      11 / 2 ^ 148 / (μ * (βmin : ℝ≥0∞).toReal) := by
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
  have hβ : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  set D := μ * ((standinScale mldsa65 * βmin).toReal * V)
  have hD : 0 < D := by simp only [D]; rw [ENNReal.toReal_mul]; positivity
  set E : TqMatrix mldsa65.k mldsa65.l → BucketVec mldsa65 → CommitHashBytes mldsa65 → ℝ :=
    fun aHat v c => |(realMass (concretePrimitives mldsa65) (sk aHat) aHat v c).toReal -
      (zAcceptFraction mldsa65 * standinMass (concretePrimitives mldsa65) (sk aHat) v c).toReal|
  have hstep : ∀ aHat, signerRegGap (concretePrimitives mldsa65) (sk aHat) aHat (Cutoff.const βmin)
      ≤
      (∑ v, 𝔼 c, E aHat v c) / D := fun aHat =>
    signerRegGap_le_const hp _ (sk aHat) aHat hβ0 hβt hμ (hmw aHat)
  have hsum : ∑ aHat, ∑ v, 𝔼 c, E aHat v c ≤ T * (K * V * (11 / 2 ^ 148)) := by
    have h := sum_expect_abs_realMass_sub_le_mldsa65_five sk₀ hs1 hs2
      (G := (concretePrimitives mldsa65).sampleInBall)
      (by rw [concreteWithSampleInBall_concrete]; exact sampleInBallShape_concrete mldsa65)
    rw [concreteWithSampleInBall_concrete] at h
    exact h
  calc 𝔼 aHat, signerRegGap (concretePrimitives mldsa65) (sk aHat) aHat (Cutoff.const βmin)
      ≤ 𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, (∑ v, 𝔼 c, E aHat v c) / D :=
        Finset.expect_le_expect fun aHat _ => hstep aHat
    _ = (∑ aHat, ∑ v, 𝔼 c, E aHat v c) / T / D := by
        rw [Finset.expect_eq_sum_div_card, ← Finset.sum_div, Finset.card_univ]
        ring
    _ ≤ T * (K * V * (11 / 2 ^ 148)) / T / D := by gcongr
    _ = 11 / 2 ^ 148 / (μ * (βmin : ℝ≥0∞).toReal) := by
        simp only [D]
        rw [ENNReal.toReal_mul]
        field_simp
        exact div_self hK.ne'

open Classical in
/-- **The averaged second moment at ML-DSA-87**: at most `2^-488`. -/
theorem averagedSecondMoment_signerCells_le_mldsa87_five
    (sk₀ : SecretKey mldsa87) (cTilde : CommitHashBytes mldsa87)
    {G : CommitHashBytes mldsa87 → ChallengePoly}
    (ha : ∀ x, |cs2Shift (concreteWithSampleInBall mldsa87 G) sk₀ cTilde x| ≤ mldsa87.beta)
    (hs1 : polyVecNorm ((concreteWithSampleInBall mldsa87 G).sampleInBall cTilde • sk₀.s1) ≤ mldsa87.beta)
    (t : ZMod 2049) (τ : Fin mldsa87.k → Rq) :
    averagedSecondMoment maskSlotEquiv
        (zBox mldsa87 ((concreteWithSampleInBall mldsa87 G).sampleInBall cTilde • sk₀.s1)) slotRoot
        (cellKernels (fun ic r => signerCells G sk₀ cTilde t τ ic r) (cellSize mldsa87))
        (keySlot (fun b => sk₀.s1.get b)) 0 ≤ 1 / 2 ^ 488 := by
  have hp := SigningParams.of_isApproved (p := mldsa87) (Or.inr (Or.inr rfl))
  refine (averagedSecondMoment_signerCells_le_five hp sk₀ cTilde ha hs1
    t τ (by norm_num) sum_hintKernel_le_mldsa87 (by rw [cellSize_mldsa87]; norm_num)).trans ?_
  obtain ⟨hk, hl, hg1, hg2, hb, -⟩ := mldsa87_vals
  obtain ⟨hδ0, hδ1, hδ2, hδ3, hδ4, hδ5⟩ := cellSupportDelta_le
  have hG : 2 * (mldsa87.gamma1 - mldsa87.beta) - 1 = 1048335 := by rw [hg1, hb]
  have hT : (modulus : ℝ) ^ 2 / (Fintype.card (Fin (bucketCount mldsa87)) * cellSize mldsa87 ^ 2) =
      8380417 ^ 2 / (16 * 523535 ^ 2) := by
    rw [Fintype.card_fin, bucketCount_mldsa87, cellSize_mldsa87,
      show ((modulus : ℕ) : ℝ) = 8380417 by norm_num [modulus]]
    norm_num
  rw [hk, hl, hG, hT, show ringDegree = 256 from rfl]
  exact envelope_five_mldsa87 hδ0 hδ1 hδ2 hδ3 hδ4 hδ5 (by norm_num) le_rfl

/-- **Regularity at ML-DSA-87, `ℓ²` form.** At the concrete primitives with `SampleInBall = G` of
challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box and every
commitment hash `c̃`, over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â (∑_v |realMass v c̃ - ρ_z standinMass v c̃|)² ≤ (K |V| · 12 · 2^-244)²`. -/
theorem sum_sq_sum_abs_realMass_sub_le_mldsa87_five (sk₀ : SecretKey mldsa87)
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
          (12 / 2 ^ 244)) ^ 2 := by
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
      averagedSecondMoment_signerCells_le_mldsa87_five sk₀ cTilde ha hs1' t τ
  refine h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ 2) (Nat.cast_nonneg _))
  · exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)) (mul_nonneg (pow_nonneg (div_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (cellSize_pos hp).le) (Nat.cast_nonneg _)) _)
        (Real.sqrt_nonneg _))
  have hΛ : ∑ t : ZMod 2049, ‖ZMod.countCoeff 2049 mldsa87.omega t‖ ≤ 12 := by
    rw [mldsa87_vals.2.2.2.2.2]; exact sum_norm_countCoeff_le_mldsa87
  have hsq : √(1 / 2 ^ 488 : ℝ) = 1 / 2 ^ 244 := by
    rw [show (1 / 2 ^ 488 : ℝ) = (1 / 2 ^ 244) ^ 2 by rw [div_pow, one_pow, ← pow_mul],
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
  have hX : 0 ≤ (L / qq) ^ n * 16 ^ n * (1 / 2 ^ 244 : ℝ) := by positivity
  calc ρ * Λ * ((L / qq) ^ n * 16 ^ n * (1 / 2 ^ 244))
      ≤ ρ * 12 * ((L / qq) ^ n * 16 ^ n * (1 / 2 ^ 244)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛ hρ) hX
    _ = _ := by ring

/-- **Regularity at ML-DSA-87.** At the concrete primitives with `SampleInBall = G` of
challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box and every
commitment hash `c̃`, averaged over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â ∑_v |realMass v c̃ - ρ_z standinMass v c̃| ≤ K |V| · 12 · 2^-244`. -/
theorem sum_abs_realMass_sub_le_mldsa87_five (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    (cTilde : CommitHashBytes mldsa87) {G : CommitHashBytes mldsa87 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa87 G)) :
    ∑ aHat : TqMatrix mldsa87.k mldsa87.l, ∑ v : BucketVec mldsa87,
        |(realMass (concreteWithSampleInBall mldsa87 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v cTilde).toReal -
          (zAcceptFraction mldsa87 * standinMass (concreteWithSampleInBall mldsa87 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal| ≤
      Fintype.card (TqMatrix mldsa87.k mldsa87.l) *
        ((standinScale mldsa87).toReal * Fintype.card (BucketVec mldsa87)) * (12 / 2 ^ 244) := by
  have h := sum_sq_sum_abs_realMass_sub_le_mldsa87_five sk₀ hs1 hs2 cTilde hG
  rw [← Finset.card_univ (α := TqMatrix mldsa87.k mldsa87.l)] at h
  have h1 := Finset.sum_le_card_mul_of_sum_sq_le
    (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)) (by norm_num)) h
  rw [Finset.card_univ] at h1
  exact h1.trans_eq (by ring)

/-- **The mean square column error at ML-DSA-87**: with `SampleInBall = G` of challenge shape and
the concrete NTT, for every key with `s₁, s₂` in the `η`-box, averaged over the matrix `Â` (with
`t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â (∑_v 𝔼_c̃ |realMass v c̃ - ρ_z standinMass v c̃|)² ≤ (K |V| · 12 · 2^-244)²`. -/
theorem expect_sq_sum_expect_abs_realMass_sub_le_mldsa87_five (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {G : CommitHashBytes mldsa87 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa87 G)) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, (∑ v : BucketVec mldsa87, 𝔼 c,
        |(realMass (concreteWithSampleInBall mldsa87 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction mldsa87 * standinMass (concreteWithSampleInBall mldsa87 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal|) ^ 2 ≤
      ((standinScale mldsa87).toReal * Fintype.card (BucketVec mldsa87) * (12 / 2 ^ 244)) ^ 2 :=
  Finset.expect_sq_sum_expect_le _ fun c =>
    sum_sq_sum_abs_realMass_sub_le_mldsa87_five sk₀ hs1 hs2 c hG

/-- **The mean regularity gap at ML-DSA-87 by Cauchy–Schwarz over the matrix.** With
`SampleInBall = G` of challenge shape and the concrete NTT, for keys with `s₁, s₂` in the
`η`-box, `t₀` recomputed from the uniform matrix `Â`, and any positive lower bound `w Â` on the
mean member weights of every bucket vector,
`𝔼_Â signerRegGap ≤ 12 · 2^-244 / β_min · √(𝔼_Â (w Â)⁻²)`. -/
theorem expect_signerRegGap_le_sqrt_mldsa87_five (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {G : CommitHashBytes mldsa87 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa87 G))
    {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    {w : TqMatrix mldsa87.k mldsa87.l → ℝ}
    (hw0 : ∀ aHat, 0 < w aHat)
    (hw : ∀ (aHat : TqMatrix mldsa87.k mldsa87.l) v, w aHat ≤ 𝔼 c,
      (flatWeight (concreteWithSampleInBall mldsa87 G) (Cutoff.const βmin)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 (v, c) : ℝ≥0∞).toReal) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, signerRegGap (concreteWithSampleInBall mldsa87 G)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) aHat (Cutoff.const βmin) ≤
      12 / 2 ^ 244 / (βmin : ℝ≥0∞).toReal *
        √(𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, (w aHat ^ 2)⁻¹) :=
  expect_signerRegGap_le_sqrt
    (SigningParams.of_isApproved (p := mldsa87) (Or.inr (Or.inr rfl))) _
    (fun aHat => keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) hβ0 hβt hw0 hw
    (by norm_num)
    (expect_sq_sum_expect_abs_realMass_sub_le_mldsa87_five sk₀ hs1 hs2 hG)

/-- **The `μ`-free numerator at ML-DSA-87 (supports up to five)**: with `SampleInBall = G`
of challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box, summed
over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`) and averaged over the commitment
hash:
`∑_Â ∑_v 𝔼_c̃ |realMass v c̃ - ρ_z standinMass v c̃| ≤ |T_q^(k×ℓ)| · K |V| · 12 · 2^-244`. -/
theorem sum_expect_abs_realMass_sub_le_mldsa87_five (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {G : CommitHashBytes mldsa87 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall mldsa87 G)) :
    ∑ aHat : TqMatrix mldsa87.k mldsa87.l, ∑ v : BucketVec mldsa87, 𝔼 c,
        |(realMass (concreteWithSampleInBall mldsa87 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction mldsa87 * standinMass (concreteWithSampleInBall mldsa87 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal| ≤
      Fintype.card (TqMatrix mldsa87.k mldsa87.l) *
        ((standinScale mldsa87).toReal * Fintype.card (BucketVec mldsa87) * (12 / 2 ^ 244)) := by
  rw [← Finset.expect_const (Finset.univ_nonempty (α := CommitHashBytes mldsa87))
    ((Fintype.card (TqMatrix mldsa87.k mldsa87.l) : ℝ) *
      ((standinScale mldsa87).toReal * Fintype.card (BucketVec mldsa87) * (12 / 2 ^ 244)))]
  calc _ = 𝔼 c : CommitHashBytes mldsa87, ∑ aHat : TqMatrix mldsa87.k mldsa87.l, ∑ v : BucketVec mldsa87,
        |(realMass (concreteWithSampleInBall mldsa87 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction mldsa87 * standinMass (concreteWithSampleInBall mldsa87 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal| := by
        rw [Finset.expect_sum_comm]
        refine Finset.sum_congr rfl fun aHat _ => ?_
        rw [Finset.expect_sum_comm]
    _ ≤ _ := Finset.expect_le_expect fun c _ =>
        (sum_abs_realMass_sub_le_mldsa87_five sk₀ hs1 hs2 c hG).trans_eq (by ring)

/-- **The averaged regularity gap at ML-DSA-87.** For keys with `s₁, s₂` in the `η`-box, `t₀`
recomputed from the uniform matrix `Â`, and mean member weights at least `μ > 0`,
`𝔼_Â signerRegGap ≤ 12 · 2^-244 / (μ β_min)`. -/
theorem expect_signerRegGap_le_mldsa87_five (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {μ : ℝ} (hμ : 0 < μ)
    (hmw : ∀ (aHat : TqMatrix mldsa87.k mldsa87.l) v, μ ≤ 𝔼 c,
      (flatWeight (concretePrimitives mldsa87) (Cutoff.const βmin)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 (v, c) : ℝ≥0∞).toReal) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, signerRegGap (concretePrimitives mldsa87)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) aHat (Cutoff.const βmin) ≤
      12 / 2 ^ 244 / (μ * (βmin : ℝ≥0∞).toReal) := by
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
  have hβ : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  set D := μ * ((standinScale mldsa87 * βmin).toReal * V)
  have hD : 0 < D := by simp only [D]; rw [ENNReal.toReal_mul]; positivity
  set E : TqMatrix mldsa87.k mldsa87.l → BucketVec mldsa87 → CommitHashBytes mldsa87 → ℝ :=
    fun aHat v c => |(realMass (concretePrimitives mldsa87) (sk aHat) aHat v c).toReal -
      (zAcceptFraction mldsa87 * standinMass (concretePrimitives mldsa87) (sk aHat) v c).toReal|
  have hstep : ∀ aHat, signerRegGap (concretePrimitives mldsa87) (sk aHat) aHat (Cutoff.const βmin)
      ≤
      (∑ v, 𝔼 c, E aHat v c) / D := fun aHat =>
    signerRegGap_le_const hp _ (sk aHat) aHat hβ0 hβt hμ (hmw aHat)
  have hsum : ∑ aHat, ∑ v, 𝔼 c, E aHat v c ≤ T * (K * V * (12 / 2 ^ 244)) := by
    have h := sum_expect_abs_realMass_sub_le_mldsa87_five sk₀ hs1 hs2
      (G := (concretePrimitives mldsa87).sampleInBall)
      (by rw [concreteWithSampleInBall_concrete]; exact sampleInBallShape_concrete mldsa87)
    rw [concreteWithSampleInBall_concrete] at h
    exact h
  calc 𝔼 aHat, signerRegGap (concretePrimitives mldsa87) (sk aHat) aHat (Cutoff.const βmin)
      ≤ 𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, (∑ v, 𝔼 c, E aHat v c) / D :=
        Finset.expect_le_expect fun aHat _ => hstep aHat
    _ = (∑ aHat, ∑ v, 𝔼 c, E aHat v c) / T / D := by
        rw [Finset.expect_eq_sum_div_card, ← Finset.sum_div, Finset.card_univ]
        ring
    _ ≤ T * (K * V * (12 / 2 ^ 244)) / T / D := by gcongr
    _ = 12 / 2 ^ 244 / (μ * (βmin : ℝ≥0∞).toReal) := by
        simp only [D]
        rw [ENNReal.toReal_mul]
        field_simp
        exact div_self hK.ne'

end GordieHowe.MLDSA.Regularity
