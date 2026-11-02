-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.InstancesFive
public import GordieHowe.Applications.MLDSA.Regularity.SlotBoxCount

@[expose] public section

/-!
# The regularity bound at ML-DSA-44 with the sharp slot count

The ML-DSA-44 instance of `Instances.lean` with the slot probabilities of the fixed-mode route
counted against the field size `q` instead of the box side `G` at `t = 5`
(`averagedSecondMoment_le_box`, `envelope_box_mldsa44`): the averaged second moment is at most
`2^-154` (`averagedSecondMoment_signerCells_le_mldsa44_box`), and the relative column error is at
most `11 · 2^-77`.

* The z-check box of every coefficient is an interval of `G = 2(γ₁ - β) - 1` residues
  (`isResidueInterval_zCheckCoeffSet`), so its character sums satisfy
  `‖∑_{x ∈ S} ψ (a x)‖ ≤ G · min(1, q / (2G|a|))` (`norm_sum_stdAddChar_le_hintKernel`), a
  kernel bound with `C = q / (2G) ≤ q / 523383` whose small-support bounds up to five roots are
  `cellSupportDelta` (`smallSupportBounds_zBox`).
* `sum_sq_sum_abs_realMass_sub_le_mldsa44_box`, `expect_sq_sum_expect_abs_realMass_sub_le_mldsa44_box`:
  the `ℓ²` forms, `𝔼_Â (∑_v |realMass v c̃ - ρ_z standinMass v c̃|)² ≤ (K |V| · 11 · 2^-77)²`;
  `sum_abs_realMass_sub_le_mldsa44_box`: the `ℓ¹` form; and
  `expect_ringRegGap_le_sqrt_mldsa44_box`: `𝔼_Â ringRegGap ≤ 11 · 2^-77 / β_min · √(𝔼_Â (w Â)⁻²)`.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA
open LatticeCrypto TransformOps

section Box

/-- **The z-check set is an interval** of `2(γ₁ - β) - 1` residues, `y = 1 - (γ₁ - β) - v + u`
for `u < 2(γ₁ - β) - 1`, when `|v| ≤ β < γ₁` and `2(γ₁ + β) < q`. -/
theorem isResidueInterval_zCheckCoeffSet {γ₁ β : ℕ} (hq : 2 * (γ₁ + β) < modulus) (hβ : β < γ₁)
    {v : ℤ} (hv : |v| ≤ β) : IsResidueInterval (zCheckCoeffSet γ₁ β v) := by
  have hv' := abs_le.mp hv
  have hcr : ∀ z : ℤ, |z| ≤ γ₁ + β → LatticeCrypto.centeredRepr ((z : Coeff)) = z := fun z hz =>
    LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le z (b := γ₁ + β)
      (by rw [abs_le] at hz; omega) hq
  set len := 2 * (γ₁ - β) - 1
  have hlen : len ≤ modulus := by omega
  set c : Coeff := ((1 - ((γ₁ : ℤ) - β) - v : ℤ) : Coeff)
  refine ⟨c, len, hlen, ?_⟩
  have hinj : Set.InjOn (fun u : ℕ => c + (u : Coeff)) (range len) := by
    intro u hu w hw h
    have h' : (u : Coeff) = w := add_left_cancel h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hu)
      hlen), Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hw) hlen)] at h'
    exact h'
  have hsub : (range len).image (fun u : ℕ => c + (u : Coeff)) ⊆ zCheckCoeffSet γ₁ β v := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    have hu' := Finset.mem_range.mp hu
    have hy1 : c + (u : Coeff) = (((1 - ((γ₁ : ℤ) - β) - v + u : ℤ)) : Coeff) := by
      simp only [c]
      push_cast
      ring
    have hy2 : c + (u : Coeff) + (v : Coeff) = (((1 - ((γ₁ : ℤ) - β) + u : ℤ)) : Coeff) := by
      rw [hy1]
      push_cast
      ring
    simp only [zCheckCoeffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hy2, hy1, hcr _ (abs_le.mpr ⟨by omega, by omega⟩),
      hcr _ (abs_le.mpr ⟨by omega, by omega⟩), abs_lt]
    omega
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [box_shift_card hq hv, Finset.card_image_of_injOn hinj, Finset.card_range]

/-- **The character sums of an interval side**: for an interval `S` of `G ≥ 1` residues,
`‖∑_{x ∈ S} e(a x)‖ ≤ #S · hintKernel (N / (2G)) a`. -/
theorem norm_sum_stdAddChar_le_hintKernel {N : ℕ} [NeZero N] {S : Finset (ZMod N)}
    (hS : IsResidueInterval S) {G : ℕ} (hG : #S = G) (hG0 : 0 < G) (a : ZMod N) :
    ‖∑ x ∈ S, ZMod.stdAddChar (a * x)‖ ≤ #S * hintKernel ((N : ℝ) / (2 * G)) a := by
  have htriv : ‖∑ x ∈ S, ZMod.stdAddChar (a * x)‖ ≤ #S :=
    (norm_sum_le _ _).trans (le_of_eq (by simp [AddChar.norm_apply]))
  unfold hintKernel
  split_ifs with ha
  · rw [mul_one]
    exact htriv
  · have hpos : 0 < |(a.valMinAbs : ℝ)| :=
      abs_pos.mpr (by exact_mod_cast (ZMod.valMinAbs_eq_zero a).not.mpr ha)
    have hint := norm_sum_interval_le hS (neg_ne_zero.mpr ha)
    have habs : |(((-a).valMinAbs : ℤ) : ℝ)| = |(a.valMinAbs : ℝ)| := by
      rw [← Int.cast_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.abs_eq_natAbs,
        ZMod.natAbs_valMinAbs_neg]
    rw [habs] at hint
    have heq : ∑ x ∈ S, ZMod.stdAddChar (-(x * -a)) = ∑ x ∈ S, ZMod.stdAddChar (a * x) :=
      Finset.sum_congr rfl fun x _ => by ring_nf
    rw [heq] at hint
    have hG' : (0 : ℝ) < G := by exact_mod_cast hG0
    rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg _), mul_one]
    refine le_min htriv (hint.trans (le_of_eq ?_))
    rw [hG]
    field_simp

/-- The interval kernel `hintKernel (q / (2G))` is a kernel bound with constant `q / (2G)`. -/
theorem isKernelBound_hintKernel_two_mul {G : ℕ} (hG0 : 0 < G) :
    IsKernelBound ((modulus : ℝ) / (2 * G))
      (hintKernel (N := modulus) ((modulus : ℝ) / (2 * G))) where
  nonneg := hintKernel_nonneg (by positivity)
  le_one := hintKernel_le_one _
  mul_abs_valMinAbs_le x hx := hintKernel_mul_abs_le hx

variable {p : Params} [NeZero (bucketCount p)] [nttOps : NTTRingOps] {M : ℕ} [NeZero M]
  {G : CommitHashBytes p → ChallengePoly}

omit [NeZero (bucketCount p)] nttOps in
/-- The small-support bounds up to five roots of the z-box kernel, for `2G ≥ 523383`. -/
theorem smallSupportBounds_zBox
    (h2G : 523383 ≤ 2 * (2 * (p.gamma1 - p.beta) - 1)) :
    SmallSupportBounds slotRoot (hintKernel (N := modulus)
      ((modulus : ℝ) / (2 * ((2 * (p.gamma1 - p.beta) - 1 : ℕ) : ℝ)))) 5 cellSupportDelta := by
  have hG0 : 0 < 2 * (p.gamma1 - p.beta) - 1 := by omega
  refine smallSupportBounds_five_of_isKernelBound slotRoot_injective slotRoot_pow
    (isKernelBound_hintKernel_two_mul hG0) ?_
  rw [show (modulus : ℝ) = 8380417 by norm_num [modulus]]
  have h : (523383 : ℝ) ≤ 2 * ((2 * (p.gamma1 - p.beta) - 1 : ℕ) : ℝ) := by exact_mod_cast h2G
  gcongr

open Classical in
/-- **The averaged second moment of the signer's cells with the sharp slot count**: under the
hypotheses of `averagedSecondMoment_signerCells_le_hybrid` and `2G ≥ 523383`, every support size
`t` takes the minimum of `boxSupportTerm t` (the sharp count at `t = 5`, box bounds
`cellSupportDelta`) and the hybrid term. -/
theorem averagedSecondMoment_signerCells_le_box [Nonempty (CoeffIndex p)]
    (hp : SigningParams p) (sk₀ : SecretKey p) (cTilde : CommitHashBytes p)
    (ha : ∀ x, |cs2Shift (concreteWithSampleInBall p G) sk₀ cTilde x| ≤ p.beta)
    (hs1 : polyVecNorm ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1) ≤ p.beta)
    (t : ZMod M) (τ : Fin p.k → Rq) {S₁ : ℝ} (hS₁ : 1 ≤ S₁)
    (hfS : ∑ a : Coeff, hintKernel ((modulus : ℝ) / cellSize p) a ≤ S₁)
    (hL₀ : 190307 ≤ cellSize p) (hℓ : 1 ≤ p.l)
    (h2G : 523383 ≤ 2 * (2 * (p.gamma1 - p.beta) - 1)) :
    averagedSecondMoment maskSlotEquiv
        (zBox p ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1)) slotRoot
        (cellKernels (fun ic r => signerCells G sk₀ cTilde t τ ic r) (cellSize p))
        (keySlot (fun b => sk₀.s1.get b)) 0 ≤
      ∑ t ∈ range (ringDegree + 1), (ringDegree.choose t : ℝ) *
        (if t = 0 then 0 else min (boxSupportTerm ringDegree p.k p.l
          (2 * (p.gamma1 - p.beta) - 1) modulus 4 5 smallSupportDelta cellSupportDelta S₁
          ((modulus : ℝ) ^ 2 / (Fintype.card (Fin (bucketCount p)) * cellSize p ^ 2)) t)
          (hybridFactor S₁ ((modulus : ℝ) / cellSize p) p.k (2 * (p.gamma1 - p.beta) - 1)
            p.l ^ t)) := by
  have hβ := hp.beta_lt_gamma1
  have hL := cellSize_pos hp
  have hC : (modulus : ℝ) / cellSize p ≤ 8380417 / 190307 := by
    rw [show (modulus : ℝ) = 8380417 by norm_num [modulus]]
    gcongr
  have hδ : SmallSupportBounds slotRoot (hintKernel ((modulus : ℝ) / cellSize p)) 4
      smallSupportDelta :=
    smallSupportBounds_of_isKernelBound slotRoot_injective slotRoot_pow
      (isKernelBound_hintKernel hp) hC
  have hq : (0 : ℝ) ≤ (modulus : ℝ) / cellSize p := by
    have : (0 : ℝ) < modulus := by norm_num [modulus]
    positivity
  have hG0 : 0 < 2 * (p.gamma1 - p.beta) - 1 := by omega
  have hψ : (ZMod.stdAddChar : AddChar Coeff ℂ) ≠ 0 := by
    have h := ZMod.isPrimitive_stdAddChar modulus (a := 1) one_ne_zero
    rwa [AddChar.mulShift_one] at h
  have hbox : ∀ i a, ‖∑ x ∈ zBox p ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1) i,
      ZMod.stdAddChar (a * x)‖ ≤
      #(zBox p ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1) i) *
        hintKernel (N := modulus)
          ((modulus : ℝ) / (2 * ((2 * (p.gamma1 - p.beta) - 1 : ℕ) : ℝ))) a := by
    intro i a
    refine norm_sum_stdAddChar_le_hintKernel ?_ (card_zBox hp hs1 i) hG0 a
    refine isResidueInterval_zCheckCoeffSet hp.gamma1_beta_lt hβ ?_
    have := GordieHowe.MLDSA44.natAbs_centeredRepr_le_polyVecNorm
      ((concreteWithSampleInBall p G).sampleInBall cTilde • sk₀.s1) i.1 i.2
    rw [abs_le]; omega
  have hE : ∀ (z : Fin p.l × Fin ringDegree → Coeff) (j : Fin ringDegree) (b : Fin p.l),
      maskSlotEquiv z j b = ∑ c, z (b, c) * slotRoot j ^ (c : ℕ) := by
    intro z j b
    rw [maskSlotEquiv, LinearEquiv.ofBijective_apply]
    exact maskSlot_apply z j b
  have h := averagedSecondMoment_le_box maskSlotEquiv _ (by omega) (card_zBox hp hs1)
    hE slotRoot_injective slotRoot_ne_zero hℓ
    (kernelBounds_signerCells hp sk₀ cTilde ha t τ hS₁ hfS)
    hq (fun i c => sum_normWeight_signerCells_sq_le hp sk₀ cTilde ha t τ i c) hδ
    ZMod.stdAddChar hψ (hintKernel_nonneg (by positivity)) (hintKernel_le_one _) hbox
    (smallSupportBounds_zBox h2G) (keySlot (fun b => sk₀.s1.get b)) 0
  rwa [ZMod.card] at h

end Box

attribute [local instance] concreteNTTRingOps

open Classical in
/-- **The averaged second moment at ML-DSA-44 with the sharp slot count**: at most `2^-154`
(`averagedSecondMoment_signerCells_le_box`, `envelope_box_mldsa44`). -/
theorem averagedSecondMoment_signerCells_le_mldsa44_box
    (sk₀ : SecretKey _root_.MLDSA.mldsa44) (cTilde : CommitHashBytes _root_.MLDSA.mldsa44)
    {G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengePoly}
    (ha : ∀ x, |cs2Shift (concreteWithSampleInBall _root_.MLDSA.mldsa44 G) sk₀ cTilde x| ≤
      _root_.MLDSA.mldsa44.beta)
    (hs1 : polyVecNorm ((concreteWithSampleInBall _root_.MLDSA.mldsa44 G).sampleInBall cTilde •
      sk₀.s1) ≤ _root_.MLDSA.mldsa44.beta)
    (t : ZMod 1025) (τ : Fin _root_.MLDSA.mldsa44.k → Rq) :
    averagedSecondMoment maskSlotEquiv
        (zBox _root_.MLDSA.mldsa44 ((concreteWithSampleInBall _root_.MLDSA.mldsa44 G).sampleInBall
          cTilde • sk₀.s1)) slotRoot
        (cellKernels (fun ic r => signerCells G sk₀ cTilde t τ ic r)
          (cellSize _root_.MLDSA.mldsa44))
        (keySlot (fun b => sk₀.s1.get b)) 0 ≤ 1 / 2 ^ 154 := by
  have hp := SigningParams.of_isApproved (p := _root_.MLDSA.mldsa44) (Or.inl rfl)
  obtain ⟨hk, hl, hg1, hg2, hb, -⟩ := mldsa44_vals
  have hG : 2 * (_root_.MLDSA.mldsa44.gamma1 - _root_.MLDSA.mldsa44.beta) - 1 = 261987 := by
    rw [hg1, hb]
  refine (averagedSecondMoment_signerCells_le_box hp sk₀ cTilde ha hs1 t τ (by norm_num)
    sum_hintKernel_le_mldsa44 (by rw [cellSize_mldsa44]) (by rw [hl]; norm_num)
    (by rw [hG]; norm_num)).trans ?_
  obtain ⟨hδ0, -, hδ2, hδ3, hδ4⟩ := smallSupportDelta_le
  obtain ⟨hδ'0, -, -, -, -, hδ'5⟩ := cellSupportDelta_le
  have hT : (modulus : ℝ) ^ 2 / (Fintype.card (Fin (bucketCount _root_.MLDSA.mldsa44)) *
      cellSize _root_.MLDSA.mldsa44 ^ 2) = 8380417 ^ 2 / (44 * 190307 ^ 2) := by
    rw [Fintype.card_fin, bucketCount_mldsa44, cellSize_mldsa44,
      show ((modulus : ℕ) : ℝ) = 8380417 by norm_num [modulus]]
    norm_num
  have hS₂ : (modulus : ℝ) / cellSize _root_.MLDSA.mldsa44 = 8380417 / 190307 := by
    rw [cellSize_mldsa44, show ((modulus : ℕ) : ℝ) = 8380417 by norm_num [modulus]]
  rw [hk, hl, hG, hT, hS₂, show ringDegree = 256 from rfl, show modulus = 8380417 from rfl]
  exact envelope_box_mldsa44 hδ0 smallSupportDelta_one_le_mldsa44 hδ2 hδ3 hδ4 (hδ'0 5) hδ'5
    (by norm_num) le_rfl (by positivity) le_rfl

/-- **Regularity at ML-DSA-44, `ℓ²` form.** At the concrete primitives with `SampleInBall = G` of
challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box and every
commitment hash `c̃`, over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â (∑_v |realMass v c̃ - ρ_z standinMass v c̃|)² ≤ (K |V| · 11 · 2^-77)²`. -/
theorem sum_sq_sum_abs_realMass_sub_le_mldsa44_box (sk₀ : SecretKey _root_.MLDSA.mldsa44)
    (hs1 : polyVecBounded sk₀.s1 _root_.MLDSA.mldsa44.eta) (hs2 : polyVecBounded sk₀.s2 _root_.MLDSA.mldsa44.eta)
    (cTilde : CommitHashBytes _root_.MLDSA.mldsa44) {G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall _root_.MLDSA.mldsa44 G)) :
    ∑ aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l, (∑ v : BucketVec _root_.MLDSA.mldsa44,
        |(realMass (concreteWithSampleInBall _root_.MLDSA.mldsa44 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v cTilde).toReal -
          (zAcceptFraction _root_.MLDSA.mldsa44 * standinMass (concreteWithSampleInBall _root_.MLDSA.mldsa44 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal|) ^ 2 ≤
      Fintype.card (TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l) *
        ((standinScale _root_.MLDSA.mldsa44).toReal * Fintype.card (BucketVec _root_.MLDSA.mldsa44) *
          (11 / 2 ^ 77)) ^ 2 := by
  have := concreteNTTRingLaws
  have hp := SigningParams.of_isApproved (p := _root_.MLDSA.mldsa44) (Or.inl rfl)
  have hlaws := signingLaws_concreteWithSampleInBall _root_.MLDSA.mldsa44 (Or.inl rfl) hG
  have hs1' := SigningLaws.polyVecNorm_sampleInBall_smul_le (concreteWithSampleInBall _root_.MLDSA.mldsa44 G) hlaws
    cTilde sk₀.s1 hs1
  have ha := fun x => SigningLaws.abs_cs2Shift_le (concreteWithSampleInBall _root_.MLDSA.mldsa44 G) sk₀ hlaws hs2 cTilde x
  have hω : _root_.MLDSA.mldsa44.omega < 1025 := by rw [mldsa44_vals.2.2.2.2.2]; norm_num
  have hN : Fintype.card (CoeffIndex _root_.MLDSA.mldsa44) < 1025 := by rw [card_coeffIndex_mldsa44]; norm_num
  have h := sum_sq_sum_abs_realMass_sub_le (M := 1025) hp hω hN sk₀ cTilde hs1' (cellSize_pos hp)
    (by positivity) fun t τ =>
      averagedSecondMoment_signerCells_le_mldsa44_box sk₀ cTilde ha hs1' t τ
  refine h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ 2) (Nat.cast_nonneg _))
  · exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)) (mul_nonneg (pow_nonneg (div_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (cellSize_pos hp).le) (Nat.cast_nonneg _)) _)
        (Real.sqrt_nonneg _))
  have hΛ : ∑ t : ZMod 1025, ‖ZMod.countCoeff 1025 _root_.MLDSA.mldsa44.omega t‖ ≤ 11 := by
    rw [mldsa44_vals.2.2.2.2.2]; exact sum_norm_countCoeff_le_mldsa44
  have hsq : √(1 / 2 ^ 154 : ℝ) = 1 / 2 ^ 77 := by
    rw [show (1 / 2 ^ 154 : ℝ) = (1 / 2 ^ 77) ^ 2 by
      rw [div_pow, one_pow, ← pow_mul], Real.sqrt_sq (by positivity)]
  have hV : (Fintype.card (BucketVec _root_.MLDSA.mldsa44) : ℝ) = 44 ^ (_root_.MLDSA.mldsa44.k * ringDegree) := by
    rw [card_bucketVec, bucketCount_mldsa44]
    push_cast
    try rfl
  rw [standinScale, ENNReal.toReal_mul, toReal_uniformScale, hV, hsq, bucketCount_mldsa44,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hρ : 0 ≤ (zAcceptFraction _root_.MLDSA.mldsa44).toReal := ENNReal.toReal_nonneg
  have hL := cellSize_pos hp
  generalize _root_.MLDSA.mldsa44.k * ringDegree = n
  generalize (zAcceptFraction _root_.MLDSA.mldsa44).toReal = ρ at hρ ⊢
  generalize cellSize _root_.MLDSA.mldsa44 = L at hL ⊢
  have hq : (0 : ℝ) < (modulus : ℕ) := by norm_num [modulus]
  generalize ((modulus : ℕ) : ℝ) = qq at hq ⊢
  have hpow : (((44 : ℕ) : ℝ) * L / qq) ^ n = (L / qq) ^ n * 44 ^ n := by
    rw [← mul_pow]; congr 1; push_cast; ring
  rw [hpow]
  generalize ∑ t : ZMod 1025, ‖ZMod.countCoeff 1025 _root_.MLDSA.mldsa44.omega t‖ = Λ at hΛ ⊢
  have hX : 0 ≤ (L / qq) ^ n * 44 ^ n * (1 / 2 ^ 77 : ℝ) := by positivity
  calc ρ * Λ * ((L / qq) ^ n * 44 ^ n * (1 / 2 ^ 77))
      ≤ ρ * 11 * ((L / qq) ^ n * 44 ^ n * (1 / 2 ^ 77)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛ hρ) hX
    _ = _ := by ring

/-- **Regularity at ML-DSA-44.** At the concrete primitives with `SampleInBall = G` of
challenge shape and the concrete NTT, for every key with `s₁, s₂` in the `η`-box and every
commitment hash `c̃`, averaged over the matrix `Â` (with `t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â ∑_v |realMass v c̃ - ρ_z standinMass v c̃| ≤ K |V| · 11 · 2^-77`. -/
theorem sum_abs_realMass_sub_le_mldsa44_box (sk₀ : SecretKey _root_.MLDSA.mldsa44)
    (hs1 : polyVecBounded sk₀.s1 _root_.MLDSA.mldsa44.eta) (hs2 : polyVecBounded sk₀.s2 _root_.MLDSA.mldsa44.eta)
    (cTilde : CommitHashBytes _root_.MLDSA.mldsa44) {G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall _root_.MLDSA.mldsa44 G)) :
    ∑ aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l, ∑ v : BucketVec _root_.MLDSA.mldsa44,
        |(realMass (concreteWithSampleInBall _root_.MLDSA.mldsa44 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v cTilde).toReal -
          (zAcceptFraction _root_.MLDSA.mldsa44 * standinMass (concreteWithSampleInBall _root_.MLDSA.mldsa44 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v cTilde).toReal| ≤
      Fintype.card (TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l) *
        ((standinScale _root_.MLDSA.mldsa44).toReal * Fintype.card (BucketVec _root_.MLDSA.mldsa44)) * (11 / 2 ^ 77) := by
  have h := sum_sq_sum_abs_realMass_sub_le_mldsa44_box sk₀ hs1 hs2 cTilde hG
  rw [← Finset.card_univ (α := TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l)] at h
  have h1 := Finset.sum_le_card_mul_of_sum_sq_le
    (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)) (by norm_num)) h
  rw [Finset.card_univ] at h1
  exact h1.trans_eq (by ring)

/-- **The mean square column error at ML-DSA-44**: with `SampleInBall = G` of challenge shape and
the concrete NTT, for every key with `s₁, s₂` in the `η`-box, averaged over the matrix `Â` (with
`t₀` recomputed from `Â s₁ + s₂`):
`𝔼_Â (∑_v 𝔼_c̃ |realMass v c̃ - ρ_z standinMass v c̃|)² ≤ (K |V| · 11 · 2^-77)²`. -/
theorem expect_sq_sum_expect_abs_realMass_sub_le_mldsa44_box (sk₀ : SecretKey _root_.MLDSA.mldsa44)
    (hs1 : polyVecBounded sk₀.s1 _root_.MLDSA.mldsa44.eta) (hs2 : polyVecBounded sk₀.s2 _root_.MLDSA.mldsa44.eta)
    {G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall _root_.MLDSA.mldsa44 G)) :
    𝔼 aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l, (∑ v : BucketVec _root_.MLDSA.mldsa44, 𝔼 c,
        |(realMass (concreteWithSampleInBall _root_.MLDSA.mldsa44 G) (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b)
            (matOfHat aHat))) aHat v c).toReal -
          (zAcceptFraction _root_.MLDSA.mldsa44 * standinMass (concreteWithSampleInBall _root_.MLDSA.mldsa44 G)
            (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) v c).toReal|) ^ 2 ≤
      ((standinScale _root_.MLDSA.mldsa44).toReal * Fintype.card (BucketVec _root_.MLDSA.mldsa44) * (11 / 2 ^ 77)) ^ 2 :=
  Finset.expect_sq_sum_expect_le _ fun c =>
    sum_sq_sum_abs_realMass_sub_le_mldsa44_box sk₀ hs1 hs2 c hG

/-- **The mean regularity gap at ML-DSA-44 by Cauchy–Schwarz over the matrix.** With
`SampleInBall = G` of challenge shape and the concrete NTT, for keys with `s₁, s₂` in the
`η`-box, `t₀` recomputed from the uniform matrix `Â`, and any positive lower bound `w Â` on the
mean member weights of every bucket vector,
`𝔼_Â ringRegGap ≤ 11 · 2^-77 / β_min · √(𝔼_Â (w Â)⁻²)`. -/
theorem expect_ringRegGap_le_sqrt_mldsa44_box (sk₀ : SecretKey _root_.MLDSA.mldsa44)
    (hs1 : polyVecBounded sk₀.s1 _root_.MLDSA.mldsa44.eta) (hs2 : polyVecBounded sk₀.s2 _root_.MLDSA.mldsa44.eta)
    {G : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengePoly}
    (hG : SampleInBallShape (concreteWithSampleInBall _root_.MLDSA.mldsa44 G))
    {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    {w : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l → ℝ}
    (hw0 : ∀ aHat, 0 < w aHat)
    (hw : ∀ (aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l) v, w aHat ≤ 𝔼 c,
      (memberWeight (concreteWithSampleInBall _root_.MLDSA.mldsa44 G) βmin
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 (v, c) : ℝ≥0∞).toReal) :
    𝔼 aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l, ringRegGap (concreteWithSampleInBall _root_.MLDSA.mldsa44 G)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) aHat βmin ≤
      11 / 2 ^ 77 / (βmin : ℝ≥0∞).toReal *
        √(𝔼 aHat : TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l, (w aHat ^ 2)⁻¹) :=
  expect_ringRegGap_le_sqrt
    (SigningParams.of_isApproved (p := _root_.MLDSA.mldsa44) (Or.inl rfl)) _
    (fun aHat => keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) hβ0 hβt hw0 hw
    (by norm_num)
    (expect_sq_sum_expect_abs_realMass_sub_le_mldsa44_box sk₀ hs1 hs2 hG)


end GordieHowe.MLDSA.Regularity
