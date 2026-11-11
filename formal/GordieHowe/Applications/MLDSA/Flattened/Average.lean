-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.Signer
public import GordieHowe.Applications.MLDSA.Regularity.InstancesSeven

public section

/-!
# The single-key flattened signer over a uniform matrix

With `ExpandA` a random oracle the matrix `Â` is uniform, and the key's `t₀` is recomputed from
`A s₁ + s₂` (`matrixKey`, `keyOf`). At a cut-off with level `top`, averaging
`tvDist_flatSigner_shapedTarget_le_of_keyFloorAt` over the matrices of a set `S` with the
regularity bounds `expect_signerRegGap_le_mldsa65_seven` and `expect_signerRegGap_le_mldsa87_seven`
(column means of the flattened weight times the shape at least `(1 - ε)` times the mean shape
under the floor):

* `expect_tvDist_flatSigner_shapedTarget_le_mldsa65_of_keyFloorAt`: at ML-DSA-65,
  `𝔼_Â 1_S(Â) · tvDist ≤ ε + 11 · 2^-199 / ((1 - ε)² · top · meanShape)`;
* `expect_tvDist_flatSigner_shapedTarget_le_mldsa87_of_keyFloorAt`: at ML-DSA-87,
  `𝔼_Â 1_S(Â) · tvDist ≤ ε + 12 · 2^-294 / ((1 - ε)² · top · meanShape)`.

The floor is assumed only at the matrices of `S`, since it bounds the key's `t₀`, which depends
on `Â`: a check at key generation holds at some matrices and fails at others. At the constant
cut-off and `S` every matrix these are `expect_tvDist_flatSigner_flatTarget_le_mldsa65_of_keyFloor`
and `_mldsa87_of_keyFloor`, against the uniform target.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete Finset PMF GordieHowe.MLDSA.Regularity
open scoped ENNReal BigOperators

section Generic

variable [nttOps : NTTRingOps]

/-- **The key at the matrix `Â`**: `sk₀` with `t₀` recomputed from `A s₁ + s₂`, `A = NTT⁻¹(Â)`
(FIPS 204 Algorithm 6, `keyOf`). -/
noncomputable def matrixKey {p : Params} (sk₀ : SecretKey p) (aHat : TqMatrix p.k p.l) :
    SecretKey p :=
  keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))

theorem matrixKey_eq {p : Params} (sk₀ : SecretKey p) (aHat : TqMatrix p.k p.l) :
    matrixKey sk₀ aHat = keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat)) := by
  rw [matrixKey]

/-- The key at a matrix keeps `s₂`. -/
theorem matrixKey_s2 {p : Params} (sk₀ : SecretKey p) (aHat : TqMatrix p.k p.l) :
    (matrixKey sk₀ aHat).s2 = sk₀.s2 := by
  rw [matrixKey, keyOf]

/-- **The averaging step at a cut-off**: if the signer is within
`ε + signerRegGap / (1 - ε)` of the shaped target at every matrix of `S` and
`𝔼_Â 1_S(Â) · signerRegGap ≤ R`, then `𝔼_Â 1_S(Â) · tvDist ≤ ε + R / (1 - ε)`. -/
theorem expect_tvDist_le_of_expect_signerRegGap_le_of_keyFloorAt {p : Params}
    [NeZero (bucketCount p)] (prims : Primitives p) [Nonempty (MaskBox p)]
    (hp : SigningParams p) (h_laws : SigningLaws prims) {sk₀ : SecretKey p}
    (hs2 : polyVecBounded sk₀.s2 p.eta) {cut : Cutoff p} {ε R : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (S : Set (TqMatrix p.k p.l))
    (hf : ∀ aHat ∈ S, KeyFloorAt prims cut ε (matrixKey sk₀ aHat).t0)
    (hR : 𝔼 aHat : TqMatrix p.k p.l,
        S.indicator (fun aHat => signerRegGap prims (matrixKey sk₀ aHat) aHat cut) aHat ≤ R) :
    𝔼 aHat : TqMatrix p.k p.l,
        S.indicator (fun aHat => tvDist (realKeptLaw prims (matrixKey sk₀ aHat) aHat cut)
          (shapedTarget cut)) aHat ≤ ε + R / (1 - ε) := by
  have h1 : 0 < 1 - ε := sub_pos.2 hε1
  calc 𝔼 aHat : TqMatrix p.k p.l,
        S.indicator (fun aHat => tvDist (realKeptLaw prims (matrixKey sk₀ aHat) aHat cut)
          (shapedTarget cut)) aHat
      ≤ 𝔼 aHat : TqMatrix p.k p.l, (ε + S.indicator (fun aHat =>
          signerRegGap prims (matrixKey sk₀ aHat) aHat cut) aHat / (1 - ε)) :=
        expect_le_expect fun aHat _ => by
          by_cases h : aHat ∈ S
          · simp only [Set.indicator_of_mem h]
            exact tvDist_flatSigner_shapedTarget_le_of_keyFloorAt prims (matrixKey sk₀ aHat) aHat
              hp h_laws (by rw [matrixKey_s2]; exact hs2) (hf aHat h)
          · simp only [Set.indicator_of_notMem h, zero_div, add_zero]
            exact hε
    _ = ε + (𝔼 aHat : TqMatrix p.k p.l, S.indicator (fun aHat =>
          signerRegGap prims (matrixKey sk₀ aHat) aHat cut) aHat) / (1 - ε) := by
        rw [expect_add_distrib, expect_const univ_nonempty, expect_div]
    _ ≤ ε + R / (1 - ε) := by gcongr

/-- **The averaging step**: if the signer is within `ε + signerRegGap / (1 - ε)` of the
target at every matrix and `𝔼_Â signerRegGap ≤ R`, then `𝔼_Â tvDist ≤ ε + R / (1 - ε)`
(`expect_tvDist_le_of_expect_signerRegGap_le_of_keyFloorAt` at the constant cut-off and every
matrix). -/
theorem expect_tvDist_le_of_expect_signerRegGap_le {p : Params} [NeZero (bucketCount p)]
    (prims : Primitives p) [Nonempty (MaskBox p)]
    (hp : SigningParams p) (h_laws : SigningLaws prims) {sk₀ : SecretKey p}
    (hs2 : polyVecBounded sk₀.s2 p.eta) {βmin : ℚ≥0} {ε R : ℝ}
    (hf : ∀ aHat, KeyFloor prims βmin ε (matrixKey sk₀ aHat).t0)
    (hR : 𝔼 aHat : TqMatrix p.k p.l, signerRegGap prims (matrixKey sk₀ aHat) aHat
        (Cutoff.const βmin) ≤ R) :
    𝔼 aHat : TqMatrix p.k p.l, tvDist (realKeptLaw prims (matrixKey sk₀ aHat) aHat
        (Cutoff.const βmin))
        (flatTarget p) ≤ ε + R / (1 - ε) := by
  have hf₀ := hf (Classical.arbitrary _)
  have h := expect_tvDist_le_of_expect_signerRegGap_le_of_keyFloorAt prims hp h_laws hs2
    (cut := Cutoff.const βmin) hf₀.nonneg hf₀.lt_one Set.univ
    (fun aHat _ => keyFloorAt_const_iff.2 (hf aHat)) (by simpa only [Set.indicator_univ] using hR)
  simpa only [Set.indicator_univ, shapedTarget_const] using h

end Generic

attribute [local instance] concreteNTTRingOps

/-- **The single-key flattened signer at ML-DSA-65 over a uniform matrix, at a cut-off**
(`ExpandA` a random oracle). For a key `sk₀` with `s₁, s₂` in the `η`-box whose `t₀` satisfies the
floor at the cut-off with defect bound `ε ≥ 0` at every matrix of a set `S`, the law of `(w₁, c̃)`
counted on `S` is on average over a uniform `Â` within
`ε + 11 · 2^-199 / ((1 - ε)² · top · meanShape)` of the shaped target
(`expect_signerRegGap_le_mldsa65_seven` with column means at least `(1 - ε) · meanShape`). -/
theorem expect_tvDist_flatSigner_shapedTarget_le_mldsa65_of_keyFloorAt (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {cut : Cutoff mldsa65} {ε : ℝ} (hε : 0 ≤ ε) (S : Set (TqMatrix mldsa65.k mldsa65.l))
    (hf : ∀ aHat ∈ S, KeyFloorAt (concretePrimitives mldsa65) cut ε (matrixKey sk₀ aHat).t0) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l,
        S.indicator (fun aHat => tvDist (realKeptLaw (concretePrimitives mldsa65)
          (matrixKey sk₀ aHat) aHat cut) (shapedTarget cut)) aHat ≤
      ε + 11 / 2 ^ 199 / ((1 - ε) ^ 2 * ((cut.top : ℝ≥0∞).toReal * cut.meanShape)) := by
  have hm := cut.meanShape_pos
  rcases S.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp only [Set.indicator_empty, expect_const_zero]
    positivity
  have hp := SigningParams.of_isApproved (p := mldsa65) (Or.inr (Or.inl rfl))
  have hf₀ := hf a₀ ha₀
  have h1 : 0 < 1 - ε := sub_pos.2 hf₀.lt_one
  refine (expect_tvDist_le_of_expect_signerRegGap_le_of_keyFloorAt (concretePrimitives mldsa65) hp
    (signingLaws_concrete mldsa65 (Or.inr (Or.inl rfl))) hs2 hε hf₀.lt_one S hf
    (R := 11 / 2 ^ 199 / ((1 - ε) * cut.meanShape * (cut.top : ℝ≥0∞).toReal)) ?_).trans_eq ?_
  · simp only [matrixKey_eq]
    exact expect_signerRegGap_le_mldsa65_seven sk₀ hs1 hs2 hf₀.cutoff_ne_zero hf₀.cutoff_ne_top
      (mul_pos h1 hm) S fun aHat h v => by
        simpa only [matrixKey_eq] using (hf aHat h).one_sub_mul_le_expect_flatWeight hp v
  · rw [div_div]
    congr 2
    ring

/-- **The single-key flattened signer at ML-DSA-65 over a uniform matrix** (`ExpandA` a random
oracle). For a key `sk₀` with `s₁, s₂` in the `η`-box whose `t₀` at every matrix satisfies the
per-key floor at `β_min` with defect bound `ε < 1`, the law of `(w₁, c̃)` is on average over a
uniform `Â` within `ε + 11 · 2^-199 / ((1 - ε)² β_min)` of the uniform target
(`expect_tvDist_flatSigner_shapedTarget_le_mldsa65_of_keyFloorAt` at the constant cut-off and every
matrix). The floor is assumed at every matrix `Â`, since `t₀` depends on `Â`. -/
theorem expect_tvDist_flatSigner_flatTarget_le_mldsa65_of_keyFloor (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {βmin : ℚ≥0} {ε : ℝ}
    (hf : ∀ aHat, KeyFloor (concretePrimitives mldsa65) βmin ε (matrixKey sk₀ aHat).t0) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l,
        tvDist (realKeptLaw (concretePrimitives mldsa65) (matrixKey sk₀ aHat) aHat
            (Cutoff.const βmin))
          (flatTarget mldsa65) ≤
      ε + 11 / 2 ^ 199 / ((1 - ε) ^ 2 * (βmin : ℝ≥0∞).toReal) := by
  have h := expect_tvDist_flatSigner_shapedTarget_le_mldsa65_of_keyFloorAt sk₀ hs1 hs2
    (cut := Cutoff.const βmin) (hf (Classical.arbitrary _)).nonneg Set.univ
    fun aHat _ => keyFloorAt_const_iff.2 (hf aHat)
  simpa only [Set.indicator_univ, shapedTarget_const, Cutoff.meanShape_const, mul_one] using h

/-- **The single-key flattened signer at ML-DSA-87 over a uniform matrix, at a cut-off**: as
`expect_tvDist_flatSigner_shapedTarget_le_mldsa65_of_keyFloorAt`, within
`ε + 12 · 2^-294 / ((1 - ε)² · top · meanShape)` of the shaped target
(`expect_signerRegGap_le_mldsa87_seven`). -/
theorem expect_tvDist_flatSigner_shapedTarget_le_mldsa87_of_keyFloorAt (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {cut : Cutoff mldsa87} {ε : ℝ} (hε : 0 ≤ ε) (S : Set (TqMatrix mldsa87.k mldsa87.l))
    (hf : ∀ aHat ∈ S, KeyFloorAt (concretePrimitives mldsa87) cut ε (matrixKey sk₀ aHat).t0) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l,
        S.indicator (fun aHat => tvDist (realKeptLaw (concretePrimitives mldsa87)
          (matrixKey sk₀ aHat) aHat cut) (shapedTarget cut)) aHat ≤
      ε + 12 / 2 ^ 294 / ((1 - ε) ^ 2 * ((cut.top : ℝ≥0∞).toReal * cut.meanShape)) := by
  have hm := cut.meanShape_pos
  rcases S.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp only [Set.indicator_empty, expect_const_zero]
    positivity
  have hp := SigningParams.of_isApproved (p := mldsa87) (Or.inr (Or.inr rfl))
  have hf₀ := hf a₀ ha₀
  have h1 : 0 < 1 - ε := sub_pos.2 hf₀.lt_one
  refine (expect_tvDist_le_of_expect_signerRegGap_le_of_keyFloorAt (concretePrimitives mldsa87) hp
    (signingLaws_concrete mldsa87 (Or.inr (Or.inr rfl))) hs2 hε hf₀.lt_one S hf
    (R := 12 / 2 ^ 294 / ((1 - ε) * cut.meanShape * (cut.top : ℝ≥0∞).toReal)) ?_).trans_eq ?_
  · simp only [matrixKey_eq]
    exact expect_signerRegGap_le_mldsa87_seven sk₀ hs1 hs2 hf₀.cutoff_ne_zero hf₀.cutoff_ne_top
      (mul_pos h1 hm) S fun aHat h v => by
        simpa only [matrixKey_eq] using (hf aHat h).one_sub_mul_le_expect_flatWeight hp v
  · rw [div_div]
    congr 2
    ring

/-- **The single-key flattened signer at ML-DSA-87 over a uniform matrix** (`ExpandA` a random
oracle): as `expect_tvDist_flatSigner_flatTarget_le_mldsa65_of_keyFloor`, within
`ε + 12 · 2^-294 / ((1 - ε)² β_min)` of the uniform target
(`expect_tvDist_flatSigner_shapedTarget_le_mldsa87_of_keyFloorAt`). -/
theorem expect_tvDist_flatSigner_flatTarget_le_mldsa87_of_keyFloor (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {βmin : ℚ≥0} {ε : ℝ}
    (hf : ∀ aHat, KeyFloor (concretePrimitives mldsa87) βmin ε (matrixKey sk₀ aHat).t0) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l,
        tvDist (realKeptLaw (concretePrimitives mldsa87) (matrixKey sk₀ aHat) aHat
            (Cutoff.const βmin))
          (flatTarget mldsa87) ≤
      ε + 12 / 2 ^ 294 / ((1 - ε) ^ 2 * (βmin : ℝ≥0∞).toReal) := by
  have h := expect_tvDist_flatSigner_shapedTarget_le_mldsa87_of_keyFloorAt sk₀ hs1 hs2
    (cut := Cutoff.const βmin) (hf (Classical.arbitrary _)).nonneg Set.univ
    fun aHat _ => keyFloorAt_const_iff.2 (hf aHat)
  simpa only [Set.indicator_univ, shapedTarget_const, Cutoff.meanShape_const, mul_one] using h

end GordieHowe.MLDSA
