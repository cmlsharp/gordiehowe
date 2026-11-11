-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.Signer
public import GordieHowe.Applications.MLDSA.Flattened.Core.Oracle
public import GordieHowe.Applications.MLDSA.Regularity.CommitPoint

public section

/-!
# The keep probability and the oracle concentration term of the flattened signer

* `le_flatKeepProb_of_keyFloorAt`: under the floor at a cut-off, one attempt keeps with
  probability at least `K · top · |V| · s̄ · (1 - ε - signerRegGap)`, `K = standinScale` and `s̄`
  the mean shape (`sub_signerRegDev_le_toReal_one_sub_flatAttempt` with the keep factor `shape`,
  `signerRegDev_le_meanShape`; against a uniform commitment-hash function as often as fresh,
  `jointAttempt_oracleAttempt_apply_none`).
* `w1MaxProb_eq_commitPointMax`: the largest probability of one commitment is the point
  probability `commitPointMax` of `GordieHowe/Applications/MLDSA/Regularity/CommitPoint.lean`.
* `flatOracleConcError_le_of_keyFloorAt`: the oracle concentration term is at most
  `√(commitPointMax / (K · top · |V| · s̄ · (1 - ε - signerRegGap))) / 2`
  (`flatOracleConcError_le`).
* `min_one_mul_flatOracleConcError_le_of_keyFloorAt`: for averaging over the matrix,
  `min(1, Q · conc)` is at most
  `Q · √(2 · commitPointMax / (K · top · |V| · s̄ · (1 - ε))) / 2 + 2 · signerRegGap / (1 - ε)`,
  splitting on `signerRegGap ≤ (1 - ε) / 2`.
* `le_flatKeepProb_of_keyFloor`, `signerKeeps_of_keyFloor`,
  `one_sub_le_signerRegGap_of_not_signerKeeps`, `flatOracleConcError_le_of_keyFloor`,
  `min_one_mul_flatOracleConcError_le`: the constant cut-off `β_min` under `KeyFloor`, where
  `top = β_min` and `s̄ = 1`.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete Finset PMF GordieHowe.MLDSA.Regularity
open scoped ENNReal BigOperators

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] (sk : SecretKey p) (aHat : TqMatrix p.k p.l)

/-- **The keep probability against a uniform commitment-hash function is the fresh one**: that of
the attempt with the unit keep factor (`jointAttempt_oracleAttempt_apply_none`). -/
theorem flatKeepProb_eq (cut : Cutoff p) :
    flatKeepProb prims sk aHat cut =
      (1 - flatAttempt prims sk aHat cut (KeepFactor.one : KeepFactor p Unit) none).toReal := by
  rw [flatKeepProb, flatAttempt_one_apply_none]
  exact congrArg (fun x : ℝ≥0∞ => (1 - x).toReal) (jointAttempt_oracleAttempt_apply_none
    (maskUniform p) (realBuckets aHat) (attemptAccept prims sk aHat)
    (fun a => (flattenCoin prims sk cut a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk cut))

/-- **The keep probability under the floor at a cut-off**: one attempt keeps with probability at
least `K · top · |V| · s̄ · (1 - ε - signerRegGap)`, `s̄` the mean shape. -/
theorem le_flatKeepProb_of_keyFloorAt (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) {cut : Cutoff p} {ε : ℝ}
    (hf : KeyFloorAt prims cut ε sk.t0) :
    (standinScale p * cut.top).toReal * Fintype.card (BucketVec p) * cut.meanShape *
        (1 - ε - signerRegGap prims sk aHat cut) ≤ flatKeepProb prims sk aHat cut := by
  have h := sub_signerRegDev_le_toReal_one_sub_flatAttempt prims sk aHat cut
    (KeepFactor.one : KeepFactor p Unit) hp h_laws hs2 hf.keyFloorOn_one
  rw [keepMass_keep_one] at h
  rw [flatKeepProb_eq]
  have hdev := signerRegDev_le_meanShape prims sk aHat hp hf.cutoff_ne_zero hf.cutoff_ne_top
    (hf.expect_flatWeight_mul_shape_pos hp)
  have e : (standinScale p * cut.top).toReal * Fintype.card (BucketVec p) * cut.meanShape *
      (1 - ε - signerRegGap prims sk aHat cut) =
      (standinScale p * cut.top).toReal *
          ((1 - ε) * (Fintype.card (BucketVec p) * cut.meanShape)) -
        signerRegGap prims sk aHat cut *
          ((standinScale p * cut.top).toReal * Fintype.card (BucketVec p) * cut.meanShape) := by
    ring
  linarith

/-- **The largest probability of one commitment is the point probability `commitPointMax`.** -/
theorem w1MaxProb_eq_commitPointMax : w1MaxProb aHat = commitPointMax aHat := by
  rw [w1MaxProb, commitPointMax, Finset.sup'_univ_eq_ciSup]

theorem commitPointMax_nonneg : 0 ≤ commitPointMax aHat :=
  ENNReal.toReal_nonneg.trans (toReal_map_realBuckets_le_commitPointMax aHat
    (Classical.arbitrary _))

/-- **The oracle concentration term under the floor at a cut-off**: when `signerRegGap < 1 - ε`,
at most `√(commitPointMax / (K · top · |V| · s̄ · (1 - ε - signerRegGap))) / 2`
(`flatOracleConcError_le`, `le_flatKeepProb_of_keyFloorAt`). -/
theorem flatOracleConcError_le_of_keyFloorAt (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) {cut : Cutoff p} {ε : ℝ}
    (hf : KeyFloorAt prims cut ε sk.t0) (hgap : signerRegGap prims sk aHat cut < 1 - ε) :
    flatOracleConcError prims sk aHat cut ≤
      √(commitPointMax aHat / ((standinScale p * cut.top).toReal * Fintype.card (BucketVec p) *
        cut.meanShape * (1 - ε - signerRegGap prims sk aHat cut))) / 2 := by
  refine (flatOracleConcError_le prims sk aHat cut
    (signerKeeps_of_keyFloorAt prims sk aHat hp h_laws hs2 hf hgap)).trans ?_
  rw [w1MaxProb_eq_commitPointMax]
  have hK := flatLevel_pos hp hf.cutoff_ne_zero hf.cutoff_ne_top
  have hV : (0 : ℝ) < Fintype.card (BucketVec p) := Nat.cast_pos.2 Fintype.card_pos
  have hpos := mul_pos (mul_pos (mul_pos hK hV) cut.meanShape_pos) (sub_pos.2 hgap)
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left
    (commitPointMax_nonneg aHat) hpos (le_flatKeepProb_of_keyFloorAt prims sk aHat hp h_laws
      hs2 hf))) zero_le_two

/-- **The oracle concentration term, capped at one, for averaging**: under the floor at a
cut-off, for every `Q`, `min(1, Q · flatOracleConcError)` is at most
`Q · √(2 · commitPointMax / (K · top · |V| · s̄ · (1 - ε))) / 2 + 2 · signerRegGap / (1 - ε)`. When
`signerRegGap ≤ (1 - ε) / 2` the keep probability is at least `K · top · |V| · s̄ · (1 - ε) / 2`
(`flatOracleConcError_le_of_keyFloorAt`); otherwise the second term is at least one. -/
theorem min_one_mul_flatOracleConcError_le_of_keyFloorAt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {cut : Cutoff p} {ε : ℝ}
    (hf : KeyFloorAt prims cut ε sk.t0) (Q : ℕ) :
    min 1 (Q * flatOracleConcError prims sk aHat cut) ≤
      Q * √(2 * commitPointMax aHat / ((standinScale p * cut.top).toReal *
          Fintype.card (BucketVec p) * cut.meanShape * (1 - ε))) / 2 +
        2 * signerRegGap prims sk aHat cut / (1 - ε) := by
  have h1 : 0 < 1 - ε := by linarith [hf.lt_one]
  have hg0 := signerRegGap_nonneg prims sk aHat cut
  have hK := flatLevel_pos hp hf.cutoff_ne_zero hf.cutoff_ne_top
  have hV : (0 : ℝ) < Fintype.card (BucketVec p) := Nat.cast_pos.2 Fintype.card_pos
  have hKV := mul_pos (mul_pos hK hV) cut.meanShape_pos
  set L := (standinScale p * cut.top).toReal * Fintype.card (BucketVec p) * cut.meanShape
  have hT : 0 ≤ (Q : ℝ) * √(2 * commitPointMax aHat / (L * (1 - ε))) / 2 := by
    positivity
  have hG : 0 ≤ 2 * signerRegGap prims sk aHat cut / (1 - ε) := by positivity
  by_cases hg : signerRegGap prims sk aHat cut ≤ (1 - ε) / 2
  · have hgap : signerRegGap prims sk aHat cut < 1 - ε := by linarith
    have hc := flatOracleConcError_le_of_keyFloorAt prims sk aHat hp h_laws hs2 hf hgap
    have hden : L * (1 - ε) / 2 ≤ L * (1 - ε - signerRegGap prims sk aHat cut) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) hKV.le
    have hsq : √(commitPointMax aHat / (L * (1 - ε - signerRegGap prims sk aHat cut))) ≤
        √(2 * commitPointMax aHat / (L * (1 - ε))) := by
      refine Real.sqrt_le_sqrt ?_
      rw [show 2 * commitPointMax aHat / (L * (1 - ε)) =
          commitPointMax aHat / (L * (1 - ε) / 2) by field_simp]
      exact div_le_div_of_nonneg_left (commitPointMax_nonneg aHat) (by positivity) hden
    calc min 1 (Q * flatOracleConcError prims sk aHat cut)
        ≤ Q * flatOracleConcError prims sk aHat cut := min_le_right _ _
      _ ≤ Q * (√(2 * commitPointMax aHat / (L * (1 - ε))) / 2) :=
          mul_le_mul_of_nonneg_left (hc.trans (div_le_div_of_nonneg_right hsq zero_le_two))
            (Nat.cast_nonneg Q)
      _ ≤ _ := by rw [← mul_div_assoc]; linarith
  · have h2 : 1 ≤ 2 * signerRegGap prims sk aHat cut / (1 - ε) := by
      rw [le_div_iff₀ h1]; linarith
    calc min 1 (Q * flatOracleConcError prims sk aHat cut) ≤ 1 := min_le_left _ _
      _ ≤ _ := by linarith

/-! ### The constant cut-off -/

variable (βmin : ℚ≥0)

/-- **The keep probability under the floor**: one attempt keeps with probability at least
`K · β_min · |V| · (1 - ε - signerRegGap)` (`le_flatKeepProb_of_keyFloorAt`). -/
theorem le_flatKeepProb_of_keyFloor (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ} (hf : KeyFloor prims βmin ε sk.t0) :
    (standinScale p * βmin).toReal * Fintype.card (BucketVec p) *
        (1 - ε - signerRegGap prims sk aHat (Cutoff.const βmin)) ≤ flatKeepProb prims sk aHat
            (Cutoff.const βmin) := by
  have h := le_flatKeepProb_of_keyFloorAt prims sk aHat hp h_laws hs2
    (keyFloorAt_const_iff.2 hf)
  rwa [Cutoff.meanShape_const, mul_one] at h

/-- **The signer keeps under the floor** when its regularity gap is below `1 - ε`
(`signerKeeps_of_keyFloorAt`). -/
theorem signerKeeps_of_keyFloor (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ} (hf : KeyFloor prims βmin ε sk.t0)
    (hgap : signerRegGap prims sk aHat (Cutoff.const βmin) < 1 - ε) : SignerKeeps prims sk aHat
        (Cutoff.const βmin) :=
  signerKeeps_of_keyFloorAt prims sk aHat hp h_laws hs2 (keyFloorAt_const_iff.2 hf) hgap

/-- **A signer that never keeps has regularity gap at least `1 - ε`** under the floor
(`one_sub_le_signerRegGap_of_keyFloorAt`). -/
theorem one_sub_le_signerRegGap_of_not_signerKeeps (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloor prims βmin ε sk.t0) (h : ¬ SignerKeeps prims sk aHat (Cutoff.const βmin)) :
    1 - ε ≤ signerRegGap prims sk aHat (Cutoff.const βmin) :=
  one_sub_le_signerRegGap_of_keyFloorAt prims sk aHat hp h_laws hs2 (keyFloorAt_const_iff.2 hf) h

/-- **The oracle concentration term under the floor**: when `signerRegGap < 1 - ε`, at most
`√(commitPointMax / (K · β_min · |V| · (1 - ε - signerRegGap))) / 2`
(`flatOracleConcError_le_of_keyFloorAt`). -/
theorem flatOracleConcError_le_of_keyFloor (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ} (hf : KeyFloor prims βmin ε sk.t0)
    (hgap : signerRegGap prims sk aHat (Cutoff.const βmin) < 1 - ε) :
    flatOracleConcError prims sk aHat (Cutoff.const βmin) ≤
      √(commitPointMax aHat / ((standinScale p * βmin).toReal * Fintype.card (BucketVec p) *
        (1 - ε - signerRegGap prims sk aHat (Cutoff.const βmin)))) / 2 := by
  have h := flatOracleConcError_le_of_keyFloorAt prims sk aHat hp h_laws hs2
    (keyFloorAt_const_iff.2 hf) hgap
  rwa [Cutoff.meanShape_const, mul_one] at h

/-- **The oracle concentration term, capped at one, for averaging**: under the floor, for every
`Q`, `min(1, Q · flatOracleConcError)` is at most
`Q · √(2 · commitPointMax / (K · β_min · |V| · (1 - ε))) / 2 + 2 · signerRegGap / (1 - ε)`
(`min_one_mul_flatOracleConcError_le_of_keyFloorAt`). -/
theorem min_one_mul_flatOracleConcError_le (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ} (hf : KeyFloor prims βmin ε sk.t0) (Q : ℕ) :
    min 1 (Q * flatOracleConcError prims sk aHat (Cutoff.const βmin)) ≤
      Q * √(2 * commitPointMax aHat /
          ((standinScale p * βmin).toReal * Fintype.card (BucketVec p) * (1 - ε))) / 2 +
        2 * signerRegGap prims sk aHat (Cutoff.const βmin) / (1 - ε) := by
  have h := min_one_mul_flatOracleConcError_le_of_keyFloorAt prims sk aHat hp h_laws hs2
    (keyFloorAt_const_iff.2 hf) Q
  rwa [Cutoff.meanShape_const, mul_one] at h

end GordieHowe.MLDSA
