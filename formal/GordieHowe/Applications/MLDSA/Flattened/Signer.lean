-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.Target
public import GordieHowe.Applications.MLDSA.Flattened.Core.RealStandin
public import GordieHowe.Foundations.ToMathlib.PMFCondSome

public section

/-!
# The single-key flattened ML-DSA signer at a fixed matrix

The signer's law of `(w₁, c̃)` with a fresh uniform commitment hash per attempt is
`realKeptLaw` (`Flatten.lean`), the kept law of the loop signer `flatLoopSigner`
(`Core/Weights.lean`, `realKeptLaw_eq_keptLaw`). The commitment-hash oracle shared across attempts
and presentations is left to the presentation bound.

* `tvDist_realKeptLaw_standinKeptLaw_le_of_keyFloorAt`: when the signer keeps with positive
  probability, the real and stand-in kept laws are within `signerRegGap / (1 - ε)` under the floor
  at the cut-off: the core's real-against-stand-in bound with the keep factor `shape`
  (`tvDist_flatKeptLaw_standinFlatKeptLaw_le_of_keyFloorOn`), whose kept mass `|V| · s̄`
  (`keepMass_keep_one`) and column deviations `signerRegGap · K · top · |V| · s̄`
  (`signerRegDev_le_meanShape`) carry the same mean shape `s̄`.
* `signerKeeps_of_keyFloorAt`, `one_sub_le_signerRegGap_of_keyFloorAt`: the signer keeps when
  `signerRegGap < 1 - ε`, so a signer that never keeps has `1 - ε ≤ signerRegGap`.
* `tvDist_flatSigner_shapedTarget_le_of_keyFloorAt`: under the floor at the cut-off, the signer's
  law is within `ε + signerRegGap / (1 - ε)` of `shapedTarget`.
* `tvDist_realKeptLaw_standinKeptLaw_le_of_keyFloor`, `tvDist_flatSigner_flatTarget_le_of_keyFloor`:
  the constant cut-off `β_min` under `KeyFloor`, against the uniform target.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete Finset PMF
open scoped ENNReal BigOperators

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] (sk : SecretKey p) (aHat : TqMatrix p.k p.l)

/-- **The single-key flattened signer with fresh hashes**: `realKeptLaw` is
the kept law (`LoopSigner.keptLaw`) of `flatLoopSigner`, whose proposal, commitment, acceptance and
keep coin are those of `realKeptLaw`. -/
theorem realKeptLaw_eq_keptLaw (hp : SigningParams p) {cut : Cutoff p}
    (hβ0 : (cut.top : ℝ≥0∞) ≠ 0) (hβt : (cut.top : ℝ≥0∞) ≠ ⊤) :
    realKeptLaw prims sk aHat cut = (flatLoopSigner prims sk aHat hp hβ0 hβt).keptLaw := by
  rw [LoopSigner.keptLaw, realKeptLaw]

/-- **The real and stand-in kept laws under the floor at a cut-off.** When the signer's fresh
attempt keeps with positive probability (`SignerKeeps`), the law of `(w₁, c̃)` with `y` uniform on
the mask box (`realKeptLaw`) is within `signerRegGap / (1 - ε)` of the stand-in law with `w`
uniform (`standinKeptLaw`): the core's bound with no side data and the keep factor `shape`
(`tvDist_flatKeptLaw_standinFlatKeptLaw_le_of_keyFloorOn`), whose denominator
`K · top · (1 - ε) · |V| · s̄` (`keepMass_keep_one`) and column deviations
`signerRegGap · K · top · |V| · s̄` (`signerRegDev_le_meanShape`) share the mean shape `s̄`. -/
theorem tvDist_realKeptLaw_standinKeptLaw_le_of_keyFloorAt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {cut : Cutoff p} {ε : ℝ}
    (hf : KeyFloorAt prims cut ε sk.t0) (hkeep : SignerKeeps prims sk aHat cut) :
    tvDist (realKeptLaw prims sk aHat cut) (standinKeptLaw prims sk cut) ≤
      signerRegGap prims sk aHat cut / (1 - ε) := by
  rw [← map_flatKeptLaw_one prims sk aHat cut, ← map_standinFlatKeptLaw_one prims sk cut]
  refine (tvDist_map_le _ _ _).trans ((tvDist_flatKeptLaw_standinFlatKeptLaw_le_of_keyFloorOn
    prims sk aHat cut _ hp h_laws hs2 hf.keyFloorOn_one
      ((flatKeeps_one_iff prims sk aHat cut).2 hkeep)).trans ?_)
  rw [keepMass_keep_one]
  have hdev := signerRegDev_le_meanShape prims sk aHat hp hf.cutoff_ne_zero hf.cutoff_ne_top
    (hf.expect_flatWeight_mul_shape_pos hp)
  have hK := flatLevel_pos hp hf.cutoff_ne_zero hf.cutoff_ne_top
  have hV : (0 : ℝ) < Fintype.card (BucketVec p) := Nat.cast_pos.2 Fintype.card_pos
  have hs := cut.meanShape_pos
  have h1 : 0 < 1 - ε := by linarith [hf.lt_one]
  rw [div_le_div_iff₀ (mul_pos hK (mul_pos h1 (mul_pos hV hs))) h1]
  calc signerRegDev prims sk aHat * (1 - ε)
      ≤ signerRegGap prims sk aHat cut *
          ((standinScale p * cut.top).toReal * Fintype.card (BucketVec p) * cut.meanShape) *
            (1 - ε) :=
        mul_le_mul_of_nonneg_right hdev h1.le
    _ = _ := by ring

/-- **The signer keeps under the floor at a cut-off** when its regularity gap is below `1 - ε`
(`flatKeeps_of_signerRegDev_lt` with the keep factor `shape`, `signerRegDev_le_meanShape`). -/
theorem signerKeeps_of_keyFloorAt (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) {cut : Cutoff p} {ε : ℝ}
    (hf : KeyFloorAt prims cut ε sk.t0) (hgap : signerRegGap prims sk aHat cut < 1 - ε) :
    SignerKeeps prims sk aHat cut := by
  rw [← flatKeeps_one_iff]
  refine flatKeeps_of_signerRegDev_lt prims sk aHat cut _ hp h_laws hs2 hf.keyFloorOn_one ?_
  rw [keepMass_keep_one]
  have hdev := signerRegDev_le_meanShape prims sk aHat hp hf.cutoff_ne_zero hf.cutoff_ne_top
    (hf.expect_flatWeight_mul_shape_pos hp)
  have hKV := mul_pos (mul_pos (flatLevel_pos hp hf.cutoff_ne_zero hf.cutoff_ne_top)
    (Nat.cast_pos.2 (Fintype.card_pos (α := BucketVec p)))) cut.meanShape_pos
  have := mul_lt_mul_of_pos_right hgap hKV
  have e : (1 - ε) * ((standinScale p * cut.top).toReal * Fintype.card (BucketVec p) *
      cut.meanShape) = (standinScale p * cut.top).toReal *
        ((1 - ε) * (Fintype.card (BucketVec p) * cut.meanShape)) := by ring
  linarith

/-- **A signer that never keeps has regularity gap at least `1 - ε`** under the floor at a
cut-off (`signerKeeps_of_keyFloorAt`). -/
theorem one_sub_le_signerRegGap_of_keyFloorAt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {cut : Cutoff p} {ε : ℝ}
    (hf : KeyFloorAt prims cut ε sk.t0) (h : ¬ SignerKeeps prims sk aHat cut) :
    1 - ε ≤ signerRegGap prims sk aHat cut :=
  not_lt.1 fun hgap => h (signerKeeps_of_keyFloorAt prims sk aHat hp h_laws hs2 hf hgap)

/-- **The single-key flattened signer at a fixed matrix against the shaped target** (the loop
signer `flatLoopSigner` with a fresh hash per attempt, `realKeptLaw_eq_keptLaw`). For a key with
`‖s₂‖∞ ≤ η` whose `t₀` satisfies the per-key floor at the cut-off with defect bound `ε < 1`, the
law of `(w₁, c̃)` is within `ε + signerRegGap / (1 - ε)` of `shapedTarget`, `signerRegGap` the
signer's regularity gap at the matrix `Â` (`tvDist_standinFlat_shapedTarget_le_of_keyFloorAt`,
`tvDist_realKeptLaw_standinKeptLaw_le_of_keyFloorAt`). If the signer never keeps, the bound is at
least one (`one_sub_le_signerRegGap_of_keyFloorAt`). -/
theorem tvDist_flatSigner_shapedTarget_le_of_keyFloorAt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {cut : Cutoff p} {ε : ℝ}
    (hf : KeyFloorAt prims cut ε sk.t0) :
    tvDist (realKeptLaw prims sk aHat cut) (shapedTarget cut) ≤
      ε + signerRegGap prims sk aHat cut / (1 - ε) := by
  by_cases hkeep : SignerKeeps prims sk aHat cut
  · refine (tvDist_triangle _ (standinKeptLaw prims sk cut) _).trans ?_
    rw [add_comm ε]
    exact add_le_add (tvDist_realKeptLaw_standinKeptLaw_le_of_keyFloorAt prims sk aHat hp h_laws
      hs2 hf hkeep) (tvDist_standinFlat_shapedTarget_le_of_keyFloorAt prims hp h_laws hs2 hf)
  · have hg := one_sub_le_signerRegGap_of_keyFloorAt prims sk aHat hp h_laws hs2 hf hkeep
    have h1 : 0 < 1 - ε := by linarith [hf.lt_one]
    have h2 : 1 ≤ signerRegGap prims sk aHat cut / (1 - ε) := by
      rw [le_div_iff₀ h1]
      linarith
    linarith [tvDist_le_one (realKeptLaw prims sk aHat cut) (shapedTarget cut), hf.nonneg]

/-- **The real and stand-in kept laws under the floor** at the constant cut-off `β_min`
(`tvDist_realKeptLaw_standinKeptLaw_le_of_keyFloorAt`). -/
theorem tvDist_realKeptLaw_standinKeptLaw_le_of_keyFloor (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {βmin : ℚ≥0} {ε : ℝ}
    (hf : KeyFloor prims βmin ε sk.t0) (hkeep : SignerKeeps prims sk aHat (Cutoff.const βmin)) :
    tvDist (realKeptLaw prims sk aHat (Cutoff.const βmin)) (standinKeptLaw prims sk
        (Cutoff.const βmin)) ≤
      signerRegGap prims sk aHat (Cutoff.const βmin) / (1 - ε) :=
  tvDist_realKeptLaw_standinKeptLaw_le_of_keyFloorAt prims sk aHat hp h_laws hs2
    (keyFloorAt_const_iff.2 hf) hkeep

/-- **The single-key flattened signer at a fixed matrix** (the loop signer `flatLoopSigner` with a
fresh hash per attempt, `realKeptLaw_eq_keptLaw`). For a key with `‖s₂‖∞ ≤ η` whose `t₀`
satisfies the per-key floor at `β_min` with defect bound `ε < 1`, the law of `(w₁, c̃)` is within
`ε + signerRegGap / (1 - ε)` of the uniform target, `signerRegGap` the signer's regularity
gap at the matrix `Â` (`tvDist_flatSigner_shapedTarget_le_of_keyFloorAt` at the constant cut-off,
`shapedTarget_const`). -/
theorem tvDist_flatSigner_flatTarget_le_of_keyFloor (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {βmin : ℚ≥0} {ε : ℝ}
    (hf : KeyFloor prims βmin ε sk.t0) :
    tvDist (realKeptLaw prims sk aHat (Cutoff.const βmin)) (flatTarget p) ≤
      ε + signerRegGap prims sk aHat (Cutoff.const βmin) / (1 - ε) := by
  rw [← shapedTarget_const βmin]
  exact tvDist_flatSigner_shapedTarget_le_of_keyFloorAt prims sk aHat hp h_laws hs2
    (keyFloorAt_const_iff.2 hf)

end GordieHowe.MLDSA
