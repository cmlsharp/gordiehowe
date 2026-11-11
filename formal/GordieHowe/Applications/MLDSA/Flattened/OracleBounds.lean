-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.KeepProb
public import GordieHowe.Applications.MLDSA.Flattened.Average
public import GordieHowe.Applications.MLDSA.Regularity.StandinScale

public section

/-!
# The oracle concentration term at ML-DSA-65 and ML-DSA-87

With `K |V| ≥ 1/16` (`one_div_sixteen_le_standinScale_mul_card_mldsa65`, `_mldsa87`) the keep
probability at a cut-off with level `top` is at least
`top · meanShape · (1 - ε - signerRegGap) / 16` (`le_flatKeepProb_of_keyFloorAt`).

* **Full rank** (`flatOracleConcError_le_mldsa65_of_keyFloorAt`, `_mldsa87_of_keyFloorAt`): at a
  matrix whose minor on some `l` rows has rank `l` at every slot, `commitPointMax ≤ deltaGood`
  (`commitPointMax_le_deltaGood`), and the oracle concentration term is at most
  `√(2^-1277 / (top · meanShape · (1 - ε - signerRegGap))) / 2` at ML-DSA-65 and
  `√(2^-1790 / (top · meanShape · (1 - ε - signerRegGap))) / 2` at ML-DSA-87.
* **Averaged over a uniform matrix** (`ExpandA` a random oracle;
  `expect_min_one_mul_flatOracleConcError_le_mldsa65_of_keyFloorAt`, `_mldsa87_of_keyFloorAt`):
  for every `Q` and every set `S` of matrices at which the floor holds,
  `𝔼_Â 1_S(Â) · min(1, Q · flatOracleConcError)` is at most
  `Q · √(2^-1020 / (L (1 - ε))) / 2 + 22 · 2^-199 / ((1 - ε)² L)` at ML-DSA-65 and
  `Q · √(2^-1533 / (L (1 - ε))) / 2 + 24 · 2^-294 / ((1 - ε)² L)` at ML-DSA-87, with
  `L = top · meanShape` (`min_one_mul_flatOracleConcError_le_of_keyFloorAt`, Jensen's inequality
  for `√`, `expect_commitPointMax_le`, and the regularity bounds
  `expect_signerRegGap_le_mldsa65_seven`, `_mldsa87_seven`).

At the constant cut-off `β_min` and `S` every matrix these are the forms without the suffix
`_of_keyFloorAt`, with `L = β_min`.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete Finset PMF GordieHowe.MLDSA.Regularity
open scoped ENNReal BigOperators

section Generic

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {βmin : ℚ≥0}

/-- **The oracle concentration term at a bounded point probability, at a cut-off**: with
`K |V| ≥ 1/16` and `commitPointMax Â ≤ A`, at most
`√(16 A / (top · meanShape · (1 - ε - signerRegGap))) / 2`
(`flatOracleConcError_le_of_keyFloorAt`). -/
theorem flatOracleConcError_le_of_commitPointMax_le_of_keyFloorAt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (hs2 : polyVecBounded sk.s2 p.eta) {cut : Cutoff p} {ε : ℝ}
    (hf : KeyFloorAt prims cut ε sk.t0) (hgap : signerRegGap prims sk aHat cut < 1 - ε)
    (hKV : 1 / 16 ≤ (standinScale p).toReal * Fintype.card (BucketVec p)) {A : ℝ}
    (hA : commitPointMax aHat ≤ A) :
    flatOracleConcError prims sk aHat cut ≤
      √(16 * A / ((cut.top : ℝ≥0∞).toReal * cut.meanShape *
        (1 - ε - signerRegGap prims sk aHat cut))) / 2 := by
  refine (flatOracleConcError_le_of_keyFloorAt prims sk aHat hp h_laws hs2 hf hgap).trans ?_
  refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) zero_le_two
  set β := (cut.top : ℝ≥0∞).toReal
  set m := cut.meanShape
  set d := 1 - ε - signerRegGap prims sk aHat cut
  have hβ : 0 < β := hf.cutoff_pos
  have hm : 0 < m := cut.meanShape_pos
  have hd : 0 < d := sub_pos.2 hgap
  have hβd : 0 < β * m * d := by positivity
  have hCP := commitPointMax_nonneg aHat
  rw [ENNReal.toReal_mul, show 16 * A / (β * m * d) = A / (β * m * d / 16) by field_simp]
  refine div_le_div₀ (hCP.trans hA) hA (by positivity) ?_
  calc β * m * d / 16 = 1 / 16 * (β * m * d) := by ring
    _ ≤ (standinScale p).toReal * Fintype.card (BucketVec p) * (β * m * d) :=
        mul_le_mul_of_nonneg_right hKV hβd.le
    _ = (standinScale p).toReal * β * Fintype.card (BucketVec p) * m * d := by ring

/-- **The oracle concentration term at a bounded point probability**: with `K |V| ≥ 1/16` and
`commitPointMax Â ≤ A`, at most `√(16 A / (β_min (1 - ε - signerRegGap))) / 2`
(`flatOracleConcError_le_of_commitPointMax_le_of_keyFloorAt` at the constant cut-off). -/
theorem flatOracleConcError_le_of_commitPointMax_le (hp : SigningParams p)
    (h_laws : SigningLaws prims) (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ} (hf : KeyFloor prims βmin ε sk.t0)
    (hgap : signerRegGap prims sk aHat (Cutoff.const βmin) < 1 - ε)
    (hKV : 1 / 16 ≤ (standinScale p).toReal * Fintype.card (BucketVec p)) {A : ℝ}
    (hA : commitPointMax aHat ≤ A) :
    flatOracleConcError prims sk aHat (Cutoff.const βmin) ≤
      √(16 * A / ((βmin : ℝ≥0∞).toReal * (1 - ε - signerRegGap prims sk aHat (Cutoff.const βmin))))
          / 2 := by
  have h := flatOracleConcError_le_of_commitPointMax_le_of_keyFloorAt prims hp h_laws sk aHat hs2
    (keyFloorAt_const_iff.2 hf) hgap hKV hA
  rwa [Cutoff.meanShape_const, mul_one] at h

variable [NTTRingLaws nttOps]

/-- **The oracle concentration term averaged over a uniform matrix, at a cut-off**: with
`K |V| ≥ 1/16`, the floor at every matrix of `S`, the average point probability bound at most `A`
and `𝔼_Â 1_S(Â) · signerRegGap ≤ R`, for every `Q`,
`𝔼_Â 1_S(Â) · min(1, Q · flatOracleConcError) ≤
Q · √(32 A / (top · meanShape · (1 - ε))) / 2 + 2 R / (1 - ε)`
(`min_one_mul_flatOracleConcError_le_of_keyFloorAt`, `Real.expect_sqrt_le_sqrt_expect`,
`expect_commitPointMax_le`). -/
theorem expect_min_one_mul_flatOracleConcError_le_of_keyFloorAt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (sk₀ : SecretKey p) (hs2 : polyVecBounded sk₀.s2 p.eta)
    {cut : Cutoff p} {ε : ℝ} (hε1 : ε < 1) (S : Set (TqMatrix p.k p.l))
    (hf : ∀ aHat ∈ S, KeyFloorAt prims cut ε (matrixKey sk₀ aHat).t0)
    (hKV : 1 / 16 ≤ (standinScale p).toReal * Fintype.card (BucketVec p))
    (σ : Fin p.l ↪ Fin p.k) {A R : ℝ} (hA : commitPointAvgBound p ≤ A)
    (hR : 𝔼 aHat : TqMatrix p.k p.l,
        S.indicator (fun aHat => signerRegGap prims (matrixKey sk₀ aHat) aHat cut) aHat ≤ R)
    (Q : ℕ) :
    𝔼 aHat : TqMatrix p.k p.l, S.indicator (fun aHat =>
        min 1 (Q * flatOracleConcError prims (matrixKey sk₀ aHat) aHat cut)) aHat ≤
      Q * √(32 * A / ((cut.top : ℝ≥0∞).toReal * cut.meanShape * (1 - ε))) / 2 +
        2 * R / (1 - ε) := by
  set β := (cut.top : ℝ≥0∞).toReal
  set m := cut.meanShape
  have h1 : 0 < 1 - ε := sub_pos.2 hε1
  have hβ0 : 0 ≤ β := ENNReal.toReal_nonneg
  have hm : 0 < m := cut.meanShape_pos
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hpt : ∀ aHat : TqMatrix p.k p.l, S.indicator (fun aHat =>
      min 1 (Q * flatOracleConcError prims (matrixKey sk₀ aHat) aHat cut)) aHat ≤
        Q / 2 * √(32 / (β * m * (1 - ε)) * commitPointMax aHat) +
          2 / (1 - ε) * S.indicator (fun aHat =>
            signerRegGap prims (matrixKey sk₀ aHat) aHat cut) aHat := fun aHat => by
    by_cases hS : aHat ∈ S
    swap
    · simp only [Set.indicator_of_notMem hS, mul_zero, add_zero]
      positivity
    simp only [Set.indicator_of_mem hS]
    have hβ : 0 < β := (hf aHat hS).cutoff_pos
    have hc : 0 < β * m * (1 - ε) := by positivity
    refine (min_one_mul_flatOracleConcError_le_of_keyFloorAt prims (matrixKey sk₀ aHat) aHat hp
      h_laws (by rw [matrixKey_s2]; exact hs2) (hf aHat hS) Q).trans ?_
    have hCP := commitPointMax_nonneg aHat
    have hsq : √(2 * commitPointMax aHat /
        ((standinScale p * cut.top).toReal * Fintype.card (BucketVec p) * m * (1 - ε))) ≤
        √(32 / (β * m * (1 - ε)) * commitPointMax aHat) := by
      refine Real.sqrt_le_sqrt ?_
      rw [show 32 / (β * m * (1 - ε)) * commitPointMax aHat =
          2 * commitPointMax aHat / (β * m * (1 - ε) / 16) by field_simp; ring]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      rw [ENNReal.toReal_mul]
      calc β * m * (1 - ε) / 16 = 1 / 16 * (β * m * (1 - ε)) := by ring
        _ ≤ (standinScale p).toReal * Fintype.card (BucketVec p) * (β * m * (1 - ε)) :=
            mul_le_mul_of_nonneg_right hKV hc.le
        _ = (standinScale p).toReal * β * Fintype.card (BucketVec p) * m * (1 - ε) := by ring
    calc (Q : ℝ) * √(2 * commitPointMax aHat /
            ((standinScale p * cut.top).toReal * Fintype.card (BucketVec p) * m * (1 - ε))) / 2 +
          2 * signerRegGap prims (matrixKey sk₀ aHat) aHat cut / (1 - ε)
        ≤ Q * √(32 / (β * m * (1 - ε)) * commitPointMax aHat) / 2 +
          2 * signerRegGap prims (matrixKey sk₀ aHat) aHat cut / (1 - ε) := by
              gcongr
      _ = _ := by ring
  have hc0 : 0 ≤ 32 / (β * m * (1 - ε)) := by positivity
  have hJ : 𝔼 aHat : TqMatrix p.k p.l, √(32 / (β * m * (1 - ε)) * commitPointMax aHat) ≤
      √(32 / (β * m * (1 - ε)) * A) := by
    refine (Real.expect_sqrt_le_sqrt_expect _ fun aHat =>
      mul_nonneg hc0 (commitPointMax_nonneg aHat)).trans (Real.sqrt_le_sqrt ?_)
    rw [← Finset.mul_expect]
    exact mul_le_mul_of_nonneg_left ((expect_commitPointMax_le hp σ).trans hA) hc0
  calc 𝔼 aHat : TqMatrix p.k p.l, S.indicator (fun aHat =>
        min 1 (Q * flatOracleConcError prims (matrixKey sk₀ aHat) aHat cut)) aHat
      ≤ 𝔼 aHat : TqMatrix p.k p.l, (Q / 2 * √(32 / (β * m * (1 - ε)) * commitPointMax aHat) +
          2 / (1 - ε) * S.indicator (fun aHat =>
            signerRegGap prims (matrixKey sk₀ aHat) aHat cut) aHat) :=
        expect_le_expect fun aHat _ => hpt aHat
    _ = Q / 2 * 𝔼 aHat : TqMatrix p.k p.l, √(32 / (β * m * (1 - ε)) * commitPointMax aHat) +
          2 / (1 - ε) * 𝔼 aHat : TqMatrix p.k p.l, S.indicator (fun aHat =>
            signerRegGap prims (matrixKey sk₀ aHat) aHat cut) aHat := by
        rw [expect_add_distrib, Finset.mul_expect, Finset.mul_expect]
    _ ≤ Q / 2 * √(32 / (β * m * (1 - ε)) * A) + 2 / (1 - ε) * R := by
        gcongr
    _ = _ := by
        rw [show 32 / (β * m * (1 - ε)) * A = 32 * A / (β * m * (1 - ε)) by ring]
        ring

/-- **The oracle concentration term averaged over a uniform matrix**: with `K |V| ≥ 1/16`, the
average point probability bound at most `A` and the average regularity gap at most `R`, for every
`Q`, `𝔼_Â min(1, Q · flatOracleConcError) ≤ Q · √(32 A / (β_min (1 - ε))) / 2 + 2 R / (1 - ε)`
(`expect_min_one_mul_flatOracleConcError_le_of_keyFloorAt` at the constant cut-off and every
matrix). -/
theorem expect_min_one_mul_flatOracleConcError_le (hp : SigningParams p)
    (h_laws : SigningLaws prims) (sk₀ : SecretKey p) (hs2 : polyVecBounded sk₀.s2 p.eta) {ε : ℝ}
    (hf : ∀ aHat, KeyFloor prims βmin ε (matrixKey sk₀ aHat).t0)
    (hKV : 1 / 16 ≤ (standinScale p).toReal * Fintype.card (BucketVec p))
    (σ : Fin p.l ↪ Fin p.k) {A R : ℝ} (hA : commitPointAvgBound p ≤ A)
    (hR : 𝔼 aHat : TqMatrix p.k p.l, signerRegGap prims (matrixKey sk₀ aHat) aHat
        (Cutoff.const βmin) ≤ R)
    (Q : ℕ) :
    𝔼 aHat : TqMatrix p.k p.l,
        min 1 (Q * flatOracleConcError prims (matrixKey sk₀ aHat) aHat (Cutoff.const βmin)) ≤
      Q * √(32 * A / ((βmin : ℝ≥0∞).toReal * (1 - ε))) / 2 + 2 * R / (1 - ε) := by
  have h := expect_min_one_mul_flatOracleConcError_le_of_keyFloorAt prims hp h_laws sk₀ hs2
    (cut := Cutoff.const βmin) (hf (Classical.arbitrary _)).lt_one Set.univ
    (fun aHat _ => keyFloorAt_const_iff.2 (hf aHat)) hKV σ hA
    (by simpa only [Set.indicator_univ] using hR) Q
  simpa only [Set.indicator_univ, Cutoff.meanShape_const, mul_one] using h

end Generic

attribute [local instance] concreteNTTRingOps

/-- Rows `0, …, l - 1` of the matrix at ML-DSA-65. -/
def firstRows65 : Fin mldsa65.l ↪ Fin mldsa65.k :=
  Fin.castLEEmb (by obtain ⟨hk, hl, -⟩ := mldsa65_vals; omega)

/-- Rows `0, …, l - 1` of the matrix at ML-DSA-87. -/
def firstRows87 : Fin mldsa87.l ↪ Fin mldsa87.k :=
  Fin.castLEEmb (by obtain ⟨hk, hl, -⟩ := mldsa87_vals; omega)

/-- **The oracle concentration term at ML-DSA-65, full rank, at a cut-off**: under the floor at
the cut-off with `signerRegGap < 1 - ε`, at a matrix whose minor on the rows `σ` has rank `l` at
every slot, at most `√(2^-1277 / (top · meanShape · (1 - ε - signerRegGap))) / 2`
(`deltaGood_mldsa65`, `one_div_sixteen_le_standinScale_mul_card_mldsa65`). -/
theorem flatOracleConcError_le_mldsa65_of_keyFloorAt (sk : SecretKey mldsa65)
    (aHat : TqMatrix mldsa65.k mldsa65.l) (hs2 : polyVecBounded sk.s2 mldsa65.eta)
    {cut : Cutoff mldsa65} {ε : ℝ} (hf : KeyFloorAt (concretePrimitives mldsa65) cut ε sk.t0)
    (hgap : signerRegGap (concretePrimitives mldsa65) sk aHat cut < 1 - ε)
    (σ : Fin mldsa65.l ↪ Fin mldsa65.k)
    (hrank : ∀ j, (slotMinor σ (matOfHat aHat) j).rank = mldsa65.l) :
    flatOracleConcError (concretePrimitives mldsa65) sk aHat cut ≤
      √((1 / 2) ^ 1277 / ((cut.top : ℝ≥0∞).toReal * cut.meanShape *
        (1 - ε - signerRegGap (concretePrimitives mldsa65) sk aHat cut))) / 2 := by
  have := concreteNTTRingLaws
  have hp := SigningParams.of_isApproved (p := mldsa65) (Or.inr (Or.inl rfl))
  have h := flatOracleConcError_le_of_commitPointMax_le_of_keyFloorAt (concretePrimitives mldsa65)
    hp (signingLaws_concrete mldsa65 (Or.inr (Or.inl rfl))) sk aHat hs2 hf hgap
    one_div_sixteen_le_standinScale_mul_card_mldsa65
    ((commitPointMax_le_deltaGood hp aHat σ hrank).trans deltaGood_mldsa65)
  rw [show (1281 : ℕ) = 4 + 1277 from rfl, pow_add] at h
  refine h.trans_eq ?_
  generalize (1 / 2 : ℝ) ^ 1277 = X
  rw [show (16 : ℝ) * ((1 / 2) ^ 4 * X) = X by ring]

/-- **The oracle concentration term at ML-DSA-65, full rank**: under the floor with
`signerRegGap < 1 - ε`, at a matrix whose minor on the rows `σ` has rank `l` at every slot, at
most `√(2^-1277 / (β_min (1 - ε - signerRegGap))) / 2`
(`flatOracleConcError_le_mldsa65_of_keyFloorAt` at the constant cut-off). -/
theorem flatOracleConcError_le_mldsa65 (sk : SecretKey mldsa65)
    (aHat : TqMatrix mldsa65.k mldsa65.l) (hs2 : polyVecBounded sk.s2 mldsa65.eta) {βmin : ℚ≥0}
    {ε : ℝ} (hf : KeyFloor (concretePrimitives mldsa65) βmin ε sk.t0)
    (hgap : signerRegGap (concretePrimitives mldsa65) sk aHat (Cutoff.const βmin) < 1 - ε)
    (σ : Fin mldsa65.l ↪ Fin mldsa65.k)
    (hrank : ∀ j, (slotMinor σ (matOfHat aHat) j).rank = mldsa65.l) :
    flatOracleConcError (concretePrimitives mldsa65) sk aHat (Cutoff.const βmin) ≤
      √((1 / 2) ^ 1277 / ((βmin : ℝ≥0∞).toReal *
        (1 - ε - signerRegGap (concretePrimitives mldsa65) sk aHat (Cutoff.const βmin)))) / 2 := by
  have h := flatOracleConcError_le_mldsa65_of_keyFloorAt sk aHat hs2 (keyFloorAt_const_iff.2 hf)
    hgap σ hrank
  rwa [Cutoff.meanShape_const, mul_one] at h

/-- **The oracle concentration term at ML-DSA-65 over a uniform matrix, at a cut-off** (`ExpandA`
a random oracle): for a key `sk₀` with `s₁, s₂` in the `η`-box whose `t₀` satisfies the floor at
the cut-off at every matrix of a set `S`, for every `Q`,
`𝔼_Â 1_S(Â) · min(1, Q · flatOracleConcError) ≤
Q · √(2^-1020 / (L (1 - ε))) / 2 + 22 · 2^-199 / ((1 - ε)² L)` with `L = top · meanShape`
(`commitPointAvgBound_mldsa65`, `expect_signerRegGap_le_mldsa65_seven`). -/
theorem expect_min_one_mul_flatOracleConcError_le_mldsa65_of_keyFloorAt (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {cut : Cutoff mldsa65} {ε : ℝ} (S : Set (TqMatrix mldsa65.k mldsa65.l))
    (hf : ∀ aHat ∈ S, KeyFloorAt (concretePrimitives mldsa65) cut ε (matrixKey sk₀ aHat).t0)
    (Q : ℕ) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l,
        S.indicator (fun aHat => min 1 (Q * flatOracleConcError (concretePrimitives mldsa65)
          (matrixKey sk₀ aHat) aHat cut)) aHat ≤
      Q * √((1 / 2) ^ 1020 / ((cut.top : ℝ≥0∞).toReal * cut.meanShape * (1 - ε))) / 2 +
        22 / 2 ^ 199 / ((1 - ε) ^ 2 * ((cut.top : ℝ≥0∞).toReal * cut.meanShape)) := by
  have hm := cut.meanShape_pos
  rcases S.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp only [Set.indicator_empty, expect_const_zero]
    positivity
  have := concreteNTTRingLaws
  have hp := SigningParams.of_isApproved (p := mldsa65) (Or.inr (Or.inl rfl))
  have hf₀ := hf a₀ ha₀
  have h1 : 0 < 1 - ε := sub_pos.2 hf₀.lt_one
  have hR : 𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, S.indicator (fun aHat =>
      signerRegGap (concretePrimitives mldsa65) (matrixKey sk₀ aHat) aHat cut) aHat ≤
        11 / 2 ^ 199 / ((1 - ε) * cut.meanShape * (cut.top : ℝ≥0∞).toReal) := by
    simp only [matrixKey_eq]
    exact expect_signerRegGap_le_mldsa65_seven sk₀ hs1 hs2 hf₀.cutoff_ne_zero hf₀.cutoff_ne_top
      (mul_pos h1 hm) S fun aHat h v => by
        simpa only [matrixKey_eq] using (hf aHat h).one_sub_mul_le_expect_flatWeight hp v
  have h := expect_min_one_mul_flatOracleConcError_le_of_keyFloorAt (concretePrimitives mldsa65) hp
    (signingLaws_concrete mldsa65 (Or.inr (Or.inl rfl))) sk₀ hs2 hf₀.lt_one S hf
    one_div_sixteen_le_standinScale_mul_card_mldsa65 firstRows65 commitPointAvgBound_mldsa65 hR Q
  rw [show (1025 : ℕ) = 5 + 1020 from rfl, pow_add] at h
  refine h.trans_eq ?_
  have hβ : 0 < (cut.top : ℝ≥0∞).toReal := hf₀.cutoff_pos
  generalize (1 / 2 : ℝ) ^ 1020 = X
  rw [show (32 : ℝ) * ((1 / 2) ^ 5 * X) = X by ring]
  congr 1
  field_simp
  ring

/-- **The oracle concentration term at ML-DSA-65 over a uniform matrix** (`ExpandA` a random
oracle): for a key `sk₀` with `s₁, s₂` in the `η`-box whose `t₀` at every matrix satisfies the
floor, for every `Q`, `𝔼_Â min(1, Q · flatOracleConcError) ≤
Q · √(2^-1020 / (β_min (1 - ε))) / 2 + 22 · 2^-199 / ((1 - ε)² β_min)`
(`expect_min_one_mul_flatOracleConcError_le_mldsa65_of_keyFloorAt` at the constant cut-off and
every matrix). -/
theorem expect_min_one_mul_flatOracleConcError_le_mldsa65 (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    {βmin : ℚ≥0} {ε : ℝ}
    (hf : ∀ aHat, KeyFloor (concretePrimitives mldsa65) βmin ε (matrixKey sk₀ aHat).t0) (Q : ℕ) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l,
        min 1 (Q * flatOracleConcError (concretePrimitives mldsa65) (matrixKey sk₀ aHat) aHat
          (Cutoff.const βmin)) ≤
      Q * √((1 / 2) ^ 1020 / ((βmin : ℝ≥0∞).toReal * (1 - ε))) / 2 +
        22 / 2 ^ 199 / ((1 - ε) ^ 2 * (βmin : ℝ≥0∞).toReal) := by
  have h := expect_min_one_mul_flatOracleConcError_le_mldsa65_of_keyFloorAt sk₀ hs1 hs2
    (cut := Cutoff.const βmin) Set.univ (fun aHat _ => keyFloorAt_const_iff.2 (hf aHat)) Q
  simpa only [Set.indicator_univ, Cutoff.meanShape_const, mul_one] using h

/-- **The oracle concentration term at ML-DSA-87, full rank, at a cut-off**: as
`flatOracleConcError_le_mldsa65_of_keyFloorAt`, at most
`√(2^-1790 / (top · meanShape · (1 - ε - signerRegGap))) / 2` (`deltaGood_mldsa87`). -/
theorem flatOracleConcError_le_mldsa87_of_keyFloorAt (sk : SecretKey mldsa87)
    (aHat : TqMatrix mldsa87.k mldsa87.l) (hs2 : polyVecBounded sk.s2 mldsa87.eta)
    {cut : Cutoff mldsa87} {ε : ℝ} (hf : KeyFloorAt (concretePrimitives mldsa87) cut ε sk.t0)
    (hgap : signerRegGap (concretePrimitives mldsa87) sk aHat cut < 1 - ε)
    (σ : Fin mldsa87.l ↪ Fin mldsa87.k)
    (hrank : ∀ j, (slotMinor σ (matOfHat aHat) j).rank = mldsa87.l) :
    flatOracleConcError (concretePrimitives mldsa87) sk aHat cut ≤
      √((1 / 2) ^ 1790 / ((cut.top : ℝ≥0∞).toReal * cut.meanShape *
        (1 - ε - signerRegGap (concretePrimitives mldsa87) sk aHat cut))) / 2 := by
  have := concreteNTTRingLaws
  have hp := SigningParams.of_isApproved (p := mldsa87) (Or.inr (Or.inr rfl))
  have h := flatOracleConcError_le_of_commitPointMax_le_of_keyFloorAt (concretePrimitives mldsa87)
    hp (signingLaws_concrete mldsa87 (Or.inr (Or.inr rfl))) sk aHat hs2 hf hgap
    one_div_sixteen_le_standinScale_mul_card_mldsa87
    ((commitPointMax_le_deltaGood hp aHat σ hrank).trans deltaGood_mldsa87)
  rw [show (1794 : ℕ) = 4 + 1790 from rfl, pow_add] at h
  refine h.trans_eq ?_
  generalize (1 / 2 : ℝ) ^ 1790 = X
  rw [show (16 : ℝ) * ((1 / 2) ^ 4 * X) = X by ring]

/-- **The oracle concentration term at ML-DSA-87, full rank**: as
`flatOracleConcError_le_mldsa65`, at most `√(2^-1790 / (β_min (1 - ε - signerRegGap))) / 2`
(`flatOracleConcError_le_mldsa87_of_keyFloorAt`). -/
theorem flatOracleConcError_le_mldsa87 (sk : SecretKey mldsa87)
    (aHat : TqMatrix mldsa87.k mldsa87.l) (hs2 : polyVecBounded sk.s2 mldsa87.eta) {βmin : ℚ≥0}
    {ε : ℝ} (hf : KeyFloor (concretePrimitives mldsa87) βmin ε sk.t0)
    (hgap : signerRegGap (concretePrimitives mldsa87) sk aHat (Cutoff.const βmin) < 1 - ε)
    (σ : Fin mldsa87.l ↪ Fin mldsa87.k)
    (hrank : ∀ j, (slotMinor σ (matOfHat aHat) j).rank = mldsa87.l) :
    flatOracleConcError (concretePrimitives mldsa87) sk aHat (Cutoff.const βmin) ≤
      √((1 / 2) ^ 1790 / ((βmin : ℝ≥0∞).toReal *
        (1 - ε - signerRegGap (concretePrimitives mldsa87) sk aHat (Cutoff.const βmin)))) / 2 := by
  have h := flatOracleConcError_le_mldsa87_of_keyFloorAt sk aHat hs2 (keyFloorAt_const_iff.2 hf)
    hgap σ hrank
  rwa [Cutoff.meanShape_const, mul_one] at h

/-- **The oracle concentration term at ML-DSA-87 over a uniform matrix, at a cut-off**: as
`expect_min_one_mul_flatOracleConcError_le_mldsa65_of_keyFloorAt`, at most
`Q · √(2^-1533 / (L (1 - ε))) / 2 + 24 · 2^-294 / ((1 - ε)² L)` with `L = top · meanShape`
(`commitPointAvgBound_mldsa87`, `expect_signerRegGap_le_mldsa87_seven`). -/
theorem expect_min_one_mul_flatOracleConcError_le_mldsa87_of_keyFloorAt (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {cut : Cutoff mldsa87} {ε : ℝ} (S : Set (TqMatrix mldsa87.k mldsa87.l))
    (hf : ∀ aHat ∈ S, KeyFloorAt (concretePrimitives mldsa87) cut ε (matrixKey sk₀ aHat).t0)
    (Q : ℕ) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l,
        S.indicator (fun aHat => min 1 (Q * flatOracleConcError (concretePrimitives mldsa87)
          (matrixKey sk₀ aHat) aHat cut)) aHat ≤
      Q * √((1 / 2) ^ 1533 / ((cut.top : ℝ≥0∞).toReal * cut.meanShape * (1 - ε))) / 2 +
        24 / 2 ^ 294 / ((1 - ε) ^ 2 * ((cut.top : ℝ≥0∞).toReal * cut.meanShape)) := by
  have hm := cut.meanShape_pos
  rcases S.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp only [Set.indicator_empty, expect_const_zero]
    positivity
  have := concreteNTTRingLaws
  have hp := SigningParams.of_isApproved (p := mldsa87) (Or.inr (Or.inr rfl))
  have hf₀ := hf a₀ ha₀
  have h1 : 0 < 1 - ε := sub_pos.2 hf₀.lt_one
  have hR : 𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, S.indicator (fun aHat =>
      signerRegGap (concretePrimitives mldsa87) (matrixKey sk₀ aHat) aHat cut) aHat ≤
        12 / 2 ^ 294 / ((1 - ε) * cut.meanShape * (cut.top : ℝ≥0∞).toReal) := by
    simp only [matrixKey_eq]
    exact expect_signerRegGap_le_mldsa87_seven sk₀ hs1 hs2 hf₀.cutoff_ne_zero hf₀.cutoff_ne_top
      (mul_pos h1 hm) S fun aHat h v => by
        simpa only [matrixKey_eq] using (hf aHat h).one_sub_mul_le_expect_flatWeight hp v
  have h := expect_min_one_mul_flatOracleConcError_le_of_keyFloorAt (concretePrimitives mldsa87) hp
    (signingLaws_concrete mldsa87 (Or.inr (Or.inr rfl))) sk₀ hs2 hf₀.lt_one S hf
    one_div_sixteen_le_standinScale_mul_card_mldsa87 firstRows87 commitPointAvgBound_mldsa87 hR Q
  rw [show (1538 : ℕ) = 5 + 1533 from rfl, pow_add] at h
  refine h.trans_eq ?_
  have hβ : 0 < (cut.top : ℝ≥0∞).toReal := hf₀.cutoff_pos
  generalize (1 / 2 : ℝ) ^ 1533 = X
  rw [show (32 : ℝ) * ((1 / 2) ^ 5 * X) = X by ring]
  congr 1
  field_simp
  ring

/-- **The oracle concentration term at ML-DSA-87 over a uniform matrix**: as
`expect_min_one_mul_flatOracleConcError_le_mldsa65`, at most
`Q · √(2^-1533 / (β_min (1 - ε))) / 2 + 24 · 2^-294 / ((1 - ε)² β_min)`
(`expect_min_one_mul_flatOracleConcError_le_mldsa87_of_keyFloorAt`). -/
theorem expect_min_one_mul_flatOracleConcError_le_mldsa87 (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    {βmin : ℚ≥0} {ε : ℝ}
    (hf : ∀ aHat, KeyFloor (concretePrimitives mldsa87) βmin ε (matrixKey sk₀ aHat).t0) (Q : ℕ) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l,
        min 1 (Q * flatOracleConcError (concretePrimitives mldsa87) (matrixKey sk₀ aHat) aHat
          (Cutoff.const βmin)) ≤
      Q * √((1 / 2) ^ 1533 / ((βmin : ℝ≥0∞).toReal * (1 - ε))) / 2 +
        24 / 2 ^ 294 / ((1 - ε) ^ 2 * (βmin : ℝ≥0∞).toReal) := by
  have h := expect_min_one_mul_flatOracleConcError_le_mldsa87_of_keyFloorAt sk₀ hs1 hs2
    (cut := Cutoff.const βmin) Set.univ (fun aHat _ => keyFloorAt_const_iff.2 (hf aHat)) Q
  simpa only [Set.indicator_univ, Cutoff.meanShape_const, mul_one] using h

end GordieHowe.MLDSA
