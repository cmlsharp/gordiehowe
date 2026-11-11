-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.PresentationBound
public import GordieHowe.Applications.MLDSA.Flattened.OracleBounds

public section

/-!
# The presentations of the flattened signer over a uniform matrix

With `ExpandA` a random oracle the matrix `Â` is uniform, and the key's `t₀` is recomputed from
`A s₁ + s₂` (`matrixKey`). At a cut-off with level `top`, with the simulator `flatPresentSimOf f`
for a sampler `f` within `δ` of the shaped target, the presentation bound
`presentations_advantage_le_of_keyFloorAt` holds at every matrix of a set `S` at which the floor
holds, and an advantage is at most one (`Adversary.advantage_le_one`), so on average over `Â`
the advantage counted on `S` is at most the average of `min(1, Q · flatOracleConcError)`
(`expect_min_one_mul_flatOracleConcError_le_mldsa65_of_keyFloorAt`, `_mldsa87_of_keyFloorAt`)
plus `Q ε`, `Q` times the average regularity term, `Q δ` and the salt terms
(`expect_advantage_honestPresenter_le_of_keyFloorAt`). With `L = top · meanShape`:

* `expect_advantage_honestPresenter_le_mldsa65_of_keyFloorAt`: at ML-DSA-65 with `R` of 32 bytes,
  at most `Q √(2^-1020 / (L (1 - ε))) / 2 + Q ε + (11 Q + 22) · 2^-199 / ((1 - ε)² L) + Q δ
  + (2 Q t + Q (Q - 1) / 2) / 2^256 + (Q t + Q (Q - 1) / 2) / 2^512`;
* `expect_advantage_honestPresenter_le_mldsa87_of_keyFloorAt`: at ML-DSA-87, the same with
  `2^-1533` and `(12 Q + 24) · 2^-294`.

The adversary and the hash `tr` of the public key may depend on the matrix. The floor is assumed
only at the matrices of `S`, since `t₀` depends on `Â`. At the constant cut-off `β_min`, the
identity sampler (`δ = 0`, the simulator `flatPresentSim`) and `S` every matrix these are the
forms without the suffix `_of_keyFloorAt`, with `L = β_min`.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete Finset PMF GordieHowe.MLDSA.Regularity GordieHowe.ROM.NIZK
open scoped ENNReal BigOperators

/-- `min(1, a + b) ≤ min(1, a) + b` for `b ≥ 0`. -/
theorem min_one_add_le {a b : ℝ} (hb : 0 ≤ b) : min 1 (a + b) ≤ min 1 a + b := by
  rcases le_total a 1 with h | h
  · rw [min_eq_right h]; exact min_le_right _ _
  · rw [min_eq_left h]; exact (min_le_left _ _).trans (by linarith)

/-- `Q (Q - 1) ≥ 0` for a natural number `Q`. -/
theorem natCast_mul_sub_one_nonneg (Q : ℕ) : (0 : ℝ) ≤ Q * (Q - 1) := by
  rcases Nat.eq_zero_or_pos Q with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ Q := Nat.one_le_cast.2 h
    nlinarith

section Generic

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {Rnd Ctx : Type} [Fintype Rnd] [Nonempty Rnd] [DecidableEq Rnd]
  [Fintype Ctx] [DecidableEq Ctx]

/-- **The presentations averaged over a uniform matrix, at a cut-off**: with the floor at every
matrix of `S`, the simulator `flatPresentSimOf f` for a sampler within `δ` of the shaped target,
`𝔼_Â 1_S(Â) · min(1, Q · flatOracleConcError) ≤ X` and `𝔼_Â 1_S(Â) · signerRegGap ≤ R`, the
average advantage counted on `S` is at most
`X + Q ε + Q R / (1 - ε) + Q δ + (2 Q t + Q (Q - 1) / 2) / |Rnd| + (Q t + Q (Q - 1) / 2) / 2^512`
(`presentations_advantage_le_of_keyFloorAt`, `Adversary.advantage_le_one`, `min_one_add_le`). -/
theorem expect_advantage_honestPresenter_le_of_keyFloorAt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (sk₀ : SecretKey p) (hs2 : polyVecBounded sk₀.s2 p.eta)
    {cut : Cutoff p} {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (S : Set (TqMatrix p.k p.l))
    (hf : ∀ aHat ∈ S, KeyFloorAt prims cut ε (matrixKey sk₀ aHat).t0)
    {C : Type} [Fintype C] [Nonempty C] (f : C → BucketVec p × CommitHashBytes p) {δ : ℝ}
    (hδ : tvDist ((uniformOfFintype C).map f) (shapedTarget cut) ≤ δ)
    (trOf : TqMatrix p.k p.l → _root_.MLDSA.Bytes 64) {m t Q : ℕ}
    (𝒜 : TqMatrix p.k p.l → Adversary (PresIn p Rnd Ctx) (PresOut p) Ctx Unit
      (Option (Presentation p)) m t)
    (hpost : ∀ aHat r, ((𝒜 aHat).alg r).PostOracleFree) {X R : ℝ}
    (hX : 𝔼 aHat : TqMatrix p.k p.l, S.indicator (fun aHat =>
      min 1 (Q * flatOracleConcError prims (matrixKey sk₀ aHat) aHat cut)) aHat ≤ X)
    (hR : 𝔼 aHat : TqMatrix p.k p.l,
        S.indicator (fun aHat => signerRegGap prims (matrixKey sk₀ aHat) aHat cut) aHat ≤ R) :
    𝔼 aHat : TqMatrix p.k p.l, S.indicator (fun aHat => (𝒜 aHat).advantage (fun _ _ => True)
        (honestPresenter (trOf aHat)) (honestPresenterLaw prims (matrixKey sk₀ aHat) aHat cut)
        (flatPresentSimOf f) Q) aHat ≤
      X + Q * ε + Q * R / (1 - ε) + Q * δ +
        ((2 * Q * t + Q * (Q - 1) / 2) / Fintype.card Rnd +
          (Q * t + Q * (Q - 1) / 2) / 2 ^ 512) := by
  have h1 : 0 < 1 - ε := sub_pos.2 hε1
  have hδ0 : 0 ≤ δ := (tvDist_nonneg _ _).trans hδ
  set E : ℝ :=
    (2 * Q * t + Q * (Q - 1) / 2) / Fintype.card Rnd + (Q * t + Q * (Q - 1) / 2) / 2 ^ 512
  have hQQ := natCast_mul_sub_one_nonneg Q
  have hE : 0 ≤ E := by positivity
  have hpt : ∀ aHat : TqMatrix p.k p.l, S.indicator (fun aHat => (𝒜 aHat).advantage
      (fun _ _ => True) (honestPresenter (trOf aHat))
        (honestPresenterLaw prims (matrixKey sk₀ aHat) aHat cut) (flatPresentSimOf f) Q) aHat ≤
      S.indicator (fun aHat =>
          min 1 (Q * flatOracleConcError prims (matrixKey sk₀ aHat) aHat cut)) aHat +
        (Q * ε + Q / (1 - ε) * S.indicator (fun aHat =>
          signerRegGap prims (matrixKey sk₀ aHat) aHat cut) aHat + Q * δ + E) := by
    intro aHat
    by_cases hS : aHat ∈ S
    swap
    · simp only [Set.indicator_of_notMem hS, mul_zero, add_zero, zero_add]
      positivity
    simp only [Set.indicator_of_mem hS]
    have hb := presentations_advantage_le_of_keyFloorAt (trOf aHat) prims (matrixKey sk₀ aHat)
      aHat cut hp h_laws (by rw [matrixKey_s2]; exact hs2) (hf aHat hS) f hδ (Q := Q) (𝒜 aHat)
      (hpost aHat)
    have hle := (𝒜 aHat).advantage_le_one (fun _ _ => True) (honestPresenter (trOf aHat))
      (honestPresenterLaw prims (matrixKey sk₀ aHat) aHat cut) (flatPresentSimOf f) (Q := Q)
    have hg := signerRegGap_nonneg prims (matrixKey sk₀ aHat) aHat cut
    have hb0 : 0 ≤ (Q : ℝ) * ε + Q / (1 - ε) * signerRegGap prims (matrixKey sk₀ aHat) aHat cut +
        Q * δ + E := by
      positivity
    refine (le_min hle (hb.trans_eq ?_)).trans (min_one_add_le hb0)
    rw [show (Q : ℝ) / (1 - ε) * signerRegGap prims (matrixKey sk₀ aHat) aHat cut =
      Q * (signerRegGap prims (matrixKey sk₀ aHat) aHat cut / (1 - ε)) by ring]
    simp only [E]
    generalize (2 : ℝ) ^ 512 = D
    ring
  clear_value E
  calc 𝔼 aHat : TqMatrix p.k p.l, S.indicator (fun aHat => (𝒜 aHat).advantage (fun _ _ => True)
        (honestPresenter (trOf aHat)) (honestPresenterLaw prims (matrixKey sk₀ aHat) aHat cut)
        (flatPresentSimOf f) Q) aHat
      ≤ 𝔼 aHat : TqMatrix p.k p.l, (S.indicator (fun aHat =>
          min 1 (Q * flatOracleConcError prims (matrixKey sk₀ aHat) aHat cut)) aHat +
        (Q * ε + Q / (1 - ε) * S.indicator (fun aHat =>
          signerRegGap prims (matrixKey sk₀ aHat) aHat cut) aHat + Q * δ + E)) :=
        expect_le_expect fun aHat _ => hpt aHat
    _ = 𝔼 aHat : TqMatrix p.k p.l, S.indicator (fun aHat =>
          min 1 (Q * flatOracleConcError prims (matrixKey sk₀ aHat) aHat cut)) aHat +
        (Q * ε + Q / (1 - ε) * 𝔼 aHat : TqMatrix p.k p.l, S.indicator (fun aHat =>
          signerRegGap prims (matrixKey sk₀ aHat) aHat cut) aHat + Q * δ + E) := by
        simp only [expect_add_distrib, expect_const univ_nonempty, Finset.mul_expect]
    _ ≤ X + (Q * ε + Q / (1 - ε) * R + Q * δ + E) := by gcongr
    _ = _ := by ring

/-- **The presentations averaged over a uniform matrix**: if `𝔼_Â min(1, Q · flatOracleConcError)
≤ X` and `𝔼_Â signerRegGap ≤ R`, then the average advantage is at most
`X + Q ε + Q R / (1 - ε) + (2 Q t + Q (Q - 1) / 2) / |Rnd| + (Q t + Q (Q - 1) / 2) / 2^512`
(`expect_advantage_honestPresenter_le_of_keyFloorAt` at the constant cut-off, the identity sampler
and every matrix). -/
theorem expect_advantage_honestPresenter_le (hp : SigningParams p) (h_laws : SigningLaws prims)
    (sk₀ : SecretKey p) (hs2 : polyVecBounded sk₀.s2 p.eta) {βmin : ℚ≥0} {ε : ℝ}
    (hf : ∀ aHat, KeyFloor prims βmin ε (matrixKey sk₀ aHat).t0)
    (trOf : TqMatrix p.k p.l → _root_.MLDSA.Bytes 64) {m t Q : ℕ}
    (𝒜 : TqMatrix p.k p.l → Adversary (PresIn p Rnd Ctx) (PresOut p) Ctx Unit
      (Option (Presentation p)) m t)
    (hpost : ∀ aHat r, ((𝒜 aHat).alg r).PostOracleFree) {X R : ℝ}
    (hX : 𝔼 aHat : TqMatrix p.k p.l,
      min 1 (Q * flatOracleConcError prims (matrixKey sk₀ aHat) aHat (Cutoff.const βmin)) ≤ X)
    (hR : 𝔼 aHat : TqMatrix p.k p.l, signerRegGap prims (matrixKey sk₀ aHat) aHat
        (Cutoff.const βmin) ≤ R) :
    𝔼 aHat : TqMatrix p.k p.l, (𝒜 aHat).advantage (fun _ _ => True)
        (honestPresenter (trOf aHat))
        (honestPresenterLaw prims (matrixKey sk₀ aHat) aHat (Cutoff.const βmin))
        flatPresentSim Q ≤
      X + Q * ε + Q * R / (1 - ε) +
        ((2 * Q * t + Q * (Q - 1) / 2) / Fintype.card Rnd + (Q * t + Q * (Q - 1) / 2) / 2 ^ 512) := by
  have hf₀ := hf (Classical.arbitrary _)
  have h := expect_advantage_honestPresenter_le_of_keyFloorAt prims hp h_laws sk₀ hs2
    (cut := Cutoff.const βmin) hf₀.nonneg hf₀.lt_one Set.univ
    (fun aHat _ => keyFloorAt_const_iff.2 (hf aHat)) id (tvDist_map_id_shapedTarget_const βmin)
    trOf 𝒜 hpost (by simpa only [Set.indicator_univ] using hX)
    (by simpa only [Set.indicator_univ] using hR)
  rw [flatPresentSim_eq_flatPresentSimOf]
  simpa only [Set.indicator_univ, mul_zero, add_zero] using h

end Generic

attribute [local instance] concreteNTTRingOps

/-- `Bytes 32` has `2^256` values (`GordieHowe.Lattice.card_bytes`). -/
theorem card_bytes32_eq : (Fintype.card (_root_.MLDSA.Bytes 32) : ℝ) = 2 ^ 256 := by
  rw [GordieHowe.Lattice.card_bytes, Nat.cast_pow, show ((256 : ℕ) : ℝ) = 2 ^ 8 by norm_num,
    ← pow_mul]

/-- **The presentations at ML-DSA-65 over a uniform matrix, at a cut-off** (`ExpandA` a random
oracle, `R` of 32 bytes). For a key `sk₀` with `s₁, s₂` in the `η`-box whose `t₀` satisfies the
floor at the cut-off with defect bound `ε ≥ 0` at every matrix of a set `S`, and the simulator
`flatPresentSimOf f` for a sampler `f` within `δ` of the shaped target, every family of
adversaries with a budget of `t` queries whose outputs do not read the final oracle, with `Q`
presentations answered, has average advantage counted on `S` at most
`Q √(2^-1020 / (L (1 - ε))) / 2 + Q ε + (11 Q + 22) · 2^-199 / ((1 - ε)² L) + Q δ
+ (2 Q t + Q (Q - 1) / 2) / 2^256 + (Q t + Q (Q - 1) / 2) / 2^512` with `L = top · meanShape`
(`expect_advantage_honestPresenter_le_of_keyFloorAt`,
`expect_min_one_mul_flatOracleConcError_le_mldsa65_of_keyFloorAt`,
`expect_signerRegGap_le_mldsa65_seven`). -/
theorem expect_advantage_honestPresenter_le_mldsa65_of_keyFloorAt {Ctx : Type} [Fintype Ctx]
    [DecidableEq Ctx] (sk₀ : SecretKey mldsa65) (hs1 : polyVecBounded sk₀.s1 mldsa65.eta)
    (hs2 : polyVecBounded sk₀.s2 mldsa65.eta) {cut : Cutoff mldsa65} {ε : ℝ} (hε : 0 ≤ ε)
    (S : Set (TqMatrix mldsa65.k mldsa65.l))
    (hf : ∀ aHat ∈ S, KeyFloorAt (concretePrimitives mldsa65) cut ε (matrixKey sk₀ aHat).t0)
    {C : Type} [Fintype C] [Nonempty C] (f : C → BucketVec mldsa65 × CommitHashBytes mldsa65)
    {δ : ℝ}
    (hδ : tvDist ((uniformOfFintype C).map f) (shapedTarget cut) ≤ δ)
    (trOf : TqMatrix mldsa65.k mldsa65.l → _root_.MLDSA.Bytes 64) {m t Q : ℕ}
    (𝒜 : TqMatrix mldsa65.k mldsa65.l → Adversary (PresIn mldsa65 (_root_.MLDSA.Bytes 32) Ctx)
      (PresOut mldsa65) Ctx Unit (Option (Presentation mldsa65)) m t)
    (hpost : ∀ aHat r, ((𝒜 aHat).alg r).PostOracleFree) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, S.indicator (fun aHat => (𝒜 aHat).advantage
        (fun _ _ => True) (honestPresenter (trOf aHat))
        (honestPresenterLaw (concretePrimitives mldsa65) (matrixKey sk₀ aHat) aHat cut)
        (flatPresentSimOf f) Q) aHat ≤
      Q * √((1 / 2) ^ 1020 / ((cut.top : ℝ≥0∞).toReal * cut.meanShape * (1 - ε))) / 2 + Q * ε +
        (11 * Q + 22) / 2 ^ 199 / ((1 - ε) ^ 2 * ((cut.top : ℝ≥0∞).toReal * cut.meanShape)) +
        Q * δ +
        ((2 * Q * t + Q * (Q - 1) / 2) / 2 ^ 256 + (Q * t + Q * (Q - 1) / 2) / 2 ^ 512) := by
  have hm := cut.meanShape_pos
  have hδ0 : 0 ≤ δ := (tvDist_nonneg _ _).trans hδ
  have hQQ := natCast_mul_sub_one_nonneg Q
  rcases S.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp only [Set.indicator_empty, expect_const_zero]
    positivity
  have := concreteNTTRingLaws
  have hp := SigningParams.of_isApproved (p := mldsa65) (Or.inr (Or.inl rfl))
  have hf₀ := hf a₀ ha₀
  have h1 : 0 < 1 - ε := sub_pos.2 hf₀.lt_one
  have hβ : 0 < (cut.top : ℝ≥0∞).toReal := hf₀.cutoff_pos
  have hR : 𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, S.indicator (fun aHat =>
      signerRegGap (concretePrimitives mldsa65) (matrixKey sk₀ aHat) aHat cut) aHat ≤
        11 / 2 ^ 199 / ((1 - ε) * cut.meanShape * (cut.top : ℝ≥0∞).toReal) := by
    simp only [matrixKey_eq]
    exact expect_signerRegGap_le_mldsa65_seven sk₀ hs1 hs2 hf₀.cutoff_ne_zero hf₀.cutoff_ne_top
      (mul_pos h1 hm) S fun aHat h v => by
        simpa only [matrixKey_eq] using (hf aHat h).one_sub_mul_le_expect_flatWeight hp v
  have h := expect_advantage_honestPresenter_le_of_keyFloorAt (concretePrimitives mldsa65) hp
    (signingLaws_concrete mldsa65 (Or.inr (Or.inl rfl))) sk₀ hs2 hε hf₀.lt_one S hf f hδ trOf 𝒜
    hpost (expect_min_one_mul_flatOracleConcError_le_mldsa65_of_keyFloorAt sk₀ hs1 hs2 S hf Q) hR
  rw [card_bytes32_eq] at h
  refine h.trans_eq ?_
  generalize √((1 / 2 : ℝ) ^ 1020 / ((cut.top : ℝ≥0∞).toReal * cut.meanShape * (1 - ε))) = Sq
  have hA : (2 : ℝ) ^ 199 ≠ 0 := by positivity
  have h1' := h1.ne'
  have hβ' := hβ.ne'
  have hm' := hm.ne'
  generalize (2 : ℝ) ^ 199 = A at hA ⊢
  generalize (2 : ℝ) ^ 256 = B
  generalize (2 : ℝ) ^ 512 = D
  field_simp
  ring

/-- **The presentations at ML-DSA-65 over a uniform matrix** (`ExpandA` a random oracle, `R` of 32
bytes). For a key `sk₀` with `s₁, s₂` in the `η`-box whose `t₀` at every matrix satisfies the
floor, every family of adversaries with a budget of `t` queries whose outputs do not read the
final oracle, with `Q` presentations answered, has average advantage at most
`Q √(2^-1020 / (β_min (1 - ε))) / 2 + Q ε + (11 Q + 22) · 2^-199 / ((1 - ε)² β_min)
+ (2 Q t + Q (Q - 1) / 2) / 2^256 + (Q t + Q (Q - 1) / 2) / 2^512`
(`expect_advantage_honestPresenter_le_mldsa65_of_keyFloorAt` at the constant cut-off, the
identity sampler and every matrix). -/
theorem expect_advantage_honestPresenter_le_mldsa65 {Ctx : Type} [Fintype Ctx] [DecidableEq Ctx]
    (sk₀ : SecretKey mldsa65) (hs1 : polyVecBounded sk₀.s1 mldsa65.eta)
    (hs2 : polyVecBounded sk₀.s2 mldsa65.eta) {βmin : ℚ≥0} {ε : ℝ}
    (hf : ∀ aHat, KeyFloor (concretePrimitives mldsa65) βmin ε (matrixKey sk₀ aHat).t0)
    (trOf : TqMatrix mldsa65.k mldsa65.l → _root_.MLDSA.Bytes 64) {m t Q : ℕ}
    (𝒜 : TqMatrix mldsa65.k mldsa65.l → Adversary (PresIn mldsa65 (_root_.MLDSA.Bytes 32) Ctx)
      (PresOut mldsa65) Ctx Unit (Option (Presentation mldsa65)) m t)
    (hpost : ∀ aHat r, ((𝒜 aHat).alg r).PostOracleFree) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, (𝒜 aHat).advantage (fun _ _ => True)
        (honestPresenter (trOf aHat))
        (honestPresenterLaw (concretePrimitives mldsa65) (matrixKey sk₀ aHat) aHat
          (Cutoff.const βmin))
        flatPresentSim Q ≤
      Q * √((1 / 2) ^ 1020 / ((βmin : ℝ≥0∞).toReal * (1 - ε))) / 2 + Q * ε +
        (11 * Q + 22) / 2 ^ 199 / ((1 - ε) ^ 2 * (βmin : ℝ≥0∞).toReal) +
        ((2 * Q * t + Q * (Q - 1) / 2) / 2 ^ 256 + (Q * t + Q * (Q - 1) / 2) / 2 ^ 512) := by
  have h := expect_advantage_honestPresenter_le_mldsa65_of_keyFloorAt sk₀ hs1 hs2
    (cut := Cutoff.const βmin) (hf (Classical.arbitrary _)).nonneg Set.univ
    (fun aHat _ => keyFloorAt_const_iff.2 (hf aHat)) id (tvDist_map_id_shapedTarget_const βmin)
    trOf (Q := Q) 𝒜 hpost
  rw [flatPresentSim_eq_flatPresentSimOf]
  simpa only [Set.indicator_univ, Cutoff.meanShape_const, mul_one, mul_zero, add_zero] using h

/-- **The presentations at ML-DSA-87 over a uniform matrix, at a cut-off**: as
`expect_advantage_honestPresenter_le_mldsa65_of_keyFloorAt`, at most
`Q √(2^-1533 / (L (1 - ε))) / 2 + Q ε + (12 Q + 24) · 2^-294 / ((1 - ε)² L) + Q δ
+ (2 Q t + Q (Q - 1) / 2) / 2^256 + (Q t + Q (Q - 1) / 2) / 2^512` with `L = top · meanShape`
(`expect_min_one_mul_flatOracleConcError_le_mldsa87_of_keyFloorAt`,
`expect_signerRegGap_le_mldsa87_seven`). -/
theorem expect_advantage_honestPresenter_le_mldsa87_of_keyFloorAt {Ctx : Type} [Fintype Ctx]
    [DecidableEq Ctx] (sk₀ : SecretKey mldsa87) (hs1 : polyVecBounded sk₀.s1 mldsa87.eta)
    (hs2 : polyVecBounded sk₀.s2 mldsa87.eta) {cut : Cutoff mldsa87} {ε : ℝ} (hε : 0 ≤ ε)
    (S : Set (TqMatrix mldsa87.k mldsa87.l))
    (hf : ∀ aHat ∈ S, KeyFloorAt (concretePrimitives mldsa87) cut ε (matrixKey sk₀ aHat).t0)
    {C : Type} [Fintype C] [Nonempty C] (f : C → BucketVec mldsa87 × CommitHashBytes mldsa87)
    {δ : ℝ}
    (hδ : tvDist ((uniformOfFintype C).map f) (shapedTarget cut) ≤ δ)
    (trOf : TqMatrix mldsa87.k mldsa87.l → _root_.MLDSA.Bytes 64) {m t Q : ℕ}
    (𝒜 : TqMatrix mldsa87.k mldsa87.l → Adversary (PresIn mldsa87 (_root_.MLDSA.Bytes 32) Ctx)
      (PresOut mldsa87) Ctx Unit (Option (Presentation mldsa87)) m t)
    (hpost : ∀ aHat r, ((𝒜 aHat).alg r).PostOracleFree) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, S.indicator (fun aHat => (𝒜 aHat).advantage
        (fun _ _ => True) (honestPresenter (trOf aHat))
        (honestPresenterLaw (concretePrimitives mldsa87) (matrixKey sk₀ aHat) aHat cut)
        (flatPresentSimOf f) Q) aHat ≤
      Q * √((1 / 2) ^ 1533 / ((cut.top : ℝ≥0∞).toReal * cut.meanShape * (1 - ε))) / 2 + Q * ε +
        (12 * Q + 24) / 2 ^ 294 / ((1 - ε) ^ 2 * ((cut.top : ℝ≥0∞).toReal * cut.meanShape)) +
        Q * δ +
        ((2 * Q * t + Q * (Q - 1) / 2) / 2 ^ 256 + (Q * t + Q * (Q - 1) / 2) / 2 ^ 512) := by
  have hm := cut.meanShape_pos
  have hδ0 : 0 ≤ δ := (tvDist_nonneg _ _).trans hδ
  have hQQ := natCast_mul_sub_one_nonneg Q
  rcases S.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp only [Set.indicator_empty, expect_const_zero]
    positivity
  have := concreteNTTRingLaws
  have hp := SigningParams.of_isApproved (p := mldsa87) (Or.inr (Or.inr rfl))
  have hf₀ := hf a₀ ha₀
  have h1 : 0 < 1 - ε := sub_pos.2 hf₀.lt_one
  have hβ : 0 < (cut.top : ℝ≥0∞).toReal := hf₀.cutoff_pos
  have hR : 𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, S.indicator (fun aHat =>
      signerRegGap (concretePrimitives mldsa87) (matrixKey sk₀ aHat) aHat cut) aHat ≤
        12 / 2 ^ 294 / ((1 - ε) * cut.meanShape * (cut.top : ℝ≥0∞).toReal) := by
    simp only [matrixKey_eq]
    exact expect_signerRegGap_le_mldsa87_seven sk₀ hs1 hs2 hf₀.cutoff_ne_zero hf₀.cutoff_ne_top
      (mul_pos h1 hm) S fun aHat h v => by
        simpa only [matrixKey_eq] using (hf aHat h).one_sub_mul_le_expect_flatWeight hp v
  have h := expect_advantage_honestPresenter_le_of_keyFloorAt (concretePrimitives mldsa87) hp
    (signingLaws_concrete mldsa87 (Or.inr (Or.inr rfl))) sk₀ hs2 hε hf₀.lt_one S hf f hδ trOf 𝒜
    hpost (expect_min_one_mul_flatOracleConcError_le_mldsa87_of_keyFloorAt sk₀ hs1 hs2 S hf Q) hR
  rw [card_bytes32_eq] at h
  refine h.trans_eq ?_
  generalize √((1 / 2 : ℝ) ^ 1533 / ((cut.top : ℝ≥0∞).toReal * cut.meanShape * (1 - ε))) = Sq
  have hA : (2 : ℝ) ^ 294 ≠ 0 := by positivity
  have h1' := h1.ne'
  have hβ' := hβ.ne'
  have hm' := hm.ne'
  generalize (2 : ℝ) ^ 294 = A at hA ⊢
  generalize (2 : ℝ) ^ 256 = B
  generalize (2 : ℝ) ^ 512 = D
  field_simp
  ring

/-- **The presentations at ML-DSA-87 over a uniform matrix**: as
`expect_advantage_honestPresenter_le_mldsa65`, at most
`Q √(2^-1533 / (β_min (1 - ε))) / 2 + Q ε + (12 Q + 24) · 2^-294 / ((1 - ε)² β_min)
+ (2 Q t + Q (Q - 1) / 2) / 2^256 + (Q t + Q (Q - 1) / 2) / 2^512`
(`expect_advantage_honestPresenter_le_mldsa87_of_keyFloorAt`). -/
theorem expect_advantage_honestPresenter_le_mldsa87 {Ctx : Type} [Fintype Ctx] [DecidableEq Ctx]
    (sk₀ : SecretKey mldsa87) (hs1 : polyVecBounded sk₀.s1 mldsa87.eta)
    (hs2 : polyVecBounded sk₀.s2 mldsa87.eta) {βmin : ℚ≥0} {ε : ℝ}
    (hf : ∀ aHat, KeyFloor (concretePrimitives mldsa87) βmin ε (matrixKey sk₀ aHat).t0)
    (trOf : TqMatrix mldsa87.k mldsa87.l → _root_.MLDSA.Bytes 64) {m t Q : ℕ}
    (𝒜 : TqMatrix mldsa87.k mldsa87.l → Adversary (PresIn mldsa87 (_root_.MLDSA.Bytes 32) Ctx)
      (PresOut mldsa87) Ctx Unit (Option (Presentation mldsa87)) m t)
    (hpost : ∀ aHat r, ((𝒜 aHat).alg r).PostOracleFree) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, (𝒜 aHat).advantage (fun _ _ => True)
        (honestPresenter (trOf aHat))
        (honestPresenterLaw (concretePrimitives mldsa87) (matrixKey sk₀ aHat) aHat
          (Cutoff.const βmin))
        flatPresentSim Q ≤
      Q * √((1 / 2) ^ 1533 / ((βmin : ℝ≥0∞).toReal * (1 - ε))) / 2 + Q * ε +
        (12 * Q + 24) / 2 ^ 294 / ((1 - ε) ^ 2 * (βmin : ℝ≥0∞).toReal) +
        ((2 * Q * t + Q * (Q - 1) / 2) / 2 ^ 256 + (Q * t + Q * (Q - 1) / 2) / 2 ^ 512) := by
  have h := expect_advantage_honestPresenter_le_mldsa87_of_keyFloorAt sk₀ hs1 hs2
    (cut := Cutoff.const βmin) (hf (Classical.arbitrary _)).nonneg Set.univ
    (fun aHat _ => keyFloorAt_const_iff.2 (hf aHat)) id (tvDist_map_id_shapedTarget_const βmin)
    trOf (Q := Q) 𝒜 hpost
  rw [flatPresentSim_eq_flatPresentSimOf]
  simpa only [Set.indicator_univ, Cutoff.meanShape_const, mul_one, mul_zero, add_zero] using h

end GordieHowe.MLDSA
