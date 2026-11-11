-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.Core.RealStandin

public section

/-!
# The target law of the single-key flattened ML-DSA signer

The credential instance of the flattened signer (`Core/Attempt.lean`): no side data and the unit
keep factor (`KeepFactor.one`), so FIPS 204 attempts (`y` uniform on the mask box,
`w₁ = HighBits(Â·y)`, the four checks of Algorithm 7) and the keep coin `min(1, val(c̃) / aw)`,
`aw = t0Weight t₀` the uniform-`w` acceptance weight of the ct₀ and hint checks and `val` a public
cut-off (`Cutoff`). It follows a proposal by another group: publish `(w₁, c̃)` with a
key-independent law by a key-dependent keep coin `min(1, p* / P_acc)`; here the cut-off `p*` is
`val(c̃)`, the constant `β_min` chosen per key or a public function of `c̃`.

* `flatTarget`: the uniform law on bucket vectors and commitment hashes; `shapedTarget cut`: `w₁`
  uniform and, independently, `c̃` with density proportional to the shape of the cut-off, the
  uniform law at a constant cut-off (`shapedTarget_const`).
* `KeyFloor`: the per-key floor, the cut-off conditions and a bound `ε < 1` on the key's check
  defect (`checkDefect`), the probability over a uniform `c̃` that the bucket-free check weight of
  `t₀` is below `β_min`.
* `KeyFloorAt`: the per-key floor at a cut-off, a bound `ε < 1` on the shaped check defect
  (`shapedDefect`, the probability over `c̃` drawn with density proportional to the shape that the
  check weight is below the cut-off); at a constant cut-off it is `KeyFloor`
  (`keyFloorAt_const_iff`), and a cut-off below the check weight gives it with `ε = 0`
  (`KeyFloorAt.of_le_checkWeight`).
* `KeyFloorAt.keyFloorOn_one`, `KeyFloorOn.keyFloorAt`: the per-key floor at a cut-off is the
  floor relative to the keep factor `shape` (`Cutoff.keep` of the unit keep factor);
  `KeyFloor.keyFloorOn_one`, `KeyFloorOn.keyFloor` are the constant case.
* `tvDist_standinFlat_shapedTarget_le_of_keyFloorAt`: under the floor, the stand-in flattened law
  (`standinKeptLaw`: `w` uniform, a fresh uniform `c̃`) is within `ε` of `shapedTarget`:
  the exact stand-in law (`standinFlatKeptLaw_eq_ofWeight`) followed by the floor step
  (`KeyFloorOn.tvDist_ofWeight_flatKeptWeight_le`); `tvDist_standinFlat_flatTarget_le_of_keyFloor`
  is the constant case.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete Finset PMF
open scoped ENNReal BigOperators

variable {p : Params} [NeZero (bucketCount p)]

/-- **The target law of the flattened signer**: `(w₁, c̃)` uniform on bucket vectors and
commitment hashes. It depends on no key, and matches the other group's claim that the published
pair is uniform.

It is uniform, not the law of `HighBits(w)` for a uniform `w`: the r0-check of FIPS 204
Algorithm 7 keeps exactly `2(γ₂ - β) - 1` residues in every `HighBits` bucket
(`bucket_r0_card`, `card_acceptSet`), so the stand-in accepted mass of `(v, c̃)` is a constant times
the acceptance weight with no bucket factor (`SigningLaws.signerMass_standin`). The law of
`HighBits(w)` itself is not uniform, since the wrap-around bucket `0` holds `2γ₂ + 1` residues and
the others `2γ₂`. -/
noncomputable def flatTarget (p : Params) [NeZero (bucketCount p)] :
    PMF (BucketVec p × CommitHashBytes p) :=
  uniformOfFintype _

/-- The target is the uniform law on pairs. -/
theorem flatTarget_eq_uniformOfFintype :
    flatTarget p = uniformOfFintype (BucketVec p × CommitHashBytes p) := by
  rw [flatTarget]

omit [NeZero (bucketCount p)] in
/-- The shape has positive total weight on pairs. -/
theorem Cutoff.sum_shape_ne_zero [NeZero (bucketCount p)] (cut : Cutoff p) :
    ∑ vc : BucketVec p × CommitHashBytes p, (cut.shape vc.2 : ℝ≥0∞) ≠ 0 := fun h => by
  obtain ⟨a⟩ := (inferInstance : Nonempty (BucketVec p × CommitHashBytes p))
  exact cut.coe_shape_ne_zero a.2 ((Finset.sum_eq_zero_iff.1 h) a (mem_univ a))

omit [NeZero (bucketCount p)] in
/-- The shape has finite total weight on pairs. -/
theorem Cutoff.sum_shape_ne_top [NeZero (bucketCount p)] (cut : Cutoff p) :
    ∑ vc : BucketVec p × CommitHashBytes p, (cut.shape vc.2 : ℝ≥0∞) ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun _ _ => ENNReal.nnratCast_ne_top _

/-- **The shaped target law**: `w₁` uniform and, independently, `c̃` with density proportional to
the shape of the cut-off. It depends on no key. -/
noncomputable def shapedTarget (cut : Cutoff p) : PMF (BucketVec p × CommitHashBytes p) :=
  ofWeight (fun vc => (cut.shape vc.2 : ℝ≥0∞)) cut.sum_shape_ne_zero cut.sum_shape_ne_top

/-- At a constant cut-off the shaped target is the uniform target. -/
theorem shapedTarget_const (β : ℚ≥0) : shapedTarget (Cutoff.const β : Cutoff p) = flatTarget p := by
  ext a
  rw [shapedTarget, ofWeight_apply, flatTarget_eq_uniformOfFintype, uniformOfFintype_apply]
  simp only [ENNReal.nnratCast_one, sum_const, card_univ, nsmul_eq_mul, mul_one, one_div]

/-- The keep factor `shape` without side data has positive mass. -/
theorem Cutoff.sum_keep_one_ne_zero (cut : Cutoff p) :
    ∑ a, (cut.keep (KeepFactor.one : KeepFactor p Unit)).val a ≠ 0 := fun h => by
  obtain ⟨a⟩ := (inferInstance : Nonempty (BucketVec p × CommitHashBytes p × Unit))
  have ha := (Finset.sum_eq_zero_iff.1 h) a (mem_univ a)
  simp only [Cutoff.keep, KeepFactor.one, mul_one] at ha
  exact cut.coe_shape_ne_zero a.2.1 ha

/-- **The shaped target is the law with density proportional to the keep factor `shape`**, with the
side data dropped. -/
theorem shapedTarget_eq_map_flatTargetOn (cut : Cutoff p) :
    shapedTarget cut =
      (flatTargetOn (cut.keep (KeepFactor.one : KeepFactor p Unit)) cut.sum_keep_one_ne_zero).map
        (dropUnitEquiv _ _) := by
  ext a
  rw [map_equiv_apply, flatTargetOn, shapedTarget, ofWeight_apply, ofWeight_apply,
    ← (dropUnitEquiv (BucketVec p) (CommitHashBytes p)).sum_comp
      (fun vc => (cut.shape vc.2 : ℝ≥0∞))]
  simp [Cutoff.keep, KeepFactor.one]

omit [NeZero (bucketCount p)] in
private theorem sum_unitSide (f : CommitHashBytes p → ℝ) :
    ∑ a : BucketVec p × CommitHashBytes p × Unit, f a.2.1 =
      Fintype.card (BucketVec p) * ∑ c, f c := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]
  rw [sum_const, card_univ, nsmul_eq_mul]

variable (prims : Primitives p) [nttOps : NTTRingOps]

/-- **The per-key floor** at the cut-off `β_min ∈ (0, 1]`: the check weight of `t₀`
(`checkWeight`, the bucket-free lower bound of the acceptance weight) is below `β_min` with
probability at most `ε < 1` over a uniform commitment hash (`checkDefect`). It is a property of
the key and the chosen cut-off, assumed here and discharged separately. -/
structure KeyFloor (βmin : ℚ≥0) (ε : ℝ) (t0 : RqVec p.k) : Prop where
  /-- The cut-off is positive. -/
  cutoff_ne_zero : (βmin : ℝ≥0∞) ≠ 0
  /-- The cut-off is at most one. -/
  cutoff_le_one : (βmin : ℝ≥0∞) ≤ 1
  /-- The defect bound is below one. -/
  lt_one : ε < 1
  /-- The check defect is at most `ε`. -/
  checkDefect_le : checkDefect prims (Cutoff.const βmin) t0 ≤ ε

/-- **The shaped check defect** of a key: the probability, over `c̃` drawn with density
proportional to the shape, that the check weight of `t₀` is below the cut-off at `c̃`. -/
noncomputable def shapedDefect (cut : Cutoff p) (t0 : RqVec p.k) : ℝ :=
  (∑ c, (cut.shape c : ℝ) * if checkWeight prims t0 c < cut.val c then 1 else 0) /
    ∑ c, (cut.shape c : ℝ)

omit [NeZero (bucketCount p)] in
/-- At a constant cut-off the shaped check defect is the check defect. -/
theorem shapedDefect_const (β : ℚ≥0) (t0 : RqVec p.k) :
    shapedDefect prims (Cutoff.const β) t0 = checkDefect prims (Cutoff.const β) t0 := by
  rw [shapedDefect, checkDefect, Fintype.expect_eq_sum_div_card]
  simp only [NNRat.cast_one, one_mul, sum_const, card_univ, nsmul_eq_mul, mul_one]

omit [NeZero (bucketCount p)] in
/-- The shaped check defect is nonnegative. -/
theorem shapedDefect_nonneg (cut : Cutoff p) (t0 : RqVec p.k) : 0 ≤ shapedDefect prims cut t0 :=
  div_nonneg (sum_nonneg fun _ _ => mul_nonneg (NNRat.cast_nonneg _) (by split_ifs <;> norm_num))
    (sum_nonneg fun _ _ => NNRat.cast_nonneg _)

/-- **The per-key floor at a cut-off**: the level is in `(0, 1]` and the shaped check defect of
`t₀` is at most `ε < 1`. -/
structure KeyFloorAt (cut : Cutoff p) (ε : ℝ) (t0 : RqVec p.k) : Prop where
  /-- The level of the cut-off is positive. -/
  cutoff_ne_zero : (cut.top : ℝ≥0∞) ≠ 0
  /-- The level of the cut-off is at most one. -/
  cutoff_le_one : (cut.top : ℝ≥0∞) ≤ 1
  /-- The defect bound is below one. -/
  lt_one : ε < 1
  /-- The shaped check defect is at most `ε`. -/
  shapedDefect_le : shapedDefect prims cut t0 ≤ ε

variable {prims}

omit [NeZero (bucketCount p)] in
/-- At a constant cut-off the per-key floor at the cut-off is the per-key floor. -/
theorem keyFloorAt_const_iff {β : ℚ≥0} {ε : ℝ} {t0 : RqVec p.k} :
    KeyFloorAt prims (Cutoff.const β) ε t0 ↔ KeyFloor prims β ε t0 :=
  ⟨fun h => ⟨h.cutoff_ne_zero, h.cutoff_le_one, h.lt_one,
      (shapedDefect_const prims β t0).symm.trans_le h.shapedDefect_le⟩,
    fun h => ⟨h.cutoff_ne_zero, h.cutoff_le_one, h.lt_one,
      (shapedDefect_const prims β t0).trans_le h.checkDefect_le⟩⟩

omit [NeZero (bucketCount p)] in
/-- **The exact floor at a cut-off**: a cut-off below the check weight at every commitment hash,
with level in `(0, 1]`, has shaped check defect 0. -/
theorem KeyFloorAt.of_le_checkWeight {cut : Cutoff p} {t0 : RqVec p.k}
    (hβ0 : (cut.top : ℝ≥0∞) ≠ 0) (hβ1 : (cut.top : ℝ≥0∞) ≤ 1)
    (h : ∀ c, cut.val c ≤ checkWeight prims t0 c) : KeyFloorAt prims cut 0 t0 where
  cutoff_ne_zero := hβ0
  cutoff_le_one := hβ1
  lt_one := zero_lt_one
  shapedDefect_le := by simp [shapedDefect, not_lt.2 (h _)]

omit [NeZero (bucketCount p)] in
/-- The level of the cut-off of a floor is finite. -/
theorem KeyFloorAt.cutoff_ne_top {cut : Cutoff p} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloorAt prims cut ε t0) : (cut.top : ℝ≥0∞) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top hf.cutoff_le_one

omit [NeZero (bucketCount p)] in
/-- The level of the cut-off of a floor is positive in `ℝ`. -/
theorem KeyFloorAt.cutoff_pos {cut : Cutoff p} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloorAt prims cut ε t0) : 0 < (cut.top : ℝ≥0∞).toReal :=
  ENNReal.toReal_pos hf.cutoff_ne_zero hf.cutoff_ne_top

omit [NeZero (bucketCount p)] in
/-- The defect bound of a floor is nonnegative (`shapedDefect_nonneg`). -/
theorem KeyFloorAt.nonneg {cut : Cutoff p} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloorAt prims cut ε t0) : 0 ≤ ε :=
  (shapedDefect_nonneg prims cut t0).trans hf.shapedDefect_le

omit [NeZero (bucketCount p)] nttOps in
/-- The total shape is positive in `ℝ`. -/
theorem Cutoff.sum_shape_pos (cut : Cutoff p) : 0 < ∑ c, (cut.shape c : ℝ) :=
  sum_pos (fun c _ => NNRat.cast_pos.2 (pos_iff_ne_zero.2 (cut.shape_ne_zero c))) univ_nonempty

omit [NeZero (bucketCount p)] in
/-- **The mean member weight times the shape under the floor** is at least `1 - ε` times the mean
shape in every bucket vector (`flatWeight_eq_one_of_le_checkWeight`). -/
theorem KeyFloorAt.one_sub_mul_le_expect_flatWeight (hp : SigningParams p) {cut : Cutoff p}
    {ε : ℝ} {t0 : RqVec p.k} (hf : KeyFloorAt prims cut ε t0) (v : BucketVec p) :
    (1 - ε) * cut.meanShape ≤ 𝔼 c : CommitHashBytes p,
      ((flatWeight prims cut t0 (v, c) : ℝ≥0∞) * (cut.shape c : ℝ≥0∞)).toReal := by
  have hd := hf.shapedDefect_le
  rw [shapedDefect, div_le_iff₀ cut.sum_shape_pos] at hd
  have hpt : ∀ c, (cut.shape c : ℝ) - (cut.shape c : ℝ) *
      (if checkWeight prims t0 c < cut.val c then 1 else 0) ≤
        ((flatWeight prims cut t0 (v, c) : ℝ≥0∞) * (cut.shape c : ℝ≥0∞)).toReal := fun c => by
    split_ifs with h
    · rw [mul_one, sub_self]
      exact ENNReal.toReal_nonneg
    · rw [flatWeight_eq_one_of_le_checkWeight prims hp hf.cutoff_ne_zero (vc := (v, c))
        (not_lt.1 h)]
      simp [ENNReal.toReal_nnratCast]
  have hsum := sum_le_sum fun c (_ : c ∈ univ) => hpt c
  rw [sum_sub_distrib] at hsum
  rw [Cutoff.meanShape, Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card,
    ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

omit [NeZero (bucketCount p)] in
/-- The means of the flattened weight times the shape are positive under the floor
(`KeyFloorAt.one_sub_mul_le_expect_flatWeight`). -/
theorem KeyFloorAt.expect_flatWeight_mul_shape_pos (hp : SigningParams p) {cut : Cutoff p}
    {ε : ℝ} {t0 : RqVec p.k} (hf : KeyFloorAt prims cut ε t0) (v : BucketVec p) :
    0 < 𝔼 c, ((flatWeight prims cut t0 (v, c) : ℝ≥0∞) * (cut.shape c : ℝ≥0∞)).toReal :=
  (mul_pos (sub_pos.2 hf.lt_one) cut.meanShape_pos).trans_le
    (hf.one_sub_mul_le_expect_flatWeight hp v)

private theorem defect_keep_one_iff {cut : Cutoff p} {ε : ℝ} {t0 : RqVec p.k} :
    (∑ a, ((cut.keep (KeepFactor.one : KeepFactor p Unit)).val a).toReal *
        (if checkWeight prims t0 a.2.1 < cut.val a.2.1 then 1 else 0) ≤
      ε * ∑ a, ((cut.keep (KeepFactor.one : KeepFactor p Unit)).val a).toReal) ↔
    shapedDefect prims cut t0 ≤ ε := by
  have hV : (0 : ℝ) < Fintype.card (BucketVec p) := Nat.cast_pos.2 Fintype.card_pos
  simp only [Cutoff.keep, KeepFactor.one, mul_one, ENNReal.toReal_nnratCast]
  rw [sum_unitSide fun c => (cut.shape c : ℝ) *
      (if checkWeight prims t0 c < cut.val c then 1 else 0),
    sum_unitSide fun c => (cut.shape c : ℝ), shapedDefect, div_le_iff₀ cut.sum_shape_pos,
    mul_left_comm]
  exact ⟨fun h => le_of_mul_le_mul_left h hV, fun h => mul_le_mul_of_nonneg_left h hV.le⟩

/-- **The per-key floor at a cut-off is the floor relative to the keep factor `shape`.** -/
theorem KeyFloorAt.keyFloorOn_one {cut : Cutoff p} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloorAt prims cut ε t0) :
    KeyFloorOn prims (cut.keep (KeepFactor.one : KeepFactor p Unit)) cut ε t0 where
  cutoff_ne_zero := hf.cutoff_ne_zero
  cutoff_le_one := hf.cutoff_le_one
  lt_one := hf.lt_one
  mass_ne_zero := cut.sum_keep_one_ne_zero
  defect_le := defect_keep_one_iff.2 hf.shapedDefect_le

/-- **The floor relative to the keep factor `shape` is the per-key floor at the cut-off.** -/
theorem KeyFloorOn.keyFloorAt {cut : Cutoff p} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloorOn prims (cut.keep (KeepFactor.one : KeepFactor p Unit)) cut ε t0) :
    KeyFloorAt prims cut ε t0 where
  cutoff_ne_zero := hf.cutoff_ne_zero
  cutoff_le_one := hf.cutoff_le_one
  lt_one := hf.lt_one
  shapedDefect_le := defect_keep_one_iff.1 hf.defect_le

omit [NeZero (bucketCount p)] in
/-- The cut-off of a floor is finite. -/
theorem KeyFloor.cutoff_ne_top {βmin : ℚ≥0} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloor prims βmin ε t0) : (βmin : ℝ≥0∞) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top hf.cutoff_le_one

omit [NeZero (bucketCount p)] in
/-- The cut-off of a floor is positive in `ℝ`. -/
theorem KeyFloor.cutoff_pos {βmin : ℚ≥0} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloor prims βmin ε t0) : 0 < (βmin : ℝ≥0∞).toReal :=
  ENNReal.toReal_pos hf.cutoff_ne_zero hf.cutoff_ne_top

omit [NeZero (bucketCount p)] in
/-- The defect bound of a floor is nonnegative (`checkDefect_nonneg`). -/
theorem KeyFloor.nonneg {βmin : ℚ≥0} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloor prims βmin ε t0) : 0 ≤ ε :=
  (checkDefect_nonneg prims (Cutoff.const βmin) t0).trans hf.checkDefect_le

omit [NeZero (bucketCount p)] in
/-- **The mean member weight under the floor** is at least `1 - ε` in every bucket vector
(`one_sub_checkDefect_le_expect_flatWeight`). -/
theorem KeyFloor.one_sub_le_expect_flatWeight (hp : SigningParams p) {βmin : ℚ≥0} {ε : ℝ}
    {t0 : RqVec p.k} (hf : KeyFloor prims βmin ε t0) (v : BucketVec p) :
    1 - ε ≤ 𝔼 c : CommitHashBytes p, (flatWeight prims (Cutoff.const βmin) t0 (v, c) :
        ℝ≥0∞).toReal :=
  (sub_le_sub_left hf.checkDefect_le 1).trans
    (one_sub_checkDefect_le_expect_flatWeight prims hp hf.cutoff_ne_zero t0 v)

omit nttOps in
/-- The unit keep factor without side data has positive mass. -/
theorem sum_keepFactorOne_ne_zero :
    ∑ _a : BucketVec p × CommitHashBytes p × Unit,
      (KeepFactor.one : KeepFactor p Unit).val _a ≠ 0 := by
  simp [KeepFactor.one]

/-- **The per-key floor is the floor relative to the unit keep factor**
(`KeyFloorAt.keyFloorOn_one`). -/
theorem KeyFloor.keyFloorOn_one {βmin : ℚ≥0} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloor prims βmin ε t0) :
    KeyFloorOn prims (KeepFactor.one : KeepFactor p Unit) (Cutoff.const βmin) ε t0 := by
  have h := (keyFloorAt_const_iff.2 hf).keyFloorOn_one
  rwa [Cutoff.keep_const] at h

/-- **The floor relative to the unit keep factor is the per-key floor**
(`KeyFloorOn.keyFloorAt`). -/
theorem KeyFloorOn.keyFloor {βmin : ℚ≥0} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloorOn prims (KeepFactor.one : KeepFactor p Unit) (Cutoff.const βmin) ε t0) :
    KeyFloor prims βmin ε t0 :=
  keyFloorAt_const_iff.1 hf.keep_const.keyFloorAt

variable (prims) in
/-- **The stand-in flattened law is close to the shaped target under the floor.** For a key with
`‖s₂‖∞ ≤ η` whose `t₀` satisfies the per-key floor at the cut-off with defect bound `ε < 1`, the
law of `(w₁, c̃)` of the stand-in flattened signer (`standinKeptLaw`: `w` uniform on coefficient
vectors, a fresh uniform `c̃`, the r0, ct₀ and hint checks, the keep coin `min(1, val(c̃) / aw)`) is
within `ε` of `shapedTarget`: it is the core's stand-in law with no side data and the unit keep
factor, which is exactly the law with density `min(1, aw / val(c̃)) · shape(c̃)`
(`standinFlatKeptLaw_eq_ofWeight`), within `ε` of the law with density `shape` under the floor
(`KeyFloorOn.tvDist_ofWeight_flatKeptWeight_le`). -/
theorem tvDist_standinFlat_shapedTarget_le_of_keyFloorAt (hp : SigningParams p)
    (h_laws : SigningLaws prims) {sk : SecretKey p} (hs2 : polyVecBounded sk.s2 p.eta)
    {cut : Cutoff p} {ε : ℝ} (hf : KeyFloorAt prims cut ε sk.t0) :
    tvDist (standinKeptLaw prims sk cut) (shapedTarget cut) ≤ ε := by
  have hfo := hf.keyFloorOn_one
  rw [← map_standinFlatKeptLaw_one prims sk cut, shapedTarget_eq_map_flatTargetOn]
  refine (tvDist_map_le _ _ _).trans ?_
  rw [standinFlatKeptLaw_eq_ofWeight prims sk cut _ hp h_laws hs2 hf.cutoff_ne_zero
    (hfo.sum_flatKeptWeight_ne_zero hp)]
  exact hfo.tvDist_ofWeight_flatKeptWeight_le hp

variable (prims) in
/-- **The stand-in flattened law is close to the target under the floor.** For a key with
`‖s₂‖∞ ≤ η` whose `t₀` satisfies the per-key floor at `β_min` with defect bound `ε < 1`, the law of
`(w₁, c̃)` of the stand-in flattened signer (`standinKeptLaw`: `w` uniform on coefficient vectors,
a fresh uniform `c̃`, the r0, ct₀ and hint checks, the keep coin `min(1, β_min / aw)`) is within
`ε` of the uniform target (`tvDist_standinFlat_shapedTarget_le_of_keyFloorAt` at the constant
cut-off, `shapedTarget_const`). -/
theorem tvDist_standinFlat_flatTarget_le_of_keyFloor (hp : SigningParams p)
    (h_laws : SigningLaws prims) {sk : SecretKey p} (hs2 : polyVecBounded sk.s2 p.eta)
    {βmin : ℚ≥0} {ε : ℝ} (hf : KeyFloor prims βmin ε sk.t0) :
    tvDist (standinKeptLaw prims sk (Cutoff.const βmin)) (flatTarget p) ≤ ε := by
  rw [← shapedTarget_const βmin]
  exact tvDist_standinFlat_shapedTarget_le_of_keyFloorAt prims hp h_laws hs2
    (keyFloorAt_const_iff.2 hf)

end GordieHowe.MLDSA
