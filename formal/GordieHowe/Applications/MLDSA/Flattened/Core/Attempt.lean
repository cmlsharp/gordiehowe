-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.Core.Weights
public import GordieHowe.Foundations.ToMathlib.PMFFreshFactor
public import GordieHowe.Foundations.ToMathlib.PMFOfWeight

public section

/-!
# The flattened signer with a keep factor

The core signer: FIPS 204 attempts (`y` uniform on the mask box, `w₁ = HighBits(Â·y)`, the four
checks of Algorithm 7), a fresh commitment hash `c̃` and fresh side data `z` per attempt, and the
keep coin `min(1, val(c̃) / aw) · g (w₁, c̃, z)` for a public cut-off `val = top · shape` (`Cutoff`)
and a keep factor `g ∈ [0, 1]` that does not read the
mask or the secret key (`KeepFactor`, `flatAttempt`). The credential presentations use `g = 1`
(`KeepFactor.one`), a public filter later; the ring signer uses the other members' flattened
weights, with `z` their commitment hashes.

* `flatKeptLaw`, `standinFlatKeptLaw`: the laws of the kept `(w₁, c̃, z)`, real (`y` uniform on the
  mask box) and stand-in (`w` uniform).
* `Cutoff.keep`: the keep factor `shape(c̃) · g`, equal to `g` at a constant cut-off
  (`Cutoff.keep_const`).
* `standinFlatKeptLaw_eq_ofWeight`: **the exact stand-in law**: density proportional to
  `min(1, aw / val(c̃)) · shape(c̃) · g` (`flatKeptWeight` of `cut.keep g`), with no floor.
* `flatTargetOn`: the law with density proportional to `g`.
* `KeyFloorOn`: the floor relative to `g`, `𝔼[g · 1(checkWeight < val)] ≤ ε · 𝔼[g]`;
  `KeyFloorOn.of_checkDefect_le`: for a `g` that does not read `c̃` it follows from the per-key
  floor `checkDefect cut t₀ ≤ ε`.
* `KeyFloorOn.tvDist_ofWeight_flatKeptWeight_le`: **the floor step**: under the floor the law
  with density `min(1, aw / val(c̃)) · g` is within `ε` of `flatTargetOn g`.
* `KeyFloorOn.of_le_checkWeight`, `standinFlatKeptLaw_eq_flatTargetOn`: **the exact floor**: a
  cut-off below the check weight at every `c̃` has floor defect 0, and the stand-in kept law is
  then the law with density `shape · g`.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete Finset PMF
open scoped ENNReal BigOperators

variable {p : Params} {Z : Type} [Fintype Z]

/-- **A keep factor** of the flattened signer: a probability at each commitment, commitment hash
and side data. It reads neither the mask nor the secret key. Its value is rational (`qval`, which
a signer computes) and `val` is that value in `ℝ≥0∞` (`val_eq`), the form the probability
statements use, as `flattenCoin` and `t0Weight` pair a rational with its cast. -/
structure KeepFactor (p : Params) (Z : Type) where
  /-- The factor at `(w₁, c̃, z)`. -/
  val : BucketVec p × CommitHashBytes p × Z → ℝ≥0∞
  /-- The factor is a probability. -/
  le_one : ∀ a, val a ≤ 1
  /-- The factor as a rational, the value a signer computes. -/
  qval : BucketVec p × CommitHashBytes p × Z → ℚ≥0
  /-- The factor is the rational value in `ℝ≥0∞`. -/
  val_eq : ∀ a, val a = qval a

/-- **The unit keep factor**: keep every attempt the flattening coin keeps. -/
@[expose] def KeepFactor.one : KeepFactor p Z where
  val _ := 1
  le_one _ := le_rfl
  qval _ := 1
  val_eq _ := ENNReal.nnratCast_one.symm

/-- **The keep factor `shape(c̃) · g`** of a cut-off and a keep factor. -/
@[expose] noncomputable def Cutoff.keep (cut : Cutoff p) (g : KeepFactor p Z) : KeepFactor p Z where
  val a := (cut.shape a.2.1 : ℝ≥0∞) * g.val a
  le_one a := mul_le_one' (cut.coe_shape_le_one a.2.1) (g.le_one a)
  qval a := cut.shape a.2.1 * g.qval a
  val_eq a := by rw [g.val_eq, ENNReal.nnratCast_mul]

omit [Fintype Z] in
/-- At a constant cut-off the keep factor `shape · g` is `g`. -/
theorem Cutoff.keep_const (β : ℚ≥0) (g : KeepFactor p Z) : (Cutoff.const β).keep g = g := by
  obtain ⟨val, le_one, qval, val_eq⟩ := g
  simp only [Cutoff.keep, ENNReal.nnratCast_one, one_mul]

/-- The total of a keep factor is finite. -/
theorem KeepFactor.sum_ne_top (g : KeepFactor p Z) : ∑ a, g.val a ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun a _ => ne_top_of_le_ne_top ENNReal.one_ne_top (g.le_one a)

variable [NeZero (bucketCount p)]

/-- **The law with density proportional to the keep factor.** -/
@[expose] noncomputable def flatTargetOn (g : KeepFactor p Z) (h0 : ∑ a, g.val a ≠ 0) :
    PMF (BucketVec p × CommitHashBytes p × Z) :=
  ofWeight g.val h0 g.sum_ne_top

variable (prims : Primitives p) [nttOps : NTTRingOps]

/-- **The density of the kept law**: the flattened weight `min(1, aw / val(c̃))` of `t₀` times the
keep factor. -/
@[expose] noncomputable def flatKeptWeight (cut : Cutoff p) (t0 : RqVec p.k) (g : KeepFactor p Z)
    (a : BucketVec p × CommitHashBytes p × Z) : ℝ≥0∞ :=
  (flatWeight prims cut t0 (a.1, a.2.1) : ℝ≥0∞) * g.val a

omit [NeZero (bucketCount p)] [Fintype Z] in
/-- The kept density is at most the keep factor. -/
theorem flatKeptWeight_le (cut : Cutoff p) (t0 : RqVec p.k) (g : KeepFactor p Z)
    (a : BucketVec p × CommitHashBytes p × Z) : flatKeptWeight prims cut t0 g a ≤ g.val a :=
  mul_le_of_le_one_left' (ENNReal.nnratCast_le_one.2 (NNRat.minOneDiv_le_one _ _))

omit [NeZero (bucketCount p)] in
/-- The total kept density is finite. -/
theorem sum_flatKeptWeight_ne_top (cut : Cutoff p) (t0 : RqVec p.k) (g : KeepFactor p Z) :
    ∑ a, flatKeptWeight prims cut t0 g a ≠ ⊤ :=
  ne_top_of_le_ne_top g.sum_ne_top (sum_le_sum fun a _ => flatKeptWeight_le prims cut t0 g a)

/-! ### The floor relative to the keep factor -/

section Floor

/-- **The floor relative to a keep factor** at the cut-off `val` with level `top ∈ (0, 1]`: the
keep factor's mass where the check weight of `t₀` is below `val(c̃)` is at most `ε < 1` times its
whole mass, `∑ g · 1(checkWeight t₀ c̃ < val c̃) ≤ ε · ∑ g`, and that mass is positive. With
`g = 1` and a constant cut-off it is the per-key floor (`KeyFloor`); for a `g` that does not read
`c̃` it follows from the per-key check defect (`KeyFloorOn.of_checkDefect_le`). It is a property
of the key, the cut-off and `g`. -/
structure KeyFloorOn (g : KeepFactor p Z) (cut : Cutoff p) (ε : ℝ) (t0 : RqVec p.k) : Prop where
  /-- The level of the cut-off is positive. -/
  cutoff_ne_zero : (cut.top : ℝ≥0∞) ≠ 0
  /-- The level of the cut-off is at most one. -/
  cutoff_le_one : (cut.top : ℝ≥0∞) ≤ 1
  /-- The defect bound is below one. -/
  lt_one : ε < 1
  /-- The keep factor has positive mass. -/
  mass_ne_zero : ∑ a, g.val a ≠ 0
  /-- The keep factor's mass below the cut-off is at most `ε` times its mass. -/
  defect_le : ∑ a, (g.val a).toReal *
      (if checkWeight prims t0 a.2.1 < cut.val a.2.1 then 1 else 0) ≤
    ε * ∑ a, (g.val a).toReal

variable {prims}

omit [NeZero (bucketCount p)] in
/-- At a constant cut-off a floor relative to `g` is a floor relative to `shape · g`
(`Cutoff.keep_const`). -/
theorem KeyFloorOn.keep_const {g : KeepFactor p Z} {β : ℚ≥0} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloorOn prims g (Cutoff.const β) ε t0) :
    KeyFloorOn prims ((Cutoff.const β).keep g) (Cutoff.const β) ε t0 := by
  rwa [Cutoff.keep_const]

omit [NeZero (bucketCount p)] in
/-- The level of the cut-off of a floor is finite. -/
theorem KeyFloorOn.cutoff_ne_top {g : KeepFactor p Z} {cut : Cutoff p} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloorOn prims g cut ε t0) : (cut.top : ℝ≥0∞) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top hf.cutoff_le_one

omit [NeZero (bucketCount p)] in
/-- The mass of the keep factor is positive, in `ℝ`. -/
theorem KeyFloorOn.sum_toReal_pos {g : KeepFactor p Z} {cut : Cutoff p} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloorOn prims g cut ε t0) : 0 < ∑ a, (g.val a).toReal := by
  rw [← ENNReal.toReal_sum fun a _ => ne_top_of_le_ne_top ENNReal.one_ne_top (g.le_one a)]
  exact ENNReal.toReal_pos hf.mass_ne_zero g.sum_ne_top

omit [Fintype Z] in
variable (prims) in
omit [NeZero (bucketCount p)] in
/-- **The kept density falls short of the keep factor only below the cut-off**:
`g - min(1, aw / val) · g ≤ g · 1(checkWeight < val)`. -/
theorem toReal_sub_flatKeptWeight_le (hp : SigningParams p) {cut : Cutoff p}
    (hβ0 : (cut.top : ℝ≥0∞) ≠ 0) (t0 : RqVec p.k) (g : KeepFactor p Z)
    (a : BucketVec p × CommitHashBytes p × Z) :
    (g.val a).toReal - (flatKeptWeight prims cut t0 g a).toReal ≤
      (g.val a).toReal * (if checkWeight prims t0 a.2.1 < cut.val a.2.1 then 1 else 0) := by
  split_ifs with h
  · rw [mul_one]
    exact sub_le_self _ ENNReal.toReal_nonneg
  · rw [mul_zero, flatKeptWeight,
      flatWeight_eq_one_of_le_checkWeight prims hp hβ0 (vc := (a.1, a.2.1)) (not_lt.1 h)]
    simp

omit [NeZero (bucketCount p)] in
/-- **The kept mass under the floor** is at least `1 - ε` times the keep factor's mass. -/
theorem KeyFloorOn.one_sub_mul_le_sum_flatKeptWeight (hp : SigningParams p)
    {g : KeepFactor p Z} {cut : Cutoff p} {ε : ℝ} {t0 : RqVec p.k}
    (hf : KeyFloorOn prims g cut ε t0) :
    (1 - ε) * ∑ a, (g.val a).toReal ≤ ∑ a, (flatKeptWeight prims cut t0 g a).toReal := by
  have h := sum_le_sum fun a (_ : a ∈ univ) =>
    toReal_sub_flatKeptWeight_le prims hp hf.cutoff_ne_zero t0 g a
  rw [sum_sub_distrib] at h
  linarith [hf.defect_le]

omit [NeZero (bucketCount p)] in
/-- The kept mass under the floor is not zero. -/
theorem KeyFloorOn.sum_flatKeptWeight_ne_zero (hp : SigningParams p) {g : KeepFactor p Z}
    {cut : Cutoff p} {ε : ℝ} {t0 : RqVec p.k} (hf : KeyFloorOn prims g cut ε t0) :
    ∑ a, flatKeptWeight prims cut t0 g a ≠ 0 := by
  intro h
  have h1 := hf.one_sub_mul_le_sum_flatKeptWeight hp
  rw [← ENNReal.toReal_sum fun a _ => ne_top_of_le_ne_top ENNReal.one_ne_top
    ((flatKeptWeight_le prims cut t0 g a).trans (g.le_one a)), h, ENNReal.toReal_zero] at h1
  nlinarith [hf.sum_toReal_pos, hf.lt_one]

omit [NeZero (bucketCount p)] in
/-- **The floor step**: under the floor relative to `g`, the law with density
`min(1, aw / val) · g` is within `ε` of the law with density `g` (`tvDist_ofWeight_le_of_le`). -/
theorem KeyFloorOn.tvDist_ofWeight_flatKeptWeight_le (hp : SigningParams p) {g : KeepFactor p Z}
    {cut : Cutoff p} {ε : ℝ} {t0 : RqVec p.k} (hf : KeyFloorOn prims g cut ε t0) :
    tvDist (ofWeight (flatKeptWeight prims cut t0 g) (hf.sum_flatKeptWeight_ne_zero hp)
        (sum_flatKeptWeight_ne_top prims cut t0 g)) (flatTargetOn g hf.mass_ne_zero) ≤ ε := by
  refine (tvDist_ofWeight_le_of_le _ _ _ _ fun a => flatKeptWeight_le prims cut t0 g a).trans ?_
  have hpos := hf.sum_toReal_pos
  rw [div_le_iff₀ hpos]
  exact (sum_le_sum fun a _ =>
    toReal_sub_flatKeptWeight_le prims hp hf.cutoff_ne_zero t0 g a).trans
      hf.defect_le

omit [NeZero (bucketCount p)] in
/-- **The free floor**: for a keep factor that does not read the commitment hash, the floor
relative to `g` follows from the per-key floor `checkDefect cut t₀ ≤ ε`, with the same `ε`,
since `c̃` is independent of `(w₁, z)`. -/
theorem KeyFloorOn.of_checkDefect_le {g : KeepFactor p Z} {cut : Cutoff p} {ε : ℝ} {t0 : RqVec p.k}
    (hβ0 : (cut.top : ℝ≥0∞) ≠ 0) (hβ1 : (cut.top : ℝ≥0∞) ≤ 1) (hε : ε < 1)
    (hd : checkDefect prims cut t0 ≤ ε) (h0 : ∑ a, g.val a ≠ 0)
    (hg : ∀ v c c' z, g.val (v, c, z) = g.val (v, c', z)) : KeyFloorOn prims g cut ε t0 where
  cutoff_ne_zero := hβ0
  cutoff_le_one := hβ1
  lt_one := hε
  mass_ne_zero := h0
  defect_le := by
    classical
    obtain ⟨c₀⟩ := (inferInstance : Nonempty (CommitHashBytes p))
    set h : BucketVec p → Z → ℝ := fun v z => (g.val (v, c₀, z)).toReal
    set ind : CommitHashBytes p → ℝ := fun c =>
      if checkWeight prims t0 c < cut.val c then 1 else 0
    have hcd : ∑ c, ind c = Fintype.card (CommitHashBytes p) * checkDefect prims cut t0 := by
      rw [checkDefect, Fintype.expect_eq_sum_div_card, mul_div_cancel₀]
      exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hL : ∑ a : BucketVec p × CommitHashBytes p × Z,
        (g.val a).toReal * (if checkWeight prims t0 a.2.1 < cut.val a.2.1 then 1 else 0) =
          (∑ v, ∑ z, h v z) * ∑ c, ind c := by
      rw [Fintype.sum_prod_type, sum_mul]
      refine sum_congr rfl fun v _ => ?_
      rw [Fintype.sum_prod_type, sum_comm, sum_mul]
      refine sum_congr rfl fun z _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun c _ => by rw [hg v c c₀ z]
    have hR : ∑ a : BucketVec p × CommitHashBytes p × Z, (g.val a).toReal =
        (∑ v, ∑ z, h v z) * Fintype.card (CommitHashBytes p) := by
      rw [Fintype.sum_prod_type, sum_mul]
      refine sum_congr rfl fun v _ => ?_
      rw [Fintype.sum_prod_type, sum_comm, sum_mul]
      refine sum_congr rfl fun z _ => ?_
      rw [sum_congr rfl fun c _ => by rw [hg v c c₀ z], sum_const, card_univ, nsmul_eq_mul,
        mul_comm]
    rw [hL, hR, hcd]
    have hh : 0 ≤ ∑ v, ∑ z, h v z :=
      sum_nonneg fun v _ => sum_nonneg fun z _ => ENNReal.toReal_nonneg
    have hC : (0 : ℝ) ≤ Fintype.card (CommitHashBytes p) := Nat.cast_nonneg _
    calc (∑ v, ∑ z, h v z) * (Fintype.card (CommitHashBytes p) * checkDefect prims cut t0)
        ≤ (∑ v, ∑ z, h v z) * (Fintype.card (CommitHashBytes p) * ε) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hC) hh
      _ = ε * ((∑ v, ∑ z, h v z) * Fintype.card (CommitHashBytes p)) := by ring

omit [NeZero (bucketCount p)] [Fintype Z] in
variable (prims) in
/-- **The kept density under the exact floor**: for a cut-off below the check weight at every
commitment hash, the kept density is the keep factor. -/
theorem flatKeptWeight_eq_of_le_checkWeight (hp : SigningParams p) {cut : Cutoff p}
    (hβ0 : (cut.top : ℝ≥0∞) ≠ 0) {t0 : RqVec p.k} (h : ∀ c, cut.val c ≤ checkWeight prims t0 c)
    {g : KeepFactor p Z} (a : BucketVec p × CommitHashBytes p × Z) :
    flatKeptWeight prims cut t0 g a = g.val a := by
  rw [flatKeptWeight, flatWeight_eq_one_of_le_checkWeight prims hp hβ0 (vc := (a.1, a.2.1))
    (h a.2.1)]
  simp

omit [NeZero (bucketCount p)] in
/-- **The exact floor**: a cut-off below the check weight at every commitment hash has floor
defect 0, relative to every keep factor of positive mass. -/
theorem KeyFloorOn.of_le_checkWeight {g : KeepFactor p Z} {cut : Cutoff p} {t0 : RqVec p.k}
    (hβ0 : (cut.top : ℝ≥0∞) ≠ 0) (hβ1 : (cut.top : ℝ≥0∞) ≤ 1) (h0 : ∑ a, g.val a ≠ 0)
    (h : ∀ c, cut.val c ≤ checkWeight prims t0 c) : KeyFloorOn prims g cut 0 t0 where
  cutoff_ne_zero := hβ0
  cutoff_le_one := hβ1
  lt_one := zero_lt_one
  mass_ne_zero := h0
  defect_le := by
    simp [not_lt.2 (h _)]

end Floor

variable [DecidableEq Z] [Nonempty Z] (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
  (cut : Cutoff p) (g : KeepFactor p Z)

/-- **The stand-in attempt with keep factor `g`**: `w` uniform on coefficient vectors, a fresh
uniform `(c̃, z)`, the stand-in checks, and the keep coin `min(1, val(c̃) / aw) · g`. -/
@[expose] noncomputable def standinFlatAttempt : PMF (Option (BucketVec p × CommitHashBytes p × Z)) :=
  freshAttemptWith (uniformOfFintype (CoeffIndex p → Coeff)) bucketsOf (standinAccept prims sk)
    (fun a => (flattenCoin prims sk cut a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk cut) g.val
    g.le_one

/-- **The stand-in kept law with keep factor `g`.** -/
@[expose] noncomputable def standinFlatKeptLaw : PMF (BucketVec p × CommitHashBytes p × Z) :=
  condSomeOr (standinFlatAttempt prims sk cut g) (uniformOfFintype _)

/-- **The stand-in attempt keeps in proportion to the kept density of `shape · g`**:
`uniformScale · top · |C × Z|⁻¹ · min(1, aw / val) · shape · g`. -/
theorem standinFlatAttempt_apply_some (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) (a : BucketVec p × CommitHashBytes p × Z) :
    standinFlatAttempt prims sk cut g (some a) =
      uniformScale p * cut.top * (Fintype.card (CommitHashBytes p × Z) : ℝ≥0∞)⁻¹ *
        flatKeptWeight prims cut sk.t0 (cut.keep g) a := by
  obtain ⟨v, c, z⟩ := a
  rw [standinFlatAttempt, freshAttemptWith_apply_some, SigningLaws.signerMass_standin prims sk hp
    h_laws hs2, ← uniformScale, flatKeptWeight]
  have h := mul_flattenCoin_eq prims sk cut (v, c)
  calc uniformScale p * (signerWeight prims sk (v, c) : ℝ≥0∞) *
        (Fintype.card (CommitHashBytes p × Z) : ℝ≥0∞)⁻¹ *
        ((flattenCoin prims sk cut (v, c) : ℝ≥0∞) * g.val (v, c, z))
      = uniformScale p * (Fintype.card (CommitHashBytes p × Z) : ℝ≥0∞)⁻¹ *
          ((signerWeight prims sk (v, c) : ℝ≥0∞) * (flattenCoin prims sk cut (v, c) : ℝ≥0∞)) *
          g.val (v, c, z) := by ring
    _ = _ := by rw [h, Cutoff.keep]; ring

/-- **The exact stand-in law**: for every keep factor with positive kept mass, the stand-in kept
law has density proportional to `min(1, aw / val) · shape · g`, with no floor. -/
theorem standinFlatKeptLaw_eq_ofWeight (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) (hβ0 : (cut.top : ℝ≥0∞) ≠ 0)
    (h0 : ∑ a, flatKeptWeight prims cut sk.t0 (cut.keep g) a ≠ 0) :
    standinFlatKeptLaw prims sk cut g =
      ofWeight (flatKeptWeight prims cut sk.t0 (cut.keep g)) h0
        (sum_flatKeptWeight_ne_top prims cut _ (cut.keep g)) := by
  set r := uniformScale p * cut.top * (Fintype.card (CommitHashBytes p × Z) : ℝ≥0∞)⁻¹
  have hr0 : r ≠ 0 := by
    simp only [r, ne_eq, mul_eq_zero, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, or_false, not_or]
    exact ⟨fun h => by simpa [h] using uniformScale_pos hp, hβ0⟩
  have hA := standinFlatAttempt_apply_some prims sk cut g hp h_laws hs2
  have hne : standinFlatAttempt prims sk cut g none ≠ 1 := by
    intro h1
    have hs := sum_apply_some (standinFlatAttempt prims sk cut g)
    rw [h1, tsub_self, sum_congr rfl fun a _ => hA a, ← mul_sum] at hs
    exact h0 ((mul_eq_zero.1 hs).resolve_left hr0)
  rw [standinFlatKeptLaw, condSomeOr_of_ne _ hne]
  exact condSome_eq_ofWeight hne _ _ _ hA

/-- **The exact stand-in law under the exact floor**: for a cut-off below the check weight of the
signer's `t₀` at every commitment hash, the stand-in kept law is the law with density
`shape · g` (`flatKeptWeight_eq_of_le_checkWeight`). -/
theorem standinFlatKeptLaw_eq_flatTargetOn (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) (hβ0 : (cut.top : ℝ≥0∞) ≠ 0)
    (h : ∀ c, cut.val c ≤ checkWeight prims sk.t0 c) (h0 : ∑ a, (cut.keep g).val a ≠ 0) :
    standinFlatKeptLaw prims sk cut g = flatTargetOn (cut.keep g) h0 := by
  have hw : flatKeptWeight prims cut sk.t0 (cut.keep g) = (cut.keep g).val :=
    funext fun a => flatKeptWeight_eq_of_le_checkWeight prims hp hβ0 h a
  have h0' : ∑ a, flatKeptWeight prims cut sk.t0 (cut.keep g) a ≠ 0 := by rwa [hw]
  rw [standinFlatKeptLaw_eq_ofWeight prims sk cut g hp h_laws hs2 hβ0 h0', flatTargetOn]
  ext a
  simp only [ofWeight_apply, hw]

variable [Nonempty (MaskBox p)]

/-- **The attempt of the flattened signer with keep factor `g`**: `y` uniform on the mask box,
`w₁ = HighBits(Â·y)`, a fresh uniform `(c̃, z)`, the four checks, and the keep coin
`min(1, val(c̃) / aw) · g (w₁, c̃, z)`. -/
@[expose] noncomputable def flatAttempt : PMF (Option (BucketVec p × CommitHashBytes p × Z)) :=
  freshAttemptWith (maskUniform p) (realBuckets aHat) (attemptAccept prims sk aHat)
    (fun a => (flattenCoin prims sk cut a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk cut) g.val
    g.le_one

/-- **The kept law of the flattened signer with keep factor `g`**: the kept `(w₁, c̃, z)`, or the
uniform law if no attempt keeps. -/
@[expose] noncomputable def flatKeptLaw : PMF (BucketVec p × CommitHashBytes p × Z) :=
  condSomeOr (flatAttempt prims sk aHat cut g) (uniformOfFintype _)

end GordieHowe.MLDSA
