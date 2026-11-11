-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.Core.Attempt
public import GordieHowe.Foundations.ToMathlib.PMFCondSome

public section

/-!
# The real and the stand-in flattened signer with a keep factor

* `zAcceptFraction_mul_standinMass_mul_flattenCoin`: the stand-in kept mass scaled by the
  z-acceptance fraction is `K · top · min(1, aw / val) · shape`, `K = standinScale`.
* `signerRegDev`: the column deviations `∑_v 𝔼_c |realMass - ρ_z · standinMass|` of the key at the
  matrix `Â`, at most `signerRegGap · K · top · |V|` when the means of the flattened weight times
  the shape are positive (`signerRegDev_le`).
* `sub_signerRegDev_le_toReal_one_sub_flatAttempt`: under the floor relative to `shape · g` the
  real attempt keeps with probability at least
  `K · top · (1 - ε) · keepMass (shape · g) - signerRegDev`, so it keeps when the column
  deviations are smaller (`flatKeeps_of_signerRegDev_lt`).
* `tvDist_flatKeptLaw_standinFlatKeptLaw_le_of_keyFloorOn`: **real against stand-in for every
  keep factor**: under the floor relative to `shape · g` (`Cutoff.keep`), when the real attempt
  keeps (`FlatKeeps`), the real and the stand-in kept laws are within
  `signerRegDev / (K · top · (1 - ε) · keepMass (shape · g))`, `keepMass` the mean of a keep
  factor over a fresh `(c̃, z)`, summed over `w₁` (`tvDist_condSome_le_scaled`).
* `map_flatKeptLaw_one`, `map_standinFlatKeptLaw_one`: with no side data and the unit keep factor
  the kept laws are `realKeptLaw` and `standinKeptLaw`; the mass of the keep factor `shape` is
  `|V| · s̄` (`keepMass_keep_one`).
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete Finset PMF
open scoped ENNReal BigOperators

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]
  (sk : SecretKey p) (aHat : TqMatrix p.k p.l)

/-- **The scaled stand-in kept mass**: `ρ_z · standinMass(v, c̃) · min(1, val / aw) =
K · top · min(1, aw / val) · shape` with `K = standinScale` (`SigningLaws.signerMass_standin`,
`mul_flattenCoin_eq`). -/
theorem zAcceptFraction_mul_standinMass_mul_flattenCoin (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) (cut : Cutoff p)
    (v : BucketVec p) (c : CommitHashBytes p) :
    zAcceptFraction p * standinMass prims sk v c * (flattenCoin prims sk cut (v, c) : ℝ≥0∞) =
      standinScale p * cut.top *
        ((flatWeight prims cut sk.t0 (v, c) : ℝ≥0∞) * (cut.shape c : ℝ≥0∞)) := by
  rw [standinMass, SigningLaws.signerMass_standin prims sk hp h_laws hs2, ← uniformScale,
    standinScale, mul_assoc (zAcceptFraction p), mul_assoc (uniformScale p),
    mul_flattenCoin_eq prims sk cut]
  ring

variable [Nonempty (MaskBox p)] {Z : Type} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- **The column deviations of the key at the matrix `Â`**:
`∑_v 𝔼_c |realMass(v, c) - ρ_z · standinMass(v, c)|`, the distance between the real accepted mass
(`y` uniform on the mask box) and the stand-in mass scaled by the z-acceptance fraction. -/
noncomputable def signerRegDev : ℝ :=
  ∑ v, 𝔼 c, |(realMass prims sk aHat v c).toReal -
    (zAcceptFraction p * standinMass prims sk v c).toReal|

theorem signerRegDev_nonneg : 0 ≤ signerRegDev prims sk aHat :=
  sum_nonneg fun _ _ => Finset.expect_nonneg fun _ _ => abs_nonneg _

/-- **The column deviations against the regularity gap**: when every mean of the flattened weight
times the shape is positive, `signerRegDev ≤ signerRegGap · K · top · |V|`. -/
theorem signerRegDev_le (hp : SigningParams p) {cut : Cutoff p} (hβ0 : (cut.top : ℝ≥0∞) ≠ 0)
    (hβt : (cut.top : ℝ≥0∞) ≠ ⊤)
    (hm : ∀ v, 0 < 𝔼 c,
      ((flatWeight prims cut sk.t0 (v, c) : ℝ≥0∞) * (cut.shape c : ℝ≥0∞)).toReal) :
    signerRegDev prims sk aHat ≤
      signerRegGap prims sk aHat cut *
        ((standinScale p * cut.top).toReal * Fintype.card (BucketVec p)) := by
  have hpos : 0 < (standinScale p * cut.top).toReal * Fintype.card (BucketVec p) :=
    mul_pos (flatLevel_pos hp hβ0 hβt) (Nat.cast_pos.2 Fintype.card_pos)
  rw [signerRegGap, div_mul_cancel₀ _ hpos.ne', signerRegDev]
  refine sum_le_sum fun v _ => le_div_self (Finset.expect_nonneg fun _ _ => abs_nonneg _) (hm v) ?_
  exact (Finset.expect_le_expect fun c _ => ENNReal.toReal_le_one_of_le_one
    (mul_le_one' (ENNReal.nnratCast_le_one.2 (NNRat.minOneDiv_le_one _ _))
      (cut.coe_shape_le_one c))).trans_eq
    (Finset.expect_const univ_nonempty 1)

/-- **The column deviations with the mean shape**: when every mean of the flattened weight times
the shape is positive, `signerRegDev ≤ signerRegGap · K · top · |V| · s̄`, `s̄` the mean shape,
since each of those means is at most `s̄`. -/
theorem signerRegDev_le_meanShape (hp : SigningParams p) {cut : Cutoff p}
    (hβ0 : (cut.top : ℝ≥0∞) ≠ 0) (hβt : (cut.top : ℝ≥0∞) ≠ ⊤)
    (hm : ∀ v, 0 < 𝔼 c,
      ((flatWeight prims cut sk.t0 (v, c) : ℝ≥0∞) * (cut.shape c : ℝ≥0∞)).toReal) :
    signerRegDev prims sk aHat ≤
      signerRegGap prims sk aHat cut *
        ((standinScale p * cut.top).toReal * Fintype.card (BucketVec p) * cut.meanShape) := by
  have hpos : 0 < (standinScale p * cut.top).toReal * Fintype.card (BucketVec p) :=
    mul_pos (flatLevel_pos hp hβ0 hβt) (Nat.cast_pos.2 Fintype.card_pos)
  rw [← mul_assoc, signerRegGap, div_mul_cancel₀ _ hpos.ne', signerRegDev, sum_mul]
  refine sum_le_sum fun v _ => ?_
  rw [div_mul_eq_mul_div, le_div_iff₀ (hm v)]
  refine mul_le_mul_of_nonneg_left ?_ (Finset.expect_nonneg fun _ _ => abs_nonneg _)
  refine Finset.expect_le_expect fun c _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_nnratCast, ENNReal.toReal_nnratCast]
  refine mul_le_of_le_one_left (NNRat.cast_nonneg _) ?_
  exact_mod_cast NNRat.minOneDiv_le_one _ _

/-- `signerRegDev_le` at a constant cut-off `β`, where the shape is one. -/
theorem signerRegDev_le_const (hp : SigningParams p) {β : ℚ≥0} (hβ0 : (β : ℝ≥0∞) ≠ 0)
    (hβt : (β : ℝ≥0∞) ≠ ⊤)
    (hm : ∀ v, 0 < 𝔼 c, (flatWeight prims (Cutoff.const β) sk.t0 (v, c) : ℝ≥0∞).toReal) :
    signerRegDev prims sk aHat ≤
      signerRegGap prims sk aHat (Cutoff.const β) *
        ((standinScale p * β).toReal * Fintype.card (BucketVec p)) :=
  signerRegDev_le prims sk aHat hp hβ0 hβt fun v => by
    simpa only [ENNReal.nnratCast_one, mul_one] using hm v

/-- **The mass of a keep factor** over a fresh `(c̃, z)`, summed over `w₁`:
`∑_{(v, c, z)} g / |C × Z|`. -/
noncomputable def keepMass (g : KeepFactor p Z) : ℝ :=
  (∑ a, (g.val a).toReal) / Fintype.card (CommitHashBytes p × Z)

variable (cut : Cutoff p) (g : KeepFactor p Z)

/-- **The real attempt keeps** with positive probability. -/
def FlatKeeps : Prop :=
  flatAttempt prims sk aHat cut g none ≠ 1

omit [Nonempty (MaskBox p)] in
/-- **The scaled stand-in keep mass under the floor**: `ρ_z · ∑ standinFlatAttempt (some ·)` is at
least `K · top · (1 - ε) · keepMass (shape · g)`. Scaled by `ρ_z`, the stand-in kept mass at
`(v, c̃, z)` is `K · top · flatKeptWeight (shape · g) / |C × Z|`
(`zAcceptFraction_mul_standinMass_mul_flattenCoin`), and the floor bounds the kept weights below
(`KeyFloorOn.one_sub_mul_le_sum_flatKeptWeight`). -/
theorem le_zAcceptFraction_mul_sum_standinFlatAttempt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloorOn prims (cut.keep g) cut ε sk.t0) :
    (standinScale p * cut.top).toReal * ((1 - ε) * keepMass (cut.keep g)) ≤
      (zAcceptFraction p).toReal * ∑ a, (standinFlatAttempt prims sk cut g (some a)).toReal := by
  set κ : BucketVec p × CommitHashBytes p → ℝ≥0∞ := fun a => (flattenCoin prims sk cut a : ℝ≥0∞)
  set A₁ := standinFlatAttempt prims sk cut g
  set ρ := (zAcceptFraction p).toReal
  set CZ : ℝ := (Fintype.card (CommitHashBytes p × Z) : ℝ)
  set K := (standinScale p).toReal
  set β := (cut.top : ℝ≥0∞).toReal
  have h1 : ∀ a : BucketVec p × CommitHashBytes p × Z, ρ * (A₁ (some a)).toReal =
      (zAcceptFraction p * standinMass prims sk a.1 a.2.1).toReal * CZ⁻¹ *
        (κ (a.1, a.2.1) * g.val a).toReal := fun a => by
    obtain ⟨v, c, z⟩ := a
    rw [show A₁ = standinFlatAttempt prims sk cut g from rfl, standinFlatAttempt,
      freshAttemptWith_apply_some, standinMass]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ρ, CZ, κ]
    ring
  have h1' : ∀ a : BucketVec p × CommitHashBytes p × Z,
      (zAcceptFraction p * standinMass prims sk a.1 a.2.1).toReal *
        (κ (a.1, a.2.1) * g.val a).toReal =
      K * β * (flatKeptWeight prims cut sk.t0 (cut.keep g) a).toReal := fun a => by
    rw [← ENNReal.toReal_mul, ← mul_assoc,
      zAcceptFraction_mul_standinMass_mul_flattenCoin prims sk hp h_laws hs2 cut,
      flatKeptWeight, Cutoff.keep]
    simp only [ENNReal.toReal_mul, K, β]
    ring
  have hden : ρ * ∑ a, (A₁ (some a)).toReal =
      K * β * (∑ a, (flatKeptWeight prims cut sk.t0 (cut.keep g) a).toReal) * CZ⁻¹ := by
    rw [mul_sum, mul_sum, sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [h1, mul_right_comm, h1']
  rw [hden, ENNReal.toReal_mul, keepMass, mul_assoc (K * β), ← mul_div_assoc, div_eq_mul_inv]
  gcongr
  exact hf.one_sub_mul_le_sum_flatKeptWeight hp

/-- **The real and the scaled stand-in accepted masses differ by at most `signerRegDev`**: at
`(v, c̃, z)` by at most `|realMass - ρ_z · standinMass| / |C × Z|`, since the keep coin and `g` are
at most one. -/
theorem sum_abs_flatAttempt_sub_le :
    ∑ a, |(flatAttempt prims sk aHat cut g (some a)).toReal -
        (zAcceptFraction p).toReal * (standinFlatAttempt prims sk cut g (some a)).toReal| ≤
      signerRegDev prims sk aHat := by
  set κ : BucketVec p × CommitHashBytes p → ℝ≥0∞ := fun a => (flattenCoin prims sk cut a : ℝ≥0∞)
  set A₀ := flatAttempt prims sk aHat cut g
  set A₁ := standinFlatAttempt prims sk cut g
  set ρ := (zAcceptFraction p).toReal
  set CZ : ℝ := (Fintype.card (CommitHashBytes p × Z) : ℝ)
  have hCZ : 0 < CZ := Nat.cast_pos.2 Fintype.card_pos
  have hκg1 : ∀ a : BucketVec p × CommitHashBytes p × Z, (κ (a.1, a.2.1) * g.val a).toReal ≤ 1 :=
    fun a => ENNReal.toReal_le_one_of_le_one
      (mul_le_one' (coe_flattenCoin_le_one prims sk cut _) (g.le_one a))
  have h0 : ∀ a : BucketVec p × CommitHashBytes p × Z, (A₀ (some a)).toReal =
      (realMass prims sk aHat a.1 a.2.1).toReal * CZ⁻¹ * (κ (a.1, a.2.1) * g.val a).toReal :=
    fun a => by
      obtain ⟨v, c, z⟩ := a
      rw [show A₀ = flatAttempt prims sk aHat cut g from rfl, flatAttempt,
        freshAttemptWith_apply_some, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, realMass]
  have h1 : ∀ a : BucketVec p × CommitHashBytes p × Z, ρ * (A₁ (some a)).toReal =
      (zAcceptFraction p * standinMass prims sk a.1 a.2.1).toReal * CZ⁻¹ *
        (κ (a.1, a.2.1) * g.val a).toReal := fun a => by
    obtain ⟨v, c, z⟩ := a
    rw [show A₁ = standinFlatAttempt prims sk cut g from rfl, standinFlatAttempt,
      freshAttemptWith_apply_some, standinMass]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ρ, CZ, κ]
    ring
  have hterm : ∀ a : BucketVec p × CommitHashBytes p × Z,
      |(A₀ (some a)).toReal - ρ * (A₁ (some a)).toReal| ≤
        |(realMass prims sk aHat a.1 a.2.1).toReal -
          (zAcceptFraction p * standinMass prims sk a.1 a.2.1).toReal| * CZ⁻¹ := fun a => by
    rw [h0, h1, ← sub_mul, ← sub_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hCZ),
      abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (inv_pos.2 hCZ).le) (hκg1 a)
  refine (sum_le_sum fun a _ => hterm a).trans_eq ?_
  rw [signerRegDev, Fintype.sum_prod_type]
  refine sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type, Fintype.expect_eq_sum_div_card, sum_div]
  refine sum_congr rfl fun c _ => ?_
  dsimp only
  rw [sum_const, card_univ, nsmul_eq_mul]
  simp only [CZ, Fintype.card_prod, Nat.cast_mul]
  have hZ : (Fintype.card Z : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

/-- **The keep probability of the real attempt under the floor**: at least
`K · top · (1 - ε) · keepMass (shape · g) - signerRegDev`
(`le_zAcceptFraction_mul_sum_standinFlatAttempt`, `sum_abs_flatAttempt_sub_le`). -/
theorem sub_signerRegDev_le_toReal_one_sub_flatAttempt (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloorOn prims (cut.keep g) cut ε sk.t0) :
    (standinScale p * cut.top).toReal * ((1 - ε) * keepMass (cut.keep g)) -
        signerRegDev prims sk aHat ≤
      (1 - flatAttempt prims sk aHat cut g none).toReal := by
  rw [← sum_toReal_apply_some]
  have h1 := le_zAcceptFraction_mul_sum_standinFlatAttempt prims sk cut g hp h_laws hs2 hf
  have h2 := sum_abs_flatAttempt_sub_le prims sk aHat cut g
  have h3 : (zAcceptFraction p).toReal *
        ∑ a, (standinFlatAttempt prims sk cut g (some a)).toReal -
      ∑ a, (flatAttempt prims sk aHat cut g (some a)).toReal ≤
      ∑ a, |(flatAttempt prims sk aHat cut g (some a)).toReal -
        (zAcceptFraction p).toReal * (standinFlatAttempt prims sk cut g (some a)).toReal| := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_le_sum fun a _ => by rw [abs_sub_comm]; exact le_abs_self _
  linarith

/-- **The real attempt keeps** when the column deviations are below the scaled keep mass
`K · top · (1 - ε) · keepMass (shape · g)` (`sub_signerRegDev_le_toReal_one_sub_flatAttempt`). -/
theorem flatKeeps_of_signerRegDev_lt (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ} (hf : KeyFloorOn prims (cut.keep g) cut ε sk.t0)
    (h : signerRegDev prims sk aHat <
      (standinScale p * cut.top).toReal * ((1 - ε) * keepMass (cut.keep g))) :
    FlatKeeps prims sk aHat cut g := by
  intro h1
  have := sub_signerRegDev_le_toReal_one_sub_flatAttempt prims sk aHat cut g hp h_laws hs2 hf
  rw [h1, tsub_self, ENNReal.toReal_zero] at this
  linarith

/-- **The real and the stand-in kept laws, for every keep factor.** Under the floor relative to
`shape · g` and when the real attempt keeps, the law of `(w₁, c̃, z)` with `y` uniform on the mask
box is within `signerRegDev / (K · top · (1 - ε) · keepMass (shape · g))` of the stand-in law with
`w` uniform (`tvDist_condSome_le_scaled` with `sum_abs_flatAttempt_sub_le` and
`le_zAcceptFraction_mul_sum_standinFlatAttempt`). -/
theorem tvDist_flatKeptLaw_standinFlatKeptLaw_le_of_keyFloorOn (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta) {ε : ℝ}
    (hf : KeyFloorOn prims (cut.keep g) cut ε sk.t0) (hkeep : FlatKeeps prims sk aHat cut g) :
    tvDist (flatKeptLaw prims sk aHat cut g) (standinFlatKeptLaw prims sk cut g) ≤
      signerRegDev prims sk aHat /
        ((standinScale p * cut.top).toReal * ((1 - ε) * keepMass (cut.keep g))) := by
  have hden_ge := le_zAcceptFraction_mul_sum_standinFlatAttempt prims sk cut g hp h_laws hs2 hf
  have hCZ : (0 : ℝ) < Fintype.card (CommitHashBytes p × Z) := Nat.cast_pos.2 Fintype.card_pos
  have hdenpos : 0 < (standinScale p * cut.top).toReal * ((1 - ε) * keepMass (cut.keep g)) :=
    mul_pos (flatLevel_pos hp hf.cutoff_ne_zero hf.cutoff_ne_top)
      (mul_pos (by linarith [hf.lt_one]) (div_pos hf.sum_toReal_pos hCZ))
  have hk₁ : standinFlatAttempt prims sk cut g none ≠ 1 := by
    intro h
    have hz : ∑ a, (standinFlatAttempt prims sk cut g (some a)).toReal = 0 :=
      sum_eq_zero fun a _ => by
        rw [apply_some_eq_zero_of_apply_none_eq_one h a, ENNReal.toReal_zero]
    rw [hz, mul_zero] at hden_ge
    linarith
  rw [FlatKeeps] at hkeep
  rw [flatKeptLaw, standinFlatKeptLaw, condSomeOr_of_ne _ hkeep, condSomeOr_of_ne _ hk₁]
  refine (tvDist_condSome_le_scaled _ _ hkeep hk₁ (zAcceptFraction_pos hp)).trans ?_
  exact div_le_div₀ (signerRegDev_nonneg prims sk aHat) (sum_abs_flatAttempt_sub_le prims sk aHat
    cut g) hdenpos hden_ge

/-! ### No side data and the unit keep factor -/

omit [Nonempty (MaskBox p)] in
/-- **The stand-in kept law with no side data and the unit keep factor** is `standinKeptLaw`. -/
theorem map_standinFlatKeptLaw_one :
    (standinFlatKeptLaw prims sk cut (KeepFactor.one : KeepFactor p Unit)).map
        (dropUnitEquiv _ _) = standinKeptLaw prims sk cut := by
  rw [standinFlatKeptLaw, ← condSomeOr_map_optionMap, map_uniformOfFintype_equiv, standinKeptLaw,
    standinFlatAttempt]
  exact congrArg (condSomeOr · _) (map_freshAttemptWith_unit _ _ _ _ _)

/-- **The real kept law with no side data and the unit keep factor** is `realKeptLaw`. -/
theorem map_flatKeptLaw_one :
    (flatKeptLaw prims sk aHat cut (KeepFactor.one : KeepFactor p Unit)).map
        (dropUnitEquiv _ _) = realKeptLaw prims sk aHat cut := by
  rw [flatKeptLaw, ← condSomeOr_map_optionMap, map_uniformOfFintype_equiv, realKeptLaw,
    flatAttempt]
  exact congrArg (condSomeOr · _) (map_freshAttemptWith_unit _ _ _ _ _)

/-- **The unit keep factor rejects as often as the signer's fresh attempt.** -/
theorem flatAttempt_one_apply_none :
    flatAttempt prims sk aHat cut (KeepFactor.one : KeepFactor p Unit) none =
      freshAttempt (maskUniform p) (realBuckets aHat) (attemptAccept prims sk aHat)
        (fun a => (flattenCoin prims sk cut a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk cut)
        none := by
  rw [← map_freshAttemptWith_unit, flatAttempt,
    show (Option.map (dropUnitEquiv (BucketVec p) (CommitHashBytes p)) :
      Option (BucketVec p × CommitHashBytes p × Unit) → Option (BucketVec p × CommitHashBytes p)) =
      Equiv.optionCongr (dropUnitEquiv _ _) from rfl, map_equiv_apply]
  rfl

/-- **The unit keep factor keeps** exactly when the signer's fresh attempt keeps (`SignerKeeps`). -/
theorem flatKeeps_one_iff :
    FlatKeeps prims sk aHat cut (KeepFactor.one : KeepFactor p Unit) ↔
      SignerKeeps prims sk aHat cut := by
  rw [FlatKeeps, SignerKeeps, flatAttempt_one_apply_none]

omit nttOps [Nonempty (MaskBox p)] in
/-- The mass of the unit keep factor without side data is the number of bucket vectors. -/
theorem keepMass_one :
    keepMass (KeepFactor.one : KeepFactor p Unit) = Fintype.card (BucketVec p) := by
  rw [keepMass]
  simp only [KeepFactor.one, ENNReal.toReal_one, sum_const, card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_prod, Fintype.card_unit, Nat.cast_mul]
  have hC : (Fintype.card (CommitHashBytes p) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
/-- The mass of the keep factor `shape` without side data is the number of bucket vectors times
the mean shape. -/
theorem keepMass_keep_one :
    keepMass (cut.keep (KeepFactor.one : KeepFactor p Unit)) =
      Fintype.card (BucketVec p) * cut.meanShape := by
  rw [keepMass, Cutoff.meanShape, Fintype.expect_eq_sum_div_card]
  simp only [Cutoff.keep, KeepFactor.one, mul_one, ENNReal.toReal_nnratCast,
    Fintype.sum_prod_type, Finset.univ_unique, sum_const, card_univ, nsmul_eq_mul,
    Fintype.card_prod, Fintype.card_unit, Finset.card_singleton, Nat.cast_one, one_mul]
  ring

end GordieHowe.MLDSA
