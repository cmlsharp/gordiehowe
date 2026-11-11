-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Flatten
public import GordieHowe.Foundations.ToMathlib.PMFOracleQuenched

@[expose] public section

/-!
# The weights and masses of the flattened ML-DSA signer

The single-key flattened signer (FIPS 204 attempts with `y` uniform on the mask box, the four
checks of Algorithm 7, and the keep coin `min(1, val(c̃) / aw)` for a public cut-off `val`,
`Cutoff`), the core that the credential presentations of
`GordieHowe/Applications/MLDSA/Flattened/` and the ring signer of
`GordieHowe/Applications/MLDSA/Signing/RingSigner.lean` instantiate.

* `t0Weight`, `flatWeight`: the uniform-`w` acceptance weight `aw` of the ct₀ and hint checks for
  a `t₀`, rational (`coe_t0Weight`), and the fill fraction `min(1, aw / val(c̃))`
  (`coe_flatWeight`, `t0Weight_le_flatWeight`).
* `mul_flattenCoin_eq`: `aw · min(1, val / aw) = top · (min(1, aw / val) · shape)`, both
  `min(aw, val)` for `val = top · shape`.
* `checkWeight`, `checkDefect`: the bucket-free lower bound of `aw` (`checkWeight_le_t0Weight`),
  where it reaches `val(c̃)` the fill fraction is one (`flatWeight_eq_one_of_le_checkWeight`), and
  the probability over a uniform `c̃` that it is below `val(c̃)`; the mean fill fraction is at
  least `1 - checkDefect` (`one_sub_checkDefect_le_expect_flatWeight`).
* `zAcceptFraction`, `uniformScale`, `standinScale`: the z-acceptance fraction `ρ_z`, the
  uniform-`w` scale and their product `K` (`maskUniform_zCheck_eq`).
* `flatLoopSigner`: the signer as a `PMF.LoopSigner`, with level `K · top` (`flatLevel_pos`).
* `realMass`, `standinMass`, `signerRegGap`: the real and the stand-in accepted masses and the
  regularity gap of the signer, the column-wise distance between the real mass and `ρ_z` times the
  stand-in mass relative to the mean of the fill fraction times the shape; it depends on the
  signer's key only.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA44 Finset PMF
open scoped ENNReal BigOperators
open LatticeCrypto TransformOps

/-! ### The weights -/

section Weights

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]

/-- **The acceptance weight of a published `t₀`** at `(w₁, c̃)`: the uniform-`w` acceptance
weight of the ct₀ and hint checks of FIPS 204 Algorithm 7 line 28 with `b = SampleInBall(c̃)·t₀`
(`acceptWeight`). The signer's flattening weight is that of its own `t₀`
(`signerWeight_eq_t0Weight`). -/
def t0Weight (t0 : RqVec p.k) (vc : BucketVec p × CommitHashBytes p) : ℚ≥0 :=
  (acceptWeightQ p.gamma2 p.beta p.omega (centeredCoeffs (prims.sampleInBall vc.2 • t0))
    fun x => (vc.1 x).val).toNNRat

omit [NeZero (bucketCount p)] in
/-- The acceptance weight of a published `t₀` in `ℝ≥0∞` is the real acceptance weight. -/
theorem coe_t0Weight (t0 : RqVec p.k) (vc : BucketVec p × CommitHashBytes p) :
    (t0Weight prims t0 vc : ℝ≥0∞) = ENNReal.ofReal (acceptWeight p.gamma2 p.beta p.omega
      (centeredCoeffs (prims.sampleInBall vc.2 • t0)) fun x => (vc.1 x).val) := by
  rw [t0Weight, ← ENNReal.ofReal_ratCast, cast_acceptWeightQ]

omit [NeZero (bucketCount p)] in
theorem signerWeight_eq_t0Weight (sk : SecretKey p) :
    signerWeight prims sk = t0Weight prims sk.t0 :=
  rfl

/-- **The flattened weight** (the fill fraction) `min(1, aw / val(c̃))` of a `t₀` at the cut-off
`val` (`NNRat.minOneDiv`, the value of `ℝ≥0∞` at `val(c̃) = 0`). -/
def flatWeight (cut : Cutoff p) (t0 : RqVec p.k) (vc : BucketVec p × CommitHashBytes p) : ℚ≥0 :=
  NNRat.minOneDiv (t0Weight prims t0 vc) (cut.val vc.2)

omit [NeZero (bucketCount p)] in
/-- The flattened weight in `ℝ≥0∞` is `min(1, aw / val(c̃))`. -/
theorem coe_flatWeight (cut : Cutoff p) (t0 : RqVec p.k) (vc : BucketVec p × CommitHashBytes p) :
    (flatWeight prims cut t0 vc : ℝ≥0∞) =
      min 1 ((t0Weight prims t0 vc : ℝ≥0∞) / (cut.val vc.2 : ℝ≥0∞)) :=
  ENNReal.nnratCast_minOneDiv _ _

omit [NeZero (bucketCount p)] in
/-- **The flattened weight is at least the acceptance weight** for `top ≤ 1`:
`aw ≤ min(1, aw / val(c̃))`, since `aw ≤ 1` (`acceptWeight_le_one`) and `val(c̃) ≤ top`. -/
theorem t0Weight_le_flatWeight (hp : SigningParams p) {cut : Cutoff p}
    (hβ : (cut.top : ℝ≥0∞) ≤ 1) (t0 : RqVec p.k) (vc : BucketVec p × CommitHashBytes p) :
    (t0Weight prims t0 vc : ℝ≥0∞) ≤ (flatWeight prims cut t0 vc : ℝ≥0∞) := by
  rw [coe_flatWeight]
  refine le_min ?_ ((div_one _).symm.le.trans
    (ENNReal.div_le_div_left (cut.coe_val_le_one hβ vc.2) _))
  rw [coe_t0Weight]
  exact ENNReal.ofReal_le_one.2 (acceptWeight_le_one hp.beta_lt_gamma2 _ _ _)

omit [NeZero (bucketCount p)] in
/-- `t0Weight_le_flatWeight` in `ℝ`. -/
theorem toReal_t0Weight_le_flatWeight (hp : SigningParams p) {cut : Cutoff p}
    (hβ : (cut.top : ℝ≥0∞) ≤ 1) (t0 : RqVec p.k) (vc : BucketVec p × CommitHashBytes p) :
    (t0Weight prims t0 vc : ℝ≥0∞).toReal ≤ (flatWeight prims cut t0 vc : ℝ≥0∞).toReal :=
  ENNReal.toReal_mono (ENNReal.nnratCast_ne_top _) (t0Weight_le_flatWeight prims hp hβ t0 vc)

omit nttOps in
/-- `x · min(1, y / x) = min x y` for finite `x`. -/
theorem _root_.ENNReal.mul_min_one_div {x y : ℝ≥0∞} (hx : x ≠ ⊤) : x * min 1 (y / x) = min x y := by
  by_cases h0 : x = 0
  · simp [h0]
  have hm : Monotone fun t : ℝ≥0∞ => x * t := fun _ _ h => by dsimp only; gcongr
  rw [hm.map_min, mul_one, ENNReal.mul_div_cancel h0 hx]

omit [NeZero (bucketCount p)] in
/-- **The signer's flattening coin against its flattened weight**:
`aw_i · min(1, val / aw_i) = top · (min(1, aw_i / val) · shape)`, both `min(aw_i, val)` for
`val = top · shape`. -/
theorem mul_flattenCoin_eq (sk : SecretKey p) (cut : Cutoff p)
    (vc : BucketVec p × CommitHashBytes p) :
    (signerWeight prims sk vc : ℝ≥0∞) * (flattenCoin prims sk cut vc : ℝ≥0∞) =
      (cut.top : ℝ≥0∞) * ((flatWeight prims cut sk.t0 vc : ℝ≥0∞) * (cut.shape vc.2 : ℝ≥0∞)) := by
  rw [coe_flattenCoin, ENNReal.mul_min_one_div (ENNReal.nnratCast_ne_top _), mul_comm
    (flatWeight prims cut sk.t0 vc : ℝ≥0∞), ← mul_assoc, ← cut.coe_val, coe_flatWeight,
    ENNReal.mul_min_one_div (ENNReal.nnratCast_ne_top _), min_comm]
  rfl

end Weights

/-! ### The check weight -/

section Check

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)]

open LatticeCrypto TransformOps in
/-- **The check weight of a published `t₀`** at the commitment hash `c̃`: the bucket-free
acceptance weight `acceptWeightLower` of the shift `b = SampleInBall(c̃)·t₀`, at most the
acceptance weight `t0Weight` in every bucket vector (`checkWeight_le_t0Weight`). -/
def checkWeight (t0 : RqVec p.k) (cTilde : CommitHashBytes p) : ℚ≥0 :=
  (acceptWeightLowerQ p.gamma2 p.beta p.omega
    (centeredCoeffs (prims.sampleInBall cTilde • t0))).toNNRat

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
open LatticeCrypto TransformOps in
/-- The check weight in `ℝ≥0∞` is the real bucket-free acceptance weight. -/
theorem coe_checkWeight (t0 : RqVec p.k) (cTilde : CommitHashBytes p) :
    (checkWeight prims t0 cTilde : ℝ≥0∞) = ENNReal.ofReal (acceptWeightLower p.gamma2 p.beta
      p.omega (centeredCoeffs (prims.sampleInBall cTilde • t0))) := by
  rw [checkWeight, ← ENNReal.ofReal_ratCast, cast_acceptWeightLowerQ]

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- The check weight is at most the acceptance weight in every bucket vector
(`acceptWeightLower_le_acceptWeight`). -/
theorem checkWeight_le_t0Weight (hp : SigningParams p) (t0 : RqVec p.k)
    (vc : BucketVec p × CommitHashBytes p) :
    (checkWeight prims t0 vc.2 : ℝ≥0∞) ≤ (t0Weight prims t0 vc : ℝ≥0∞) := by
  rw [coe_checkWeight, coe_t0Weight]
  exact ENNReal.ofReal_le_ofReal (acceptWeightLower_le_acceptWeight hp.beta_lt_gamma2 _ _ _)

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- **The flattened weight is one where the check weight reaches the cut-off**: for a positive
level and `val(c̃) ≤ checkWeight(t₀, c̃)`, `min(1, aw / val(c̃)) = 1` in every bucket vector. -/
theorem flatWeight_eq_one_of_le_checkWeight (hp : SigningParams p) {cut : Cutoff p}
    (hβ0 : (cut.top : ℝ≥0∞) ≠ 0) {t0 : RqVec p.k} {vc : BucketVec p × CommitHashBytes p}
    (h : cut.val vc.2 ≤ checkWeight prims t0 vc.2) : flatWeight prims cut t0 vc = 1 := by
  rw [← ENNReal.nnratCast_inj, coe_flatWeight, ENNReal.nnratCast_one]
  exact le_antisymm (min_le_left _ _) (le_min le_rfl
    ((ENNReal.div_self (cut.coe_val_ne_zero hβ0 vc.2) (ENNReal.nnratCast_ne_top _)).symm.le.trans
    (ENNReal.div_le_div_right ((ENNReal.nnratCast_le_nnratCast.2 h).trans
      (checkWeight_le_t0Weight prims hp t0 vc)) _)))

/-- **The check defect of a published `t₀`** at the cut-off `val`: the probability over a
uniform commitment hash `c̃` that the check weight is below `val(c̃)`. -/
noncomputable def checkDefect (cut : Cutoff p) (t0 : RqVec p.k) : ℝ :=
  𝔼 cTilde : CommitHashBytes p, if checkWeight prims t0 cTilde < cut.val cTilde then 1 else 0

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- The check defect is a probability. -/
theorem checkDefect_le_one (cut : Cutoff p) (t0 : RqVec p.k) : checkDefect prims cut t0 ≤ 1 :=
  (Finset.expect_le_expect fun _ _ => by split_ifs <;> norm_num).trans_eq
    (Finset.expect_const univ_nonempty 1)

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- The check defect is nonnegative. -/
theorem checkDefect_nonneg (cut : Cutoff p) (t0 : RqVec p.k) : 0 ≤ checkDefect prims cut t0 :=
  Finset.expect_nonneg fun _ _ => by split_ifs <;> norm_num

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- **The mean flattened weight of a `t₀` is at least one minus its check defect**, in
every bucket vector: `1 - checkDefect cut t₀ ≤ 𝔼_c min(1, aw(t₀, v, c) / val(c))`
(`flatWeight_eq_one_of_le_checkWeight`). -/
theorem one_sub_checkDefect_le_expect_flatWeight (hp : SigningParams p) {cut : Cutoff p}
    (hβ0 : (cut.top : ℝ≥0∞) ≠ 0) (t0 : RqVec p.k) (v : BucketVec p) :
    1 - checkDefect prims cut t0 ≤
      𝔼 c : CommitHashBytes p, (flatWeight prims cut t0 (v, c) : ℝ≥0∞).toReal := by
  rw [checkDefect]
  have h1 : (1 : ℝ) - 𝔼 c : CommitHashBytes p,
      (if checkWeight prims t0 c < cut.val c then 1 else 0 : ℝ) =
        𝔼 c : CommitHashBytes p,
          (1 - if checkWeight prims t0 c < cut.val c then 1 else 0 : ℝ) := by
    rw [Finset.expect_sub_distrib, Finset.expect_const univ_nonempty]
  rw [h1]
  refine Finset.expect_le_expect fun c _ => ?_
  split_ifs with h
  · rw [sub_self]
    exact ENNReal.toReal_nonneg
  · rw [flatWeight_eq_one_of_le_checkWeight prims hp hβ0 (vc := (v, c)) (not_lt.1 h)]
    simp

end Check

/-! ### The signer -/

section Signer

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] (sk : SecretKey p) (aHat : TqMatrix p.k p.l)

/-- **The z-acceptance fraction** `ρ_z = ((2(γ₁ - β) - 1) / (2γ₁))^(256 l)`: the probability that a
mask `y` uniform on the mask box passes the z-check `‖y + c·s₁‖∞ < γ₁ - β` (FIPS 204 Algorithm 7
line 23), the same for every challenge and every shift with `‖c·s₁‖∞ ≤ β`
(`maskUniform_zCheck_eq`). -/
noncomputable def zAcceptFraction (p : Params) : ℝ≥0∞ :=
  ENNReal.ofReal ((((2 * (p.gamma1 - p.beta) - 1 : ℕ) : ℝ) / (2 * p.gamma1 : ℕ)) ^
    (ringDegree * p.l))

/-- **The uniform-`w` scale** `((2(γ₂ - β) - 1) / q)^(256 k)`: the stand-in accepted mass of
`(w₁, c̃)` is this times the flattening weight (`SigningLaws.signerMass_standin`). -/
noncomputable def uniformScale (p : Params) : ℝ≥0∞ :=
  ENNReal.ofReal ((((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) / modulus) ^ Fintype.card (CoeffIndex p))

/-- **The stand-in scale** `K = ρ_z · ((2(γ₂ - β) - 1) / q)^(256 k)`: the z-acceptance fraction
times the uniform-`w` scale. The real accepted mass of `(w₁, c̃)` is compared with `ρ_z` times
the stand-in mass, which is `K` times the flattening weight. -/
noncomputable def standinScale (p : Params) : ℝ≥0∞ :=
  zAcceptFraction p * uniformScale p

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
theorem zAcceptFraction_pos (hp : SigningParams p) : 0 < (zAcceptFraction p).toReal := by
  have h1 : 0 < 2 * (p.gamma1 - p.beta) - 1 := by have := hp.beta_lt_gamma1; omega
  have h2 : 0 < 2 * p.gamma1 := by have := hp.beta_lt_gamma1; omega
  have hK : 0 < (((2 * (p.gamma1 - p.beta) - 1 : ℕ) : ℝ) / (2 * p.gamma1 : ℕ)) ^
      (ringDegree * p.l) := pow_pos (div_pos (by exact_mod_cast h1) (by exact_mod_cast h2)) _
  rw [zAcceptFraction, ENNReal.toReal_ofReal hK.le]
  exact hK

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
theorem uniformScale_pos (hp : SigningParams p) : 0 < (uniformScale p).toReal := by
  have h1 : 0 < 2 * (p.gamma2 - p.beta) - 1 := by have := hp.beta_lt_gamma2; omega
  have hK : 0 < (((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) / modulus) ^ Fintype.card (CoeffIndex p) :=
    pow_pos (div_pos (by exact_mod_cast h1) (by norm_num [modulus])) _
  rw [uniformScale, ENNReal.toReal_ofReal hK.le]
  exact hK

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
theorem standinScale_pos (hp : SigningParams p) : 0 < (standinScale p).toReal := by
  rw [standinScale, ENNReal.toReal_mul]
  exact mul_pos (zAcceptFraction_pos hp) (uniformScale_pos hp)

omit [NeZero (bucketCount p)] nttOps in
/-- **The z-check passes with probability `ρ_z`** for every shift `v` with `‖v‖∞ ≤ β`
(`zCheck_vec_card`, `card_maskBox`). -/
theorem maskUniform_zCheck_eq (hp : SigningParams p) (v : RqVec p.l)
    (hv : polyVecNorm v ≤ p.beta) :
    (maskUniform p).toOuterMeasure {y | zCheck (p := p) (y.1 + v) = true} = zAcceptFraction p := by
  classical
  have hq := hp.two_gamma1_lt
  have hset : {y : MaskBox p | zCheck (p := p) (y.1 + v) = true} =
      ↑(Finset.univ.filter fun y : MaskBox p => zCheck (p := p) (y.1 + v) = true) := by
    ext y; simp
  have hcard : (Finset.univ.filter fun y : MaskBox p => zCheck (p := p) (y.1 + v) = true).card =
      (2 * (p.gamma1 - p.beta) - 1) ^ (ringDegree * p.l) := by
    rw [← zCheck_vec_card hp.beta_lt_gamma1 hp.gamma1_beta_lt v hv, ← Fintype.card_subtype,
      ← Nat.card_eq_fintype_card]
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (InMaskBox p.gamma1)
      fun y => zCheck (p := p) (y + v) = true).trans (Equiv.subtypeEquivRight fun y => ?_))
    simp [zCheck, InMaskBox]
  rw [hset, PMF.toOuterMeasure_apply_finset, maskUniform]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, hcard,
    card_maskBox hq]
  have h2 : (0 : ℝ) < (2 * p.gamma1 : ℕ) := by
    have := hp.beta_lt_gamma1; exact_mod_cast (by omega : 0 < 2 * p.gamma1)
  rw [zAcceptFraction, ENNReal.ofReal_pow (div_nonneg (Nat.cast_nonneg _) h2.le),
    ENNReal.ofReal_div_of_pos h2, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    div_eq_mul_inv, mul_pow ((2 * (p.gamma1 - p.beta) - 1 : ℕ) : ℝ≥0∞) ((2 * p.gamma1 : ℕ) : ℝ≥0∞)⁻¹,
    ← ENNReal.inv_pow, Nat.cast_pow, Nat.cast_pow]

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
/-- The level `K · top` of the flattened signer is positive. -/
theorem flatLevel_pos (hp : SigningParams p) {cut : Cutoff p} (hβ0 : (cut.top : ℝ≥0∞) ≠ 0)
    (hβt : (cut.top : ℝ≥0∞) ≠ ⊤) :
    0 < (standinScale p * cut.top).toReal := by
  rw [ENNReal.toReal_mul]
  exact mul_pos (standinScale_pos hp) (ENNReal.toReal_pos hβ0 hβt)

/-- **The flattened ML-DSA signer** as a loop signer: `y` uniform on the mask box, commitment
`w₁ = HighBits(Â·y)`, acceptance the four checks of FIPS 204 Algorithm 7, the flattening coin
`min(1, val(c̃) / aw_i)`, and level `K · top`. -/
@[reducible]
noncomputable def flatLoopSigner (hp : SigningParams p) {cut : Cutoff p}
    (hβ0 : (cut.top : ℝ≥0∞) ≠ 0) (hβt : (cut.top : ℝ≥0∞) ≠ ⊤) :
    PMF.LoopSigner (BucketVec p) (CommitHashBytes p) where
  Y := MaskBox p
  P := maskUniform p
  w1 := realBuckets aHat
  acc := attemptAccept prims sk aHat
  κ a := (flattenCoin prims sk cut a : ℝ≥0∞)
  hκ := coe_flattenCoin_le_one prims sk cut
  β := (standinScale p * cut.top).toReal
  hβ := flatLevel_pos hp hβ0 hβt

/-- The real accepted mass of `(w₁, c̃)`: `Pr_y[HighBits(Â·y) = v ∧ the four checks pass at c̃]`. -/
noncomputable def realMass (v : BucketVec p) (cTilde : CommitHashBytes p) : ℝ≥0∞ :=
  signerMass (maskUniform p) (realBuckets aHat) (attemptAccept prims sk aHat) v cTilde

/-- The uniform-`w` stand-in accepted mass of `(w₁, c̃)` (no z-check). -/
noncomputable def standinMass (v : BucketVec p) (cTilde : CommitHashBytes p) : ℝ≥0∞ :=
  signerMass (uniformOfFintype (CoeffIndex p → Coeff)) bucketsOf (standinAccept prims sk) v cTilde

/-- **The regularity gap of the signer** at the cut-off `val = top · shape`: the column-wise ℓ1
distance `∑_v 𝔼_c |realMass v c - ρ_z · standinMass v c|` between the real accepted mass and the
stand-in mass scaled by the z-acceptance fraction `ρ_z`, each column relative to the signer's
mean `𝔼_c min(1, aw / val(c)) · shape(c)`, over `K · top · |V|`. -/
noncomputable def signerRegGap (cut : Cutoff p) : ℝ :=
  (∑ v, (𝔼 c, |(realMass prims sk aHat v c).toReal -
      (zAcceptFraction p * standinMass prims sk v c).toReal|) /
      𝔼 c, ((flatWeight prims cut sk.t0 (v, c) : ℝ≥0∞) * (cut.shape c : ℝ≥0∞)).toReal) /
    ((standinScale p * cut.top).toReal * Fintype.card (BucketVec p))

/-- The regularity gap at a constant cut-off `β`: each column relative to the mean flattened
weight `𝔼_c min(1, aw / β)`, over `K · β · |V|`. -/
theorem signerRegGap_const (β : ℚ≥0) :
    signerRegGap prims sk aHat (Cutoff.const β) =
      (∑ v, (𝔼 c, |(realMass prims sk aHat v c).toReal -
          (zAcceptFraction p * standinMass prims sk v c).toReal|) /
          𝔼 c, (flatWeight prims (Cutoff.const β) sk.t0 (v, c) : ℝ≥0∞).toReal) /
        ((standinScale p * β).toReal * Fintype.card (BucketVec p)) := by
  simp only [signerRegGap, ENNReal.nnratCast_one, mul_one]

/-- The regularity gap is nonnegative. -/
theorem signerRegGap_nonneg (cut : Cutoff p) : 0 ≤ signerRegGap prims sk aHat cut :=
  div_nonneg (Finset.sum_nonneg fun _ _ => div_nonneg
    (Finset.expect_nonneg fun _ _ => abs_nonneg _)
    (Finset.expect_nonneg fun _ _ => ENNReal.toReal_nonneg))
    (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))

end Signer

end GordieHowe.MLDSA
