-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Flatten
public import GordieHowe.Foundations.ToMathlib.PMFOracleQuenched

@[expose] public section

/-!
# The ML-DSA ring signer publishing `w₁`

Every ring member publishes `(ρ, t₁, t₀)`. The signer `i` repeats idealized FIPS 204 attempts
(`Ideal.lean`: `y` uniform on the mask box, `c̃_i = H(µ_i ‖ w₁)`); for an accepted attempt with
commitment `w₁` it reads every member's hash `c̃_j = H(µ_j ‖ w₁)` and keeps the attempt with
probability `min(1, β_min / aw_i(c̃_i, w₁)) · ∏_{j ≠ i} min(1, aw_j(c̃_j, w₁) / β_min)`, where
`aw_j(c̃, w₁)` is the uniform-`w` acceptance weight of the ct₀ and hint checks with member `j`'s
published `t₀` (`t0Weight`, `acceptWeight`).

* `t0Weight`, `memberWeight`, `ringWeights`: the weights `aw_j` and `min(1, aw_j / β_min)`,
  rational (`coe_t0Weight`, `coe_memberWeight`: their casts to `ℝ≥0∞`), as the column weights of
  `PMF.RingWeights`; `t0Weight_le_memberWeight`: `aw_j ≤ min(1, aw_j / β_min)`
  for `β_min ≤ 1`.
* `mul_flattenCoin_eq`: `aw_i · min(1, β_min / aw_i) = β_min · min(1, aw_i / β_min)`.
* `ringLoopSigner`: the signer as a `PMF.LoopSigner`, with level `β = K · β_min`, `K` the
  stand-in scale (`standinScale`, the z-acceptance fraction times the uniform-`w` scale).
* `ringRegGap`, `relColError_le_ringRegGap`: the signer's relative column error is at most its
  regularity gap: the column-wise ℓ1 distance between the real accepted mass (`y` uniform on the
  mask box, all four checks) and the uniform-`w` stand-in mass times the z-acceptance fraction
  `ρ_z` (`zAcceptFraction`, `maskUniform_zCheck_eq`), relative to the signer's own mean weight.
  It depends on the signer's key only.
* `ringVerify`: FIPS 204 Algorithm 8 (`MLDSA.fipsVerify`) with the commitment hash
  `c̃ = H((tr, m), w₁)` read from a random oracle on `(tr, m)` and bucket vectors, and the
  recomputed commitment required to equal the published `w₁`.
* `ringVerify_attemptOutput`: every accepted attempt of an honestly generated key verifies.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA44 Finset PMF
open scoped ENNReal BigOperators
open LatticeCrypto TransformOps

/-! ### The weights of the ring -/

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

theorem signerWeight_eq_t0Weight (sk : SecretKey p) :
    signerWeight prims sk = t0Weight prims sk.t0 :=
  rfl

/-- **The member weight** `min(1, aw / β_min)` of a published `t₀` (`NNRat.minOneDiv`, the value
of `ℝ≥0∞` at `β_min = 0`). -/
def memberWeight (βmin : ℚ≥0) (t0 : RqVec p.k) (vc : BucketVec p × CommitHashBytes p) : ℚ≥0 :=
  NNRat.minOneDiv (t0Weight prims t0 vc) βmin

omit [NeZero (bucketCount p)] in
/-- The member weight in `ℝ≥0∞` is `min(1, aw / β_min)`. -/
theorem coe_memberWeight (βmin : ℚ≥0) (t0 : RqVec p.k) (vc : BucketVec p × CommitHashBytes p) :
    (memberWeight prims βmin t0 vc : ℝ≥0∞) = min 1 ((t0Weight prims t0 vc : ℝ≥0∞) / βmin) :=
  ENNReal.nnratCast_minOneDiv _ _

omit [NeZero (bucketCount p)] in
/-- **The member weight is at least the acceptance weight** for `β_min ≤ 1`:
`aw ≤ min(1, aw / β_min)`, since `aw ≤ 1` (`acceptWeight_le_one`). -/
theorem t0Weight_le_memberWeight (hp : SigningParams p) {βmin : ℚ≥0} (hβ : (βmin : ℝ≥0∞) ≤ 1)
    (t0 : RqVec p.k) (vc : BucketVec p × CommitHashBytes p) :
    (t0Weight prims t0 vc : ℝ≥0∞) ≤ (memberWeight prims βmin t0 vc : ℝ≥0∞) := by
  rw [coe_memberWeight]
  refine le_min ?_ ((div_one _).symm.le.trans (ENNReal.div_le_div_left hβ _))
  rw [coe_t0Weight]
  exact ENNReal.ofReal_le_one.2 (acceptWeight_le_one hp.beta_lt_gamma2 _ _ _)

omit [NeZero (bucketCount p)] in
/-- `t0Weight_le_memberWeight` in `ℝ`. -/
theorem toReal_t0Weight_le_memberWeight (hp : SigningParams p) {βmin : ℚ≥0} (hβ : (βmin : ℝ≥0∞) ≤ 1)
    (t0 : RqVec p.k) (vc : BucketVec p × CommitHashBytes p) :
    (t0Weight prims t0 vc : ℝ≥0∞).toReal ≤ (memberWeight prims βmin t0 vc : ℝ≥0∞).toReal :=
  ENNReal.toReal_mono (ENNReal.nnratCast_ne_top _) (t0Weight_le_memberWeight prims hp hβ t0 vc)

/-- **The column weights of a ring of published `t₀`s.** -/
def ringWeights {n : ℕ} (βmin : ℚ≥0) (t0s : Fin n → RqVec p.k) :
    PMF.RingWeights (Fin n) (BucketVec p) (CommitHashBytes p) where
  wtQ j := memberWeight prims βmin (t0s j)
  wtQ_le_one _ _ := NNRat.minOneDiv_le_one _ _

/-- `x · min(1, y / x) = min x y` for finite `x`. -/
theorem _root_.ENNReal.mul_min_one_div {x y : ℝ≥0∞} (hx : x ≠ ⊤) : x * min 1 (y / x) = min x y := by
  by_cases h0 : x = 0
  · simp [h0]
  have hm : Monotone fun t : ℝ≥0∞ => x * t := fun _ _ h => by dsimp only; gcongr
  rw [hm.map_min, mul_one, ENNReal.mul_div_cancel h0 hx]

/-- **The signer's flattening coin against its member weight**:
`aw_i · min(1, β_min / aw_i) = β_min · min(1, aw_i / β_min)`. -/
theorem mul_flattenCoin_eq (sk : SecretKey p) {βmin : ℚ≥0} (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (vc : BucketVec p × CommitHashBytes p) :
    (signerWeight prims sk vc : ℝ≥0∞) * (flattenCoin prims sk βmin vc : ℝ≥0∞) =
      (βmin : ℝ≥0∞) * (memberWeight prims βmin sk.t0 vc : ℝ≥0∞) := by
  rw [coe_flattenCoin, flattenKeep, ENNReal.mul_min_one_div (ENNReal.nnratCast_ne_top _),
    coe_memberWeight, ENNReal.mul_min_one_div hβt, min_comm]
  rfl

end Weights

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

/-- The level `K · β_min` of the ring signer is positive. -/
theorem ringLevel_pos (hp : SigningParams p) {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) :
    0 < (standinScale p * βmin).toReal := by
  rw [ENNReal.toReal_mul]
  exact mul_pos (standinScale_pos hp) (ENNReal.toReal_pos hβ0 hβt)

/-- **The ML-DSA ring signer** as a loop signer: `y` uniform on the mask box, commitment
`w₁ = HighBits(Â·y)`, acceptance the four checks of FIPS 204 Algorithm 7, the flattening coin
`min(1, β_min / aw_i)`, and level `K · β_min`. -/
noncomputable def ringLoopSigner (hp : SigningParams p) {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) : PMF.LoopSigner (BucketVec p) (CommitHashBytes p) where
  Y := MaskBox p
  P := maskUniform p
  w1 := realBuckets aHat
  acc := attemptAccept prims sk aHat
  κ a := (flattenCoin prims sk βmin a : ℝ≥0∞)
  hκ := coe_flattenCoin_le_one prims sk βmin
  β := (standinScale p * βmin).toReal
  hβ := ringLevel_pos hp hβ0 hβt

/-- The real accepted mass of `(w₁, c̃)`: `Pr_y[HighBits(Â·y) = v ∧ the four checks pass at c̃]`. -/
noncomputable def realMass (v : BucketVec p) (cTilde : CommitHashBytes p) : ℝ≥0∞ :=
  signerMass (maskUniform p) (realBuckets aHat) (attemptAccept prims sk aHat) v cTilde

/-- The uniform-`w` stand-in accepted mass of `(w₁, c̃)` (no z-check). -/
noncomputable def standinMass (v : BucketVec p) (cTilde : CommitHashBytes p) : ℝ≥0∞ :=
  signerMass (uniformOfFintype (CoeffIndex p → Coeff)) bucketsOf (standinAccept prims sk) v cTilde

/-- **The regularity gap of the signer** at the cut-off `β_min`: the column-wise ℓ1 distance
`∑_v 𝔼_c |realMass v c - ρ_z · standinMass v c|` between the real accepted mass and the
stand-in mass scaled by the z-acceptance fraction `ρ_z`, each column relative to the signer's
mean member weight `𝔼_c min(1, aw_i / β_min)`, over `K · β_min · |V|`. -/
noncomputable def ringRegGap (βmin : ℚ≥0) : ℝ :=
  (∑ v, (𝔼 c, |(realMass prims sk aHat v c).toReal -
      (zAcceptFraction p * standinMass prims sk v c).toReal|) /
      𝔼 c, (memberWeight prims βmin sk.t0 (v, c) : ℝ≥0∞).toReal) /
    ((standinScale p * βmin).toReal * Fintype.card (BucketVec p))

/-- The regularity gap is nonnegative. -/
theorem ringRegGap_nonneg (βmin : ℚ≥0) : 0 ≤ ringRegGap prims sk aHat βmin :=
  div_nonneg (Finset.sum_nonneg fun _ _ => div_nonneg
    (Finset.expect_nonneg fun _ _ => abs_nonneg _)
    (Finset.expect_nonneg fun _ _ => ENNReal.toReal_nonneg))
    (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))

/-- **The column deviation of the ring signer is at most the column regularity gap**, when the
signer's published `t₀` is its own. -/
theorem colDev_le_abs_sub (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) {n : ℕ} (t0s : Fin n → RqVec p.k) (i : Fin n)
    (hi : t0s i = sk.t0) {βmin : ℚ≥0} (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (v : BucketVec p) (c : CommitHashBytes p) :
    colDev (ringWeights prims βmin t0s) i (maskUniform p) (realBuckets aHat)
        (attemptAccept prims sk aHat) (fun a => (flattenCoin prims sk βmin a : ℝ≥0∞))
        (standinScale p * βmin).toReal
        v c ≤ |(realMass prims sk aHat v c).toReal -
          (zAcceptFraction p * standinMass prims sk v c).toReal| := by
  have hS : zAcceptFraction p * standinMass prims sk v c =
      standinScale p * signerWeight prims sk (v, c) := by
    rw [standinMass, SigningLaws.signerMass_standin prims sk hp h_laws hs2 v c, standinScale,
      mul_assoc]
    rfl
  have hlev : (standinScale p * βmin).toReal *
      ((ringWeights prims βmin t0s).wt i (v, c)).toReal =
      (zAcceptFraction p * standinMass prims sk v c * flattenCoin prims sk βmin (v, c)).toReal := by
    rw [← ENNReal.toReal_mul, hS, mul_assoc (standinScale p) (signerWeight prims sk (v, c)),
      mul_flattenCoin_eq prims sk hβt]
    simp only [ringWeights, PMF.RingWeights.wt, hi, mul_assoc]
  have hκ : (flattenCoin prims sk βmin (v, c) : ℝ≥0∞).toReal ≤ 1 :=
    ENNReal.toReal_le_one_of_le_one (coe_flattenCoin_le_one prims sk βmin _)
  unfold colDev
  rw [hlev, ENNReal.toReal_mul, ENNReal.toReal_mul, ← sub_mul, abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_of_le_one_right (abs_nonneg _) hκ

/-- **The signer's relative column error is at most its regularity gap.** -/
theorem relColError_le_ringRegGap (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) {n : ℕ} (t0s : Fin n → RqVec p.k) (i : Fin n)
    (hi : t0s i = sk.t0) {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) :
    relColError (ringWeights prims βmin t0s) i (maskUniform p) (realBuckets aHat)
        (attemptAccept prims sk aHat) (fun a => (flattenCoin prims sk βmin a : ℝ≥0∞))
        (standinScale p * βmin).toReal ≤
      ringRegGap prims sk aHat βmin := by
  unfold relColError ringRegGap
  have hden : 0 < (standinScale p * βmin).toReal * Fintype.card (BucketVec p) :=
    mul_pos (ringLevel_pos hp hβ0 hβt) (by exact_mod_cast Fintype.card_pos)
  refine div_le_div_of_nonneg_right ?_ hden.le
  refine Finset.sum_le_sum fun v _ => ?_
  have hmean : (ringWeights prims βmin t0s).meanWeight i v =
      𝔼 c, (memberWeight prims βmin sk.t0 (v, c) : ℝ≥0∞).toReal := by
    simp only [PMF.RingWeights.meanWeight, PMF.RingWeights.wt, ringWeights, hi]
  rw [hmean]
  refine div_le_div_of_nonneg_right ?_ (Finset.expect_nonneg fun _ _ => ENNReal.toReal_nonneg)
  exact Finset.expect_le_expect fun c _ =>
    colDev_le_abs_sub prims sk aHat hp h_laws hs2 t0s i hi hβt v c

end Signer

/-! ### Verification against a random oracle -/

section Verify

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]
  {Msg : Type}

/-- **ML-DSA verification with the commitment hash read from a random oracle** (FIPS 204
Algorithm 8, as the vendored `MLDSA.fipsVerify`): with `tr = H(pk)` (line 6),
`c = SampleInBall(c̃)`, `w'_Approx = Â·z - c·t₁·2^d` and `w₁' = UseHint(h, w'_Approx)`
(lines 7–10), accept iff `‖z‖∞ < γ₁ - β`, the recomputed commitment `w₁'` (as a bucket vector,
`enc`) is the published `w₁`, `c̃ = H((tr, m), w₁)` (line 12, with the random oracle `H` in place
of `H(µ ‖ w1Encode(w₁))`), and `h` has at most `ω` ones. -/
def ringVerify (H : (Bytes 64 × Msg) × BucketVec p → CommitHashBytes p)
    (enc : Vector prims.High p.k → BucketVec p) (pk : PublicKey p prims) (m : Msg)
    (w1 : BucketVec p) (sig : FIPSSignature p prims) : Bool :=
  let aHat := prims.expandA pk.rho
  let tr := prims.hashPublicKey pk.rho pk.t1
  let c := prims.sampleInBall sig.cTilde
  let wApprox := computeWApprox p prims aHat c sig.z pk.t1
  let w1' := enc (prims.useHintVec sig.h wApprox)
  decide (polyVecNorm sig.z < p.gamma1 - p.beta) && decide (w1' = w1) &&
    decide (H ((tr, m), w1) = sig.cTilde) && decide (prims.hintWeight sig.h ≤ p.omega)

/-- **The primitive laws of verification**: the transform laws, the `Power2Round` decomposition
and the `UseHint`/`MakeHint` law, three fields of `Primitives.Laws`. -/
structure VerifyLaws : Prop where
  /-- Generic transform laws for the instantiated ring backend. -/
  transform : NTTRingLaws nttOps
  /-- `power2RoundShift(fst(power2Round(r))) + snd(power2Round(r)) = r`. -/
  power2Round_decomp : ∀ r : Rq,
    prims.power2RoundShift (prims.power2Round r).1 + (prims.power2Round r).2 = r
  /-- `UseHint(MakeHint(z, r), r) = HighBits(r + z)` when `‖z‖∞ ≤ γ₂`. -/
  useHint_makeHint : ∀ z r : Rq, polyNorm z ≤ p.gamma2 →
    prims.useHint (prims.makeHint z r) r = prims.highBits (r + z)

omit [NeZero (bucketCount p)] in
/-- **The key identity** `w'_Approx = Â·y - c·s₂ + c·t₀` for `z = y + c·s₁` and an honestly
generated key (the vendored `keyGenFromSeed_wApprox_eq`, from the transform laws and the
`Power2Round` decomposition only). -/
theorem VerifyLaws.wApprox_eq (h_laws : VerifyLaws prims) {pk : PublicKey p prims}
    {sk : SecretKey p} (seed : Bytes 32) (hkeygen : keyGenFromSeed p prims seed = (pk, sk))
    (c : Rq) (y : RqVec p.l) :
    computeWApprox p prims (prims.expandA pk.rho) c (y + c • sk.s1) pk.t1 =
      (prims.expandA pk.rho) * y - c • sk.s2 + c • sk.t0 := by
  have := h_laws.transform
  let laws := h_laws.transform
  set aHat := prims.expandA pk.rho
  simp only [computeWApprox]
  refine Vector.ext fun i hi => ?_
  simp only [Vector.getElem_add, Vector.getElem_sub,
    nttOps.hatVec_add, nttOps.unhatVec_sub, nttOps.matVecMul_add, nttOps.unhatVec_add]
  have h_kg : prims.power2RoundShiftVec pk.t1 + sk.t0 = aHat * sk.s1 + sk.s2 := by
    simp only [keyGenFromSeed, Prod.mk.injEq] at hkeygen
    obtain ⟨hpk, hsk⟩ := hkeygen
    have hrho  := congr_arg PublicKey.rho hpk.symm
    have hs1   := congr_arg SecretKey.s1 hsk.symm
    have hs2   := congr_arg SecretKey.s2 hsk.symm
    have haHat : aHat = prims.expandA (prims.expandSeed seed).1 := by simp [aHat, hrho]
    rw [show pk.t1 = (prims.power2RoundVec (aHat * sk.s1 + sk.s2)).1 from by
          rw [hs1, hs2, haHat]; exact congr_arg PublicKey.t1 hpk.symm,
        show sk.t0 = (prims.power2RoundVec (aHat * sk.s1 + sk.s2)).2 from by
          rw [hs1, hs2, haHat]; exact congr_arg SecretKey.t0 hsk.symm]
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_add, Primitives.power2RoundShiftVec, Primitives.power2RoundVec,
      Vector.map_map, Vector.getElem_map, Function.comp]
    exact h_laws.power2Round_decomp _
  have hAs1_hat : nttOps.matVecMul aHat (nttOps.hatVec sk.s1) =
      nttOps.hatVec (prims.power2RoundShiftVec pk.t1 + sk.t0 - sk.s2) := by
    rw [h_kg]
    refine Vector.ext fun j hj => ?_
    simp only [hatVec, HMul.hMul, coeffMatVecMul, unhatVec, matVecMul,
               Vector.getElem_map, Vector.getElem_sub, Vector.getElem_add]
    have hcancel : (fromHat (dot nttOps aHat[j] (Vector.map toHat sk.s1)) : Rq) +
        sk.s2[j] - sk.s2[j] = fromHat (dot nttOps aHat[j] (Vector.map toHat sk.s1)) := by
      abel
    rw [hcancel, laws.toHat_fromHat]
  have hMatScalarComm : nttOps.matVecMul aHat (nttOps.hatVec (c • sk.s1)) =
      nttOps.scalarVecMul (toHat c) (nttOps.matVecMul aHat (nttOps.hatVec sk.s1)) := by
    have hNTTSmul : nttOps.hatVec (c • sk.s1) =
        nttOps.scalarVecMul (toHat c) (nttOps.hatVec sk.s1) := by
      refine Vector.ext fun j hj => ?_
      simp only [hatVec, scalarVecMul, Vector.getElem_map]
      change nttOps.toHat (nttOps.coeffScalarVecMul c sk.s1)[j] = _
      simp only [coeffScalarVecMul, unhatVec, scalarVecMul, hatVec,
                 Vector.map_map, Vector.getElem_map, Function.comp_apply, laws.toHat_fromHat]
    rw [hNTTSmul]
    refine Vector.ext fun j hj => ?_
    simp only [matVecMul, scalarVecMul, Vector.getElem_map]
    exact nttOps.dot_scalar_right (toHat c) _ _
  simp only [hMatScalarComm, hAs1_hat]
  change (aHat * y)[i] +
      (nttOps.coeffScalarVecMul c (prims.power2RoundShiftVec pk.t1 + sk.t0 - sk.s2))[i] -
      (nttOps.coeffScalarVecMul c (prims.power2RoundShiftVec pk.t1))[i] =
      (aHat * y)[i] -
      (nttOps.coeffScalarVecMul c sk.s2)[i] + (nttOps.coeffScalarVecMul c sk.t0)[i]
  simp only [nttOps.coeffScalarVecMul_sub, nttOps.coeffScalarVecMul_add,
             Vector.getElem_sub, Vector.getElem_add]
  abel

/-- **Every accepted attempt of an honestly generated key verifies**: for the key of `seed`
with `‖s₂‖∞ ≤ η`, a mask `y` whose attempt with `c̃ = H((tr, m), HighBits(Â·y))` passes the four
checks outputs a signature `(c̃, y + c·s₁, h)` that `ringVerify` accepts with the published
commitment `HighBits(Â·y)`, given the signing and verification laws and an encoding `enc` of
commitments as bucket vectors coherent with `bucketsOf` (`henc`). -/
theorem ringVerify_attemptOutput [Nonempty (MaskBox p)] (h_laws : SigningLaws prims)
    (hv : VerifyLaws prims)
    {enc : Vector prims.High p.k → BucketVec p}
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} {pk : PublicKey p prims} {sk : SecretKey p}
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (hs2 : polyVecBounded sk.s2 p.eta)
    (H : (Bytes 64 × Msg) × BucketVec p → CommitHashBytes p) (m : Msg) (y : MaskBox p)
    (hacc : attemptAccept prims sk (prims.expandA pk.rho) y
      (H ((prims.hashPublicKey pk.rho pk.t1, m), realBuckets (prims.expandA pk.rho) y)) = true) :
    ringVerify prims H enc pk m (realBuckets (prims.expandA pk.rho) y)
      (attemptOutput prims sk (prims.expandA pk.rho)
        (y, H ((prims.hashPublicKey pk.rho pk.t1, m), realBuckets (prims.expandA pk.rho) y))) =
      true := by
  set aHat := prims.expandA pk.rho
  set cT := H ((prims.hashPublicKey pk.rho pk.t1, m), realBuckets aHat y)
  set c := prims.sampleInBall cT
  have hacc' := hacc
  simp only [attemptAccept, signAccept, zCheck, r0Check, ct0Check, hintCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hacc'
  obtain ⟨⟨⟨hz, hr0⟩, hct0⟩, hw⟩ := hacc'
  have hcs2 : polyVecNorm (c • sk.s2) ≤ p.beta :=
    SigningLaws.polyVecNorm_sampleInBall_smul_le prims h_laws cT sk.s2 hs2
  have hrec : prims.useHintVec (attemptHint prims sk aHat y.1 cT)
      (computeWApprox p prims aHat c (y.1 + c • sk.s1) pk.t1) = prims.highBitsVec (aHat * y.1) := by
    rw [hv.wApprox_eq prims seed hkeygen c y.1]
    refine useHintVec_makeHintVec_eq_highBitsVec p prims hv.useHint_makeHint h_laws.hide_low
      (aHat * y.1) (c • sk.s2) (c • sk.t0) hct0 hr0 fun j => ?_
    have hj : polyNorm ((c • sk.s2).get j) ≤ p.beta :=
      le_trans (LatticeCrypto.PolyVec.component_cInfNorm_le normOps (c • sk.s2) j) hcs2
    unfold polyNorm normOps at hj
    simpa [LatticeCrypto.zmodPolyNormOps, LatticeCrypto.normOpsOfCenteredView,
      LatticeCrypto.cInfNorm] using hj
  simp only [ringVerify, attemptOutput, Bool.and_eq_true]
  refine ⟨⟨⟨decide_eq_true hz, decide_eq_true ?_⟩, decide_eq_true rfl⟩, decide_eq_true hw⟩
  rw [hrec, henc]
  rfl

end Verify

end GordieHowe.MLDSA
