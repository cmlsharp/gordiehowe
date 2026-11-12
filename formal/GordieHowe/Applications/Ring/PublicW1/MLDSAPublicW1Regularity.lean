-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1ExpandS
public import GordieHowe.Applications.MLDSA.Regularity.WeightTail
public import GordieHowe.Applications.MLDSA.Regularity.WeightTail44
public import GordieHowe.Applications.MLDSA.Regularity.InstancesSeven
public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1Concentration
public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1Query
public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1Keys

@[expose] public section

/-!
# The regularity term and the check parameters of the ring publishing `w₁`

The game in which `ExpandA`, `ExpandS` and `SampleInBall` are random oracles: `oraclePrimitives
G_B G_S` are the concrete primitives with `SampleInBall = G_B` onto the challenge set `B_τ`
(FIPS 204 §2.3, Algorithm 29) and `ExpandS = G_S` onto the `η`-box (Algorithm 33, `withExpandS`),
and `ExpandA` (Algorithm 32) is a random oracle `G_A` (`withExpandA`). The anonymity headline
averaged over these oracles is `w1Scheme.expect_anonAdvantage_le` (`MLDSAW1AnonOracle.lean`); this
file gives its regularity and check numbers.

* `concreteWithSampleInBallExpandS`, `concreteWithSampleInBallExpandS_concrete`, `oraclePrimitives`,
  `oraclePrimitives_eq`, `signingLaws_concreteWithSampleInBallExpandS`,
  `verifyLaws_concreteWithSampleInBallExpandS`: the concrete primitives with any `SampleInBall` and
  `ExpandS`, equal to `concretePrimitivesKeyGen` at the FIPS 204 ones, and their signing and
  verification laws.
* `expect_regGapAvg_le_of`: `𝔼_{G_B, G_S} regGapAvg ≤ R / β_min · √B` from a per-key bound
  `𝔼_Â signerRegGap ≤ R / β_min · √(𝔼_Â w⁻²)` for every positive lower bound `w` on the mean member
  weights (`expect_signerRegGap_le_sqrt`), a bound `F(‖t₀‖₂²)` on the oracle average of the inverse
  square acceptance floor (`oracleAcceptFloor`, which bounds the mean member weights for
  `β_min ≤ 1`: `oracleAcceptFloor_le_expect_flatWeight`), and a bound `B` on
  `𝔼_{s, Â} F(‖t₀‖₂²)`. `ExpandS` as a random oracle gives a uniform box secret
  (`expect_regGapAvg_withExpandS`); the key of key generation is the key of the regularity
  argument (`signerRegGap_idealSecretKey_eq`); Jensen's inequality for `√` over `G_B` and over the
  secret (`Real.expect_sqrt_le_sqrt_expect`) leaves `√(𝔼_{s, G_B, Â} w⁻²)`.
* `expect_regGapAvg_le_mldsa65`, `_mldsa87`: for `β_min ≤ 1`,
  `𝔼_{G_B, G_S} regGapAvg ≤ R · C / β_min` with the seven-slot regularity bound `R = 11 · 2^-199`
  at ML-DSA-65 and `R = 12 · 2^-294` at ML-DSA-87 (`expect_signerRegGap_le_sqrt_mldsa65_seven`,
  `_mldsa87_seven`), and the weight factor `C = 9/2` at ML-DSA-65 and `C = 33/5` at ML-DSA-87
  (`expect_expect_floorInvSqBound_le_mldsa65`, `_mldsa87`): `log₂ C = 2.17` and `2.72` bits, so
  `log₂ (R · C) = -193.37` at ML-DSA-65 and `-287.69` at ML-DSA-87.
* `isApproved_mldsa65`, `isApproved_mldsa87`: the two parameter sets are approved.

At ML-DSA-44 `τ · 2^12 > γ₂`, so the ct₀ check can fail and the acceptance floor (`FloorParams`)
does not apply. In its place:

* `expect_regGapAvg_le_of_weight`: `expect_regGapAvg_le_of` for any weight `W G t₀ ≥ 0` that
  bounds the mean member weights and is `0` only where they all are, with the Cauchy–Schwarz bound
  for a weight that may vanish (`expect_signerRegGap_le_sqrt_of_nonneg`) and a bound `B` on
  `𝔼_{s, Â, G} (W G t₀)⁻²`.
* `expect_regGapAvg_le_mldsa44`: for `β_min ≤ 1`, `𝔼_{G_B, G_S} regGapAvg ≤ R · C / β_min` with
  `R = 11 · 2^-101` (`expect_signerRegGap_le_sqrt_mldsa44_box_seven_of_nonneg`) and `C = 24/5`
  (`mldsa44OracleWeight`, `expect_expect_expect_inv_sq_mldsa44OracleWeight_le`): `log₂ C = 2.26`
  bits, so `log₂ (R · C) = -95.27`.
* `checkError_checkParams_le`: at `reps = 355`, `tol = 2`, `s = 1/2` and `x = 89` the check error
  is at most `2^-240`.
* `checkError_le_of`, `CheckParams`, `checkParams_tol{2,8,16,40}`: check parameters with check
  error at most `2^-240` at 355 samples per member: `(tol, s, x)` = `(2, 1/2, 89)`,
  `(8, 3/5, 26)`, `(16, 2/3, 15)`, `(40, 5/6, 7)`, the tolerance and the defect budget growing
  with the ring size (the README estimates the sizes each row supports).
* `checkError_le_of_bits`, `checkError_tol{2,8,16,40}_le_300`: the check error at most `2^-κ`
  from two binary exponents, and the same rows at check error at most `2^-300` with 439, 407,
  405 and 401 samples per member.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA GordieHowe.MLDSA.Spec
  GordieHowe.MLDSA.Regularity PMF IOP GordieHowe.SPBCS GordieHowe.QROM
open LatticeCrypto TransformOps

attribute [local instance] concreteNTTRingOps

/-! ### The primitives of the game -/

section Primitives

variable (p : Params)

/-- **The concrete primitives with `SampleInBall = G` and `ExpandS = X`**: the vendored FIPS 204
primitives with the FIPS 204 `ExpandS` (`concretePrimitivesKeyGen`) with `SampleInBall`
(Algorithm 29) replaced by `G` and `ExpandS` (Algorithm 33) by `X`. -/
abbrev concreteWithSampleInBallExpandS (G : CommitHashBytes p → ChallengePoly)
    (X : _root_.MLDSA.Bytes 64 → RqVec p.l × RqVec p.k) : Primitives p :=
  { concretePrimitivesKeyGen p with sampleInBall := G, expandS := X }

/-- At the FIPS 204 `SampleInBall` and `ExpandS` these are the primitives
`concretePrimitivesKeyGen`. -/
theorem concreteWithSampleInBallExpandS_concrete :
    concreteWithSampleInBallExpandS p (concretePrimitives p).sampleInBall (Spec.expandS p) =
      concretePrimitivesKeyGen p :=
  rfl

variable {p}

/-- **The primitives with `SampleInBall` and `ExpandS` random oracles**: `SampleInBall = G_B`
onto the challenge set `B_τ` and `ExpandS = G_S` onto the coefficient arrays of `η`-bounded
secrets (`secretOfCoeffs`). -/
noncomputable abbrev oraclePrimitives (GB : CommitHashBytes p → ChallengeBall p.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p) : Primitives p :=
  concreteWithSampleInBallExpandS p (fun c => (GB c).1) fun rhoPrime => secretOfCoeffs (GS rhoPrime)

/-- The oracle primitives are `withExpandS` of `withSampleInBall` of `concretePrimitivesKeyGen`. -/
theorem oraclePrimitives_eq (GB : CommitHashBytes p → ChallengeBall p.tau)
    (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p) :
    oraclePrimitives GB GS =
      withExpandS (withSampleInBall (concretePrimitivesKeyGen p) fun c => (GB c).1) GS :=
  rfl

/-- ML-DSA-65 is an approved parameter set. -/
theorem isApproved_mldsa65 : mldsa65.isApproved := Or.inr (Or.inl rfl)

/-- ML-DSA-87 is an approved parameter set. -/
theorem isApproved_mldsa87 : mldsa87.isApproved := Or.inr (Or.inr rfl)

end Primitives

/-! ### Anonymity at the concrete primitives with `ExpandA` a random oracle -/

section Ideal

variable {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)] {Msg : Type} [Fintype Msg]
  [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n Q : ℕ}

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- **The signing laws at `concreteWithSampleInBallExpandS`** for `SampleInBall` of challenge
shape (`signingLaws_concreteWithSampleInBall`; the laws do not read `ExpandS`). -/
theorem signingLaws_concreteWithSampleInBallExpandS (hp : p.isApproved)
    {G : CommitHashBytes p → ChallengePoly} (hG : SampleInBallShape (concreteWithSampleInBall p G))
    (X : _root_.MLDSA.Bytes 64 → RqVec p.l × RqVec p.k) :
    SigningLaws (concreteWithSampleInBallExpandS p G X) :=
  let h := signingLaws_concreteWithSampleInBall p hp hG
  ⟨h.transform, h.hide_low, h.sampleInBall_smul_bound⟩

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- **The verification laws at `concreteWithSampleInBallExpandS`** (`verifyLaws_concrete`; the
laws do not read `SampleInBall` or `ExpandS`). -/
theorem verifyLaws_concreteWithSampleInBallExpandS (hp : p.isApproved)
    (G : CommitHashBytes p → ChallengePoly) (X : _root_.MLDSA.Bytes 64 → RqVec p.l × RqVec p.k) :
    VerifyLaws (concreteWithSampleInBallExpandS p G X) (nttOps := concreteNTTRingOps) :=
  let h := verifyLaws_concrete hp
  ⟨h.transform, h.power2Round_decomp, h.useHint_makeHint⟩


end Ideal


/-! ### The averaged regularity gap -/

section RegGap

variable {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)]

/-- **The averaged regularity gap from the Cauchy–Schwarz bound and the weight tail.** For
`β_min ≤ 1` and the acceptance floor parameters of `p` (`FloorParams`), if
* for every key `sk₀` with `s₁, s₂` in the `η`-box, every `SampleInBall` oracle `G` onto `B_τ` and
  every positive lower bound `w Â` on the mean member weights,
  `𝔼_Â signerRegGap ≤ R / β_min · √(𝔼_Â (w Â)⁻²)` (`expect_signerRegGap_le_sqrt_mldsa65`),
* `𝔼_G (oracleAcceptFloor p κ G t₀)⁻² ≤ F(‖t₀‖₂²)` for `‖t₀‖∞ ≤ 2^12`, and
* `𝔼_{e, Â} F(‖t₀‖₂²) ≤ B` over uniform box secrets `e` and a uniform matrix, for every key,

then `𝔼_{G_B, G_S} regGapAvg (oraclePrimitives G_B G_S) ≤ R / β_min · √B`. -/
theorem expect_regGapAvg_le_of {x₀ κ : ℝ} (hf : FloorParams p x₀ κ) {βmin : ℚ≥0}
    (hβ1 : (βmin : ℝ≥0∞) ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    (hgap : ∀ sk₀ : SecretKey p, polyVecBounded sk₀.s1 p.eta → polyVecBounded sk₀.s2 p.eta →
      ∀ (G : CommitHashBytes p → ChallengeBall p.tau) (w : TqMatrix p.k p.l → ℝ),
        (∀ aHat, 0 < w aHat) →
        (∀ aHat v, w aHat ≤ 𝔼 c, (flatWeight (oraclePrims G) (Cutoff.const βmin)
          (matrixKey sk₀ aHat).t0 (v, c) : ℝ≥0∞).toReal) →
        𝔼 aHat, signerRegGap (oraclePrims G) (matrixKey sk₀ aHat) aHat (Cutoff.const βmin) ≤
          R / (βmin : ℝ≥0∞).toReal * √(𝔼 aHat, (w aHat ^ 2)⁻¹))
    {F : ℝ → ℝ} (hF : ∀ t0 : RqVec p.k, polyVecNorm t0 ≤ 4096 →
      𝔼 G : CommitHashBytes p → ChallengeBall p.tau, (oracleAcceptFloor p κ G t0)⁻¹ ^ 2 ≤
        F (t0SqNorm t0))
    {B : ℝ} (hB : ∀ sk : SecretKey p, 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
      F (t0SqNorm (keyOf (keyOfCoeffs sk e)
        (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0) ≤ B) :
    𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p,
        regGapAvg (oraclePrimitives GB GS) βmin ≤ R / (βmin : ℝ≥0∞).toReal * √B := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty hf.tau_le
  set c := R / (βmin : ℝ≥0∞).toReal
  have hc : 0 ≤ c := div_nonneg hR ENNReal.toReal_nonneg
  set sk : _root_.MLDSA.Bytes 32 → SecretKey p := fun seed =>
    (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).2
  set w : (CommitHashBytes p → ChallengeBall p.tau) → _root_.MLDSA.Bytes 32 → SecretCoeffs p →
      TqMatrix p.k p.l → ℝ := fun GB seed e aHat =>
    oracleAcceptFloor p κ GB (matrixKey (keyOfCoeffs (sk seed) e) aHat).t0
  set Y : (CommitHashBytes p → ChallengeBall p.tau) → _root_.MLDSA.Bytes 32 → SecretCoeffs p →
      ℝ := fun GB seed e => 𝔼 aHat, (w GB seed e aHat ^ 2)⁻¹
  have ht0 : ∀ (sk₀ : SecretKey p) aHat, polyVecNorm (matrixKey sk₀ aHat).t0 ≤ 4096 :=
    fun sk₀ aHat => by
      rw [matrixKey_t0]
      exact polyVecNorm_edgeT0Of_le _
  -- The gap at the key of key generation is the gap of the regularity argument.
  have hkey : ∀ GB, 𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p,
      regGapAvg (oraclePrimitives GB GS) βmin =
        𝔼 seed : _root_.MLDSA.Bytes 32, 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
          signerRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat
              (Cutoff.const βmin) :=
    fun GB => by
      refine (expect_regGapAvg_withExpandS
        (withSampleInBall (concretePrimitivesKeyGen p) fun c => (GB c).1) βmin).trans ?_
      refine Finset.expect_congr rfl fun seed _ => Finset.expect_congr rfl fun e _ =>
        Finset.expect_congr rfl fun aHat _ => ?_
      exact signerRegGap_idealSecretKey_eq (fun c => (GB c).1) _ _ aHat _
        (keyOfCoeffs (sk seed) e) rfl rfl βmin
  -- The Cauchy–Schwarz bound for each key and oracle.
  have hstep : ∀ GB seed e, 𝔼 aHat : TqMatrix p.k p.l,
      signerRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat
          (Cutoff.const βmin) ≤
        c * √(Y GB seed e) := fun GB seed e =>
    hgap (keyOfCoeffs (sk seed) e) (secretOfCoeffs_bounded e).1 (secretOfCoeffs_bounded e).2 GB
      (w GB seed e) (fun aHat => acceptFloor_pos _ _ _ _) fun aHat v =>
        oracleAcceptFloor_le_expect_flatWeight hf (oraclePrims GB) GB (fun _ => rfl) hβ1 _
          (ht0 _ aHat) v
  have hY0 : ∀ GB seed e, 0 ≤ Y GB seed e := fun GB seed e =>
    Finset.expect_nonneg fun aHat _ => inv_nonneg.2 (sq_nonneg _)
  -- The tail of the weight, averaged over the oracle, the secret and the matrix.
  have hYB : ∀ seed, 𝔼 e : SecretCoeffs p, 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
      Y GB seed e ≤ B := fun seed => by
    refine le_trans (le_of_eq ?_) ((Finset.expect_le_expect fun e _ =>
      Finset.expect_le_expect fun aHat _ => hF _ (ht0 _ aHat)).trans (hB (sk seed)))
    refine Finset.expect_congr rfl fun e _ => ?_
    simp only [Y, w, inv_pow]
    exact Finset.expect_comm _ _ _
  calc 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p, regGapAvg (oraclePrimitives GB GS) βmin
      = 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 seed : _root_.MLDSA.Bytes 32,
          𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
            signerRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat
                (Cutoff.const βmin) :=
        Finset.expect_congr rfl fun GB _ => hkey GB
    _ = 𝔼 seed : _root_.MLDSA.Bytes 32, 𝔼 e : SecretCoeffs p,
          𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 aHat : TqMatrix p.k p.l,
            signerRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat
                (Cutoff.const βmin) := by
        rw [Finset.expect_comm]
        exact Finset.expect_congr rfl fun seed _ => Finset.expect_comm _ _ _
    _ ≤ 𝔼 seed : _root_.MLDSA.Bytes 32, 𝔼 e : SecretCoeffs p,
          𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, c * √(Y GB seed e) :=
        Finset.expect_le_expect fun seed _ => Finset.expect_le_expect fun e _ =>
          Finset.expect_le_expect fun GB _ => hstep GB seed e
    _ ≤ 𝔼 seed : _root_.MLDSA.Bytes 32, c * √B := by
        refine Finset.expect_le_expect fun seed _ => ?_
        simp_rw [← Finset.mul_expect]
        refine mul_le_mul_of_nonneg_left ?_ hc
        calc 𝔼 e : SecretCoeffs p, 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
              √(Y GB seed e)
            ≤ 𝔼 e : SecretCoeffs p, √(𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
                Y GB seed e) :=
              Finset.expect_le_expect fun e _ =>
                Real.expect_sqrt_le_sqrt_expect _ fun GB => hY0 GB seed e
          _ ≤ √(𝔼 e : SecretCoeffs p, 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
                Y GB seed e) :=
              Real.expect_sqrt_le_sqrt_expect _ fun e =>
                Finset.expect_nonneg fun GB _ => hY0 GB seed e
          _ ≤ √B := Real.sqrt_le_sqrt (hYB seed)
    _ = c * √B := Finset.expect_const Finset.univ_nonempty _

/-- **The averaged regularity gap at ML-DSA-65** with `ExpandS` and `SampleInBall`
random oracles: `𝔼_{G_B, G_S} regGapAvg ≤ 11 · 2^-199 · (9/2) / β_min` for
`β_min ≤ 1` (`expect_signerRegGap_le_sqrt_mldsa65_seven`,
`expect_expect_floorInvSqBound_le_mldsa65`). -/
theorem expect_regGapAvg_le_mldsa65 {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβ1 : (βmin : ℝ≥0∞) ≤ 1) :
    𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        regGapAvg (oraclePrimitives GB GS) βmin ≤ 11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal :=
          by
  have hβt : (βmin : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hβ1
  refine (expect_regGapAvg_le_of floorParams_mldsa65 hβ1 (by positivity)
    (fun sk₀ h1 h2 G w hw0 hw => expect_signerRegGap_le_sqrt_mldsa65_seven sk₀ h1 h2
      (sampleInBallShape_oraclePrims G) hβ0 hβt hw0 hw)
    expect_inv_sq_oracleAcceptFloor_le_floorInvSqBound_mldsa65
    expect_expect_floorInvSqBound_le_mldsa65).trans_eq ?_
  rw [Real.sqrt_sq (by norm_num)]
  exact div_mul_eq_mul_div _ _ _

/-- **The averaged regularity gap at ML-DSA-87** with `ExpandS` and `SampleInBall`
random oracles: `𝔼_{G_B, G_S} regGapAvg ≤ 12 · 2^-294 · (33/5) / β_min` for
`β_min ≤ 1` (`expect_signerRegGap_le_sqrt_mldsa87_seven`,
`expect_expect_floorInvSqBound_le_mldsa87`). -/
theorem expect_regGapAvg_le_mldsa87 {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβ1 : (βmin : ℝ≥0∞) ≤ 1) :
    𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        regGapAvg (oraclePrimitives GB GS) βmin ≤ 12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal :=
          by
  have hβt : (βmin : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hβ1
  refine (expect_regGapAvg_le_of floorParams_mldsa87 hβ1 (by positivity)
    (fun sk₀ h1 h2 G w hw0 hw => expect_signerRegGap_le_sqrt_mldsa87_seven sk₀ h1 h2
      (sampleInBallShape_oraclePrims G) hβ0 hβt hw0 hw)
    expect_inv_sq_oracleAcceptFloor_le_floorInvSqBound_mldsa87
    expect_expect_floorInvSqBound_le_mldsa87).trans_eq ?_
  rw [Real.sqrt_sq (by norm_num)]
  exact div_mul_eq_mul_div _ _ _

/-- **The averaged regularity gap from a weight that may vanish.** For `τ ≤ 256`, a weight
`W G t₀ ≥ 0` that bounds the mean member weights of every bucket vector for `‖t₀‖∞ ≤ 2^12` and is
`0` only where they are all `0`, if
* for every key `sk₀` with `s₁, s₂` in the `η`-box, every `SampleInBall` oracle `G` onto `B_τ` and
  every lower bound `w Â ≥ 0` on the mean member weights that is `0` only where they are all `0`,
  `𝔼_Â signerRegGap ≤ R / β_min · √(𝔼_Â (w Â)⁻²)` (`expect_signerRegGap_le_sqrt_of_nonneg`), and
* `𝔼_{e, Â, G} (W G t₀)⁻² ≤ B` over uniform box secrets `e`, a uniform matrix and a uniform oracle,
  for every key,

then `𝔼_{G_B, G_S} regGapAvg (oraclePrimitives G_B G_S) ≤ R / β_min · √B`. As
`expect_regGapAvg_le_of`, with `W` in place of the acceptance floor. -/
theorem expect_regGapAvg_le_of_weight (hτ : p.tau ≤ ringDegree) {βmin : ℚ≥0} {R : ℝ}
    (hR : 0 ≤ R) (W : (CommitHashBytes p → ChallengeBall p.tau) → RqVec p.k → ℝ)
    (hW0 : ∀ G t0, 0 ≤ W G t0)
    (hW : ∀ G t0, polyVecNorm t0 ≤ 4096 → ∀ v,
      W G t0 ≤ 𝔼 c, (flatWeight (oraclePrims G) (Cutoff.const βmin) t0 (v, c) : ℝ≥0∞).toReal)
    (hWz : ∀ G t0, W G t0 = 0 → ∀ v,
      𝔼 c, (flatWeight (oraclePrims G) (Cutoff.const βmin) t0 (v, c) : ℝ≥0∞).toReal = 0)
    (hgap : ∀ sk₀ : SecretKey p, polyVecBounded sk₀.s1 p.eta → polyVecBounded sk₀.s2 p.eta →
      ∀ (G : CommitHashBytes p → ChallengeBall p.tau) (w : TqMatrix p.k p.l → ℝ),
        (∀ aHat, 0 ≤ w aHat) →
        (∀ aHat v, w aHat ≤ 𝔼 c, (flatWeight (oraclePrims G) (Cutoff.const βmin)
          (matrixKey sk₀ aHat).t0 (v, c) : ℝ≥0∞).toReal) →
        (∀ aHat, w aHat = 0 → ∀ v, 𝔼 c, (flatWeight (oraclePrims G) (Cutoff.const βmin)
          (matrixKey sk₀ aHat).t0 (v, c) : ℝ≥0∞).toReal = 0) →
        𝔼 aHat, signerRegGap (oraclePrims G) (matrixKey sk₀ aHat) aHat (Cutoff.const βmin) ≤
          R / (βmin : ℝ≥0∞).toReal * √(𝔼 aHat, (w aHat ^ 2)⁻¹))
    {B : ℝ} (hB : ∀ sk : SecretKey p, 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
      𝔼 G : CommitHashBytes p → ChallengeBall p.tau, (W G (keyOf (keyOfCoeffs sk e)
        (keyMap (fun b => (keyOfCoeffs sk e).s1.get b) (matOfHat aHat))).t0)⁻¹ ^ 2 ≤ B) :
    𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p,
        regGapAvg (oraclePrimitives GB GS) βmin ≤ R / (βmin : ℝ≥0∞).toReal * √B := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty hτ
  set c := R / (βmin : ℝ≥0∞).toReal
  have hc : 0 ≤ c := div_nonneg hR ENNReal.toReal_nonneg
  set sk : _root_.MLDSA.Bytes 32 → SecretKey p := fun seed =>
    (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).2
  set w : (CommitHashBytes p → ChallengeBall p.tau) → _root_.MLDSA.Bytes 32 → SecretCoeffs p →
      TqMatrix p.k p.l → ℝ := fun GB seed e aHat =>
    W GB (matrixKey (keyOfCoeffs (sk seed) e) aHat).t0
  set Y : (CommitHashBytes p → ChallengeBall p.tau) → _root_.MLDSA.Bytes 32 → SecretCoeffs p →
      ℝ := fun GB seed e => 𝔼 aHat, (w GB seed e aHat ^ 2)⁻¹
  have ht0 : ∀ (sk₀ : SecretKey p) aHat, polyVecNorm (matrixKey sk₀ aHat).t0 ≤ 4096 :=
    fun sk₀ aHat => by
      rw [matrixKey_t0]
      exact polyVecNorm_edgeT0Of_le _
  -- The gap at the key of key generation is the gap of the regularity argument.
  have hkey : ∀ GB, 𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p,
      regGapAvg (oraclePrimitives GB GS) βmin =
        𝔼 seed : _root_.MLDSA.Bytes 32, 𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
          signerRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat
              (Cutoff.const βmin) :=
    fun GB => by
      refine (expect_regGapAvg_withExpandS
        (withSampleInBall (concretePrimitivesKeyGen p) fun c => (GB c).1) βmin).trans ?_
      refine Finset.expect_congr rfl fun seed _ => Finset.expect_congr rfl fun e _ =>
        Finset.expect_congr rfl fun aHat _ => ?_
      exact signerRegGap_idealSecretKey_eq (fun c => (GB c).1) _ _ aHat _
        (keyOfCoeffs (sk seed) e) rfl rfl βmin
  -- The Cauchy–Schwarz bound for each key and oracle.
  have hstep : ∀ GB seed e, 𝔼 aHat : TqMatrix p.k p.l,
      signerRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat
          (Cutoff.const βmin) ≤
        c * √(Y GB seed e) := fun GB seed e =>
    hgap (keyOfCoeffs (sk seed) e) (secretOfCoeffs_bounded e).1 (secretOfCoeffs_bounded e).2 GB
      (w GB seed e) (fun aHat => hW0 _ _) (fun aHat v => hW GB _ (ht0 _ aHat) v)
      (fun aHat h v => hWz GB _ h v)
  have hY0 : ∀ GB seed e, 0 ≤ Y GB seed e := fun GB seed e =>
    Finset.expect_nonneg fun aHat _ => inv_nonneg.2 (sq_nonneg _)
  -- The weight averaged over the oracle, the secret and the matrix.
  have hYB : ∀ seed, 𝔼 e : SecretCoeffs p, 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
      Y GB seed e ≤ B := fun seed => by
    refine le_trans (le_of_eq ?_) (hB (sk seed))
    refine Finset.expect_congr rfl fun e _ => ?_
    simp only [Y, w, inv_pow]
    exact Finset.expect_comm _ _ _
  calc 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs p, regGapAvg (oraclePrimitives GB GS) βmin
      = 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 seed : _root_.MLDSA.Bytes 32,
          𝔼 e : SecretCoeffs p, 𝔼 aHat : TqMatrix p.k p.l,
            signerRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat
                (Cutoff.const βmin) :=
        Finset.expect_congr rfl fun GB _ => hkey GB
    _ = 𝔼 seed : _root_.MLDSA.Bytes 32, 𝔼 e : SecretCoeffs p,
          𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, 𝔼 aHat : TqMatrix p.k p.l,
            signerRegGap (oraclePrims GB) (matrixKey (keyOfCoeffs (sk seed) e) aHat) aHat
                (Cutoff.const βmin) := by
        rw [Finset.expect_comm]
        exact Finset.expect_congr rfl fun seed _ => Finset.expect_comm _ _ _
    _ ≤ 𝔼 seed : _root_.MLDSA.Bytes 32, 𝔼 e : SecretCoeffs p,
          𝔼 GB : CommitHashBytes p → ChallengeBall p.tau, c * √(Y GB seed e) :=
        Finset.expect_le_expect fun seed _ => Finset.expect_le_expect fun e _ =>
          Finset.expect_le_expect fun GB _ => hstep GB seed e
    _ ≤ 𝔼 seed : _root_.MLDSA.Bytes 32, c * √B := by
        refine Finset.expect_le_expect fun seed _ => ?_
        simp_rw [← Finset.mul_expect]
        refine mul_le_mul_of_nonneg_left ?_ hc
        calc 𝔼 e : SecretCoeffs p, 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
              √(Y GB seed e)
            ≤ 𝔼 e : SecretCoeffs p, √(𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
                Y GB seed e) :=
              Finset.expect_le_expect fun e _ =>
                Real.expect_sqrt_le_sqrt_expect _ fun GB => hY0 GB seed e
          _ ≤ √(𝔼 e : SecretCoeffs p, 𝔼 GB : CommitHashBytes p → ChallengeBall p.tau,
                Y GB seed e) :=
              Real.expect_sqrt_le_sqrt_expect _ fun e =>
                Finset.expect_nonneg fun GB _ => hY0 GB seed e
          _ ≤ √B := Real.sqrt_le_sqrt (hYB seed)
    _ = c * √B := Finset.expect_const Finset.univ_nonempty _

/-- **The averaged regularity gap at ML-DSA-44** with `ExpandS` and `SampleInBall`
random oracles: `𝔼_{G_B, G_S} regGapAvg ≤ 11 · 2^-101 · (24/5) / β_min` for `β_min ≤ 1`
(`expect_regGapAvg_le_of_weight` with the weight `mldsa44OracleWeight`,
`expect_signerRegGap_le_sqrt_mldsa44_box_seven_of_nonneg`,
`expect_expect_expect_inv_sq_mldsa44OracleWeight_le`). -/
theorem expect_regGapAvg_le_mldsa44 {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβ1 : (βmin : ℝ≥0∞) ≤ 1) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        regGapAvg (oraclePrimitives GB GS) βmin ≤ 11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal :=
          by
  have := concreteNTTRingLaws
  have hβt : (βmin : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hβ1
  refine (expect_regGapAvg_le_of_weight (p := _root_.MLDSA.mldsa44)
    (by rw [show _root_.MLDSA.mldsa44.tau = 39 from rfl]; norm_num [ringDegree]) (by positivity)
    mldsa44OracleWeight mldsa44OracleWeight_nonneg
    (fun G t0 ht0 v => mldsa44OracleWeight_le_expect_flatWeight (oraclePrims G) G
      (fun _ => rfl) hβ1 t0 ht0 v)
    (fun G t0 h v => expect_flatWeight_eq_zero_of_mldsa44OracleWeight (oraclePrims G) G
      (fun _ => rfl) βmin t0 h v)
    (fun sk₀ h1 h2 G w hw0 hw hz => expect_signerRegGap_le_sqrt_mldsa44_box_seven_of_nonneg sk₀ h1 h2
      (sampleInBallShape_oraclePrims G) hβ0 hβt hw0 hw hz)
    expect_expect_expect_inv_sq_mldsa44OracleWeight_le).trans_eq ?_
  rw [Real.sqrt_sq (by norm_num)]
  exact div_mul_eq_mul_div _ _ _

end RegGap


/-! ### The check parameters -/

/-- **The check error at the check parameters**: at 355 samples per member, tolerance `2`, the
defect budget `1/2` and `x = 89`, `89² · exp(-(88/89) · 177.5) ≤ 2^-240`, from `89² ≤ 2^13` and
`(88/89) · 177.5 ≥ 253 · log 2` (`log 2 < 0.6931471808`, `Real.log_two_lt_d9`). -/
theorem checkError_checkParams_le : checkError 355 2 (1 / 2) 89 ≤ 1 / 2 ^ 240 := by
  have h2 : Real.exp ((253 : ℕ) * Real.log 2) = 2 ^ 253 := by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]
  have hl := Real.log_two_lt_d9
  have he : Real.exp (-((1 - (89 : ℝ)⁻¹) * ((355 : ℕ) * (1 / 2)))) ≤ 1 / 2 ^ 253 :=
    calc Real.exp (-((1 - (89 : ℝ)⁻¹) * ((355 : ℕ) * (1 / 2))))
        ≤ Real.exp (-((253 : ℕ) * Real.log 2)) :=
          Real.exp_le_exp.2 (by push_cast; norm_num at hl ⊢; linarith)
      _ = 1 / 2 ^ 253 := by rw [Real.exp_neg, h2, one_div]
  unfold checkError
  calc (89 : ℝ) ^ 2 * Real.exp (-((1 - (89 : ℝ)⁻¹) * ((355 : ℕ) * (1 / 2))))
      ≤ 2 ^ 13 * (1 / 2 ^ 253) :=
        mul_le_mul (by norm_num) he (Real.exp_pos _).le (by norm_num)
    _ = 1 / 2 ^ 240 := by norm_num

/-- **The check error from two binary exponents**: `checkError reps tol s x ≤ 2^-240` once
`x^tol ≤ 2^a`, `b · log 2 ≤ (1 - 1/x) · reps · s` and `a + 240 ≤ b`. -/
theorem checkError_le_of {reps tol : ℕ} {s x : ℝ} {a b : ℕ} (hxa : x ^ tol ≤ 2 ^ a)
    (hb : (b : ℝ) * Real.log 2 ≤ (1 - x⁻¹) * (reps * s)) (hab : a + 240 ≤ b) :
    checkError reps tol s x ≤ 1 / 2 ^ 240 := by
  have h2 : Real.exp ((b : ℝ) * Real.log 2) = 2 ^ b := by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]
  have he : Real.exp (-((1 - x⁻¹) * (reps * s))) ≤ 1 / 2 ^ b :=
    calc Real.exp (-((1 - x⁻¹) * (reps * s))) ≤ Real.exp (-((b : ℝ) * Real.log 2)) :=
          Real.exp_le_exp.2 (neg_le_neg hb)
      _ = 1 / 2 ^ b := by rw [Real.exp_neg, h2, one_div]
  unfold checkError
  calc x ^ tol * Real.exp (-((1 - x⁻¹) * (reps * s))) ≤ 2 ^ a * (1 / 2 ^ b) :=
        mul_le_mul hxa he (Real.exp_pos _).le (by positivity)
    _ ≤ 1 / 2 ^ 240 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) hab

/-- **Check parameters**: `reps` samples per member, tolerance `tol`, defect budget `s < 1` and a
Chernoff parameter `x ≥ 1` at which the check error is at most `2^-240`
(`expect_ringCheck_le`). -/
structure CheckParams (reps tol : ℕ) (s x : ℝ) : Prop where
  /-- The Chernoff parameter is at least one. -/
  one_le_x : 1 ≤ x
  /-- The defect budget is below one. -/
  s_lt_one : s < 1
  /-- The check error is at most `2^-240`. -/
  checkError_le : checkError reps tol s x ≤ 1 / 2 ^ 240

/-- **The check parameters with tolerance 2** (`checkError_checkParams_le`): 355 samples per
member, defect budget `1/2`. -/
theorem checkParams_tol2 : CheckParams 355 2 (1 / 2) 89 :=
  ⟨by norm_num, by norm_num, checkError_checkParams_le⟩

/-- **The check parameters with tolerance 8**: 355 samples per member, defect budget `3/5`, at
`x = 26`: `26^8 ≤ 2^38` and `(25/26) · 213 ≥ 278 · log 2`. -/
theorem checkParams_tol8 : CheckParams 355 8 (3 / 5) 26 := by
  refine ⟨by norm_num, by norm_num, checkError_le_of (a := 38) (b := 278) (by norm_num) ?_
    (by norm_num)⟩
  have hl := Real.log_two_lt_d9
  push_cast
  norm_num at hl ⊢
  linarith

/-- **The check parameters with tolerance 16**: 355 samples per member, defect budget `2/3`, at
`x = 15`: `15^16 ≤ 2^63` and `(14/15) · (710/3) ≥ 303 · log 2`. -/
theorem checkParams_tol16 : CheckParams 355 16 (2 / 3) 15 := by
  refine ⟨by norm_num, by norm_num, checkError_le_of (a := 63) (b := 303) (by norm_num) ?_
    (by norm_num)⟩
  have hl := Real.log_two_lt_d9
  push_cast
  norm_num at hl ⊢
  linarith

/-- **The check parameters with tolerance 40**: 355 samples per member, defect budget `5/6`, at
`x = 7`: `7^40 ≤ 2^113` and `(6/7) · (1775/6) ≥ 353 · log 2`. -/
theorem checkParams_tol40 : CheckParams 355 40 (5 / 6) 7 := by
  refine ⟨by norm_num, by norm_num, checkError_le_of (a := 113) (b := 353) (by norm_num) ?_
    (by norm_num)⟩
  have hl := Real.log_two_lt_d9
  push_cast
  norm_num at hl ⊢
  linarith

/-- **The check error below `2^-κ` from two binary exponents**: `checkError reps tol s x ≤ 2^-κ`
once `x^tol ≤ 2^a`, `b · log 2 ≤ (1 - 1/x) · reps · s` and `a + κ ≤ b`. -/
theorem checkError_le_of_bits {reps tol : ℕ} {s x : ℝ} {a b κ : ℕ} (hxa : x ^ tol ≤ 2 ^ a)
    (hb : (b : ℝ) * Real.log 2 ≤ (1 - x⁻¹) * (reps * s)) (hab : a + κ ≤ b) :
    checkError reps tol s x ≤ 1 / 2 ^ κ := by
  have h2 : Real.exp ((b : ℝ) * Real.log 2) = 2 ^ b := by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]
  have he : Real.exp (-((1 - x⁻¹) * (reps * s))) ≤ 1 / 2 ^ b :=
    calc Real.exp (-((1 - x⁻¹) * (reps * s))) ≤ Real.exp (-((b : ℝ) * Real.log 2)) :=
          Real.exp_le_exp.2 (neg_le_neg hb)
      _ = 1 / 2 ^ b := by rw [Real.exp_neg, h2, one_div]
  unfold checkError
  calc x ^ tol * Real.exp (-((1 - x⁻¹) * (reps * s))) ≤ 2 ^ a * (1 / 2 ^ b) :=
        mul_le_mul hxa he (Real.exp_pos _).le (by positivity)
    _ ≤ 1 / 2 ^ κ := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) hab

/-- **Tolerance 2 at check error `2^-300`**: 439 samples per member, defect budget `1/2`, at
`x = 89`: `89² ≤ 2^13` and `(88/89) · (439/2) ≥ 313 · log 2`. -/
theorem checkError_tol2_le_300 : checkError 439 2 (1 / 2) 89 ≤ 1 / 2 ^ 300 := by
  refine checkError_le_of_bits (a := 13) (b := 313) (by norm_num) ?_ (by norm_num)
  have hl := Real.log_two_lt_d9
  push_cast
  norm_num at hl ⊢
  linarith

/-- **Tolerance 8 at check error `2^-300`**: 407 samples per member, defect budget `3/5`, at
`x = 26`: `26^8 ≤ 2^38` and `(25/26) · (1221/5) ≥ 338 · log 2`. -/
theorem checkError_tol8_le_300 : checkError 407 8 (3 / 5) 26 ≤ 1 / 2 ^ 300 := by
  refine checkError_le_of_bits (a := 38) (b := 338) (by norm_num) ?_ (by norm_num)
  have hl := Real.log_two_lt_d9
  push_cast
  norm_num at hl ⊢
  linarith

/-- **Tolerance 16 at check error `2^-300`**: 405 samples per member, defect budget `2/3`, at
`x = 15`: `15^16 ≤ 2^63` and `(14/15) · 270 ≥ 363 · log 2`. -/
theorem checkError_tol16_le_300 : checkError 405 16 (2 / 3) 15 ≤ 1 / 2 ^ 300 := by
  refine checkError_le_of_bits (a := 63) (b := 363) (by norm_num) ?_ (by norm_num)
  have hl := Real.log_two_lt_d9
  push_cast
  norm_num at hl ⊢
  linarith

/-- **Tolerance 40 at check error `2^-300`**: 401 samples per member, defect budget `5/6`, at
`x = 7`: `7^40 ≤ 2^113` and `(6/7) · (2005/6) ≥ 413 · log 2`. -/
theorem checkError_tol40_le_300 : checkError 401 40 (5 / 6) 7 ≤ 1 / 2 ^ 300 := by
  refine checkError_le_of_bits (a := 113) (b := 413) (by norm_num) ?_ (by norm_num)
  have hl := Real.log_two_lt_d9
  push_cast
  norm_num at hl ⊢
  linarith


end GordieHowe.Ring.MLDSAW1
