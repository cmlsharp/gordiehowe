-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Flattened.Core.Weights

@[expose] public section

/-!
# The ML-DSA ring signer publishing `w₁`

Every ring member publishes `(ρ, t₁, t₀)`. The signer `i` repeats idealized FIPS 204 attempts
(`Ideal.lean`: `y` uniform on the mask box, `c̃_i = H(µ_i ‖ w₁)`); for an accepted attempt with
commitment `w₁` it reads every member's hash `c̃_j = H(µ_j ‖ w₁)` and keeps the attempt with
probability `min(1, β_min / aw_i(c̃_i, w₁)) · ∏_{j ≠ i} min(1, aw_j(c̃_j, w₁) / β_min)`, where
`aw_j(c̃, w₁)` is the uniform-`w` acceptance weight of the ct₀ and hint checks with member `j`'s
published `t₀` (`t0Weight`, `acceptWeight`).

The single-key weights, masses, loop signer and regularity gap are those of the flattened signer
(`GordieHowe/Applications/MLDSA/Flattened/Core/Weights.lean`: `t0Weight`, `flatWeight`,
`flatLoopSigner`, `signerRegGap`).

* `ringWeights`: the members' flattened weights `min(1, aw_j / β_min)` as the column weights of
  `PMF.RingWeights`.
* `colDev_le_abs_sub`, `relColError_le_signerRegGap`: the signer's relative column error in the
  ring is at most its regularity gap `signerRegGap`.
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

/-- **The column weights of a ring of published `t₀`s.** -/
def ringWeights {n : ℕ} (βmin : ℚ≥0) (t0s : Fin n → RqVec p.k) :
    PMF.RingWeights (Fin n) (BucketVec p) (CommitHashBytes p) where
  wtQ j := flatWeight prims (Cutoff.const βmin) (t0s j)
  wtQ_le_one _ _ := NNRat.minOneDiv_le_one _ _

end Weights

/-! ### The signer's column error -/

section Signer

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] (sk : SecretKey p) (aHat : TqMatrix p.k p.l)

/-- **The column deviation of the ring signer is at most the column regularity gap**, when the
signer's published `t₀` is its own. -/
theorem colDev_le_abs_sub (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) {n : ℕ} (t0s : Fin n → RqVec p.k) (i : Fin n)
    (hi : t0s i = sk.t0) {βmin : ℚ≥0} (_hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (v : BucketVec p) (c : CommitHashBytes p) :
    colDev (ringWeights prims βmin t0s) i (maskUniform p) (realBuckets aHat)
        (attemptAccept prims sk aHat) (fun a => (flattenCoin prims sk (Cutoff.const βmin) a : ℝ≥0∞))
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
      (zAcceptFraction p * standinMass prims sk v c * flattenCoin prims sk (Cutoff.const βmin) (v,
          c)).toReal := by
    rw [← ENNReal.toReal_mul, hS, mul_assoc (standinScale p) (signerWeight prims sk (v, c)),
      mul_flattenCoin_eq prims sk _]
    simp only [ringWeights, PMF.RingWeights.wt, hi, mul_assoc, ENNReal.nnratCast_one, mul_one]
  have hκ : (flattenCoin prims sk (Cutoff.const βmin) (v, c) : ℝ≥0∞).toReal ≤ 1 :=
    ENNReal.toReal_le_one_of_le_one (coe_flattenCoin_le_one prims sk (Cutoff.const βmin) _)
  rw [colDev_eq, hlev, ENNReal.toReal_mul, ENNReal.toReal_mul, ← sub_mul, abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_of_le_one_right (abs_nonneg _) hκ

/-- **The signer's relative column error is at most its regularity gap.** -/
theorem relColError_le_signerRegGap (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) {n : ℕ} (t0s : Fin n → RqVec p.k) (i : Fin n)
    (hi : t0s i = sk.t0) {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) :
    relColError (ringWeights prims βmin t0s) i (maskUniform p) (realBuckets aHat)
        (attemptAccept prims sk aHat) (fun a => (flattenCoin prims sk (Cutoff.const βmin) a : ℝ≥0∞))
        (standinScale p * βmin).toReal ≤
      signerRegGap prims sk aHat (Cutoff.const βmin) := by
  rw [relColError_eq]
  rw [signerRegGap_const]
  have hden : 0 < (standinScale p * βmin).toReal * Fintype.card (BucketVec p) :=
    mul_pos (flatLevel_pos (cut := Cutoff.const βmin) hp hβ0 hβt) (by exact_mod_cast
        Fintype.card_pos)
  refine div_le_div_of_nonneg_right ?_ hden.le
  refine Finset.sum_le_sum fun v _ => ?_
  have hmean : (ringWeights prims βmin t0s).meanWeight i v =
      𝔼 c, (flatWeight prims (Cutoff.const βmin) sk.t0 (v, c) : ℝ≥0∞).toReal := by
    simp only [PMF.RingWeights.meanWeight_eq, PMF.RingWeights.wt, ringWeights, hi]
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
