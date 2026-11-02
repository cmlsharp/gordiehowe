-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.BaseSigners
public import GordieHowe.Model.RingSignature.BaseCompleteness

@[expose] public section

/-!
# Completeness facts of the generic base signers

The hypotheses of the completeness theorems (`GordieHowe/Model/RingSignature/BaseCompleteness.lean`,
`GordieHowe/Applications/Ring/SPBCSCompleteness.lean`) that hold for the base signers of
`GordieHowe/Applications/Ring/BaseSigners.lean` by their definitions.

- `falconBaseSigner_refuseAtWithin`: the Falcon-512 base signer never refuses (`RefuseAtWithin` at
  `0` on every supported ring); `falconBaseSigner_refusal_le_zero`: at every input;
  `falconBaseSigner_refusalOfCoins`: its refusals are the empty predicate of the coins.
- `falconBaseSigner_oracleFree`, `mldsaBaseSigner_oracleFree`: neither makes an oracle query
  (`BaseSigner.OracleFree`); hence `falconBaseSigner_verifiesWithoutOracle`,
  `mldsaBaseSigner_verifiesWithoutOracle`: their base verification and public values read no
  oracle (`BaseSigner.OracleFree.verifiesWithoutOracle`).
- `falconBaseSigner_pubOfCoins`: for a signer whose signatures carry the drawn salt
  (`Signer.CarriesSalt`), the public value is the salt of the coins (`BaseSigner.PubOfCoins`);
  `exists_carriesSalt`: some signer carries the salt (satisfiability).
- `mldsaBaseSigner_refusal_le_one`: the ML-DSA base signer refuses with probability at most `1` at
  every input (satisfiability of a refusal bound).
- `fipsVerify_of_fipsSignWith`: a signature of the hedged signer `fipsSignWith` verifies by FIPS
  204 (`fipsVerify`, Algorithm 8) under the key generated with it (Algorithm 6), given the signing
  and verification laws (`SigningLaws`, `VerifyLaws`) and `‖s₂‖∞ ≤ η`;
  `bverify_of_fipsSignWith`: it passes the base verification `boundedOk && fipsVerify`.
- `mldsaBaseSigner_correctWithin_zero`, `mldsaBaseSigner_stdCorrectWithin_zero`: under these
  laws and `‖s₂‖∞ ≤ η` for every generated key, the ring-aware and the ordinary ML-DSA signers
  have correctness error `0` (`BaseSigner.CorrectWithin`, `BaseSigner.StdCorrectWithin`).
- `SigningLaws.withSigning`, `VerifyLaws.withSigning`, `keyGenFromSeed_s2_withSigning`: the laws
  and the generated `s₂` do not read `ExpandMask` (nor, for the laws, `ExpandS`), for an abstract
  bundle `P`.
- `mldsaBaseSigner_correctWithin_zero_concreteKeyGen`,
  `mldsaBaseSigner_stdCorrectWithin_zero_concreteKeyGen`: correctness error `0` at the concrete
  primitives with the FIPS 204 `ExpandS` (`concretePrimitivesKeyGen p`), at every approved
  parameter set; `mldsaBaseSigner_correctWithin_zero_concrete`,
  `mldsaBaseSigner_stdCorrectWithin_zero_concrete`: likewise at
  `{concretePrimitives p with expandS := expandS p, expandMask := eM}` for every `ExpandMask` `eM`.
-/

namespace GordieHowe.Ring

open GordieHowe.RingSignature
open scoped NNReal ENNReal

variable {X Y : Type} {N : ℕ}

section Falcon

open GordieHowe.Falcon512.Ring.Native

variable {msgLen : ℕ} (G : Signer msgLen) {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  (bmsg : KeyRing PublicKey N → RMsg → (Fin msgLen → UInt8))

/-- **The Falcon-512 base signer never refuses**: its per-key refusal rate is `0` on every set
`adm` of supported rings. -/
theorem falconBaseSigner_refuseAtWithin (adm : KeyRing PublicKey N → Prop) :
    (falconBaseSigner (X := X) (Y := Y) G bmsg).RefuseAtWithin adm 0 := by
  intro H kc R _ _ m
  refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
  refine Set.disjoint_left.2 fun c _ hc => ?_
  simp only [Set.mem_ofPred_eq] at hc
  exact Option.some_ne_none _ hc

/-- **The Falcon-512 base signer refuses with probability `0` at every input.** -/
theorem falconBaseSigner_refusal_le_zero (H : X → Y) (kc : G.KeyCoins) (R : KeyRing PublicKey N)
    (i : ℕ) (m : RMsg) :
    Pr[cb ~ PMF.uniformOfFintype (falconBaseSigner (X := X) (Y := Y) G bmsg).Coins :
      ((falconBaseSigner (X := X) (Y := Y) G bmsg).bsign
        ((falconBaseSigner (X := X) (Y := Y) G bmsg).sk kc) R i m cb).run H = none] ≤
      ((0 : ℝ≥0) : ℝ≥0∞) := by
  refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
  refine Set.disjoint_left.2 fun c _ hc => ?_
  simp only [Set.mem_ofPred_eq] at hc
  exact Option.some_ne_none _ hc

/-- **The Falcon-512 base signer never refuses, as a function of the coins**: its refusals are the
empty predicate (`BaseSigner.RefusalOfCoins`). -/
theorem falconBaseSigner_refusalOfCoins :
    (falconBaseSigner (X := X) (Y := Y) G bmsg).RefusalOfCoins fun _ _ _ _ => False := by
  intro H kc R i _ m c
  exact ⟨fun h => Option.some_ne_none _ h, False.elim⟩

/-- **The Falcon-512 base signer is oracle-free**: its signers and public value make no queries
and its verification reads no oracle. -/
theorem falconBaseSigner_oracleFree : (falconBaseSigner (X := X) (Y := Y) G bmsg).OracleFree where
  bsign_noQuery := (falconBaseSigner (X := X) (Y := Y) G bmsg).bsign_queries
  ssign_noQuery := (falconBaseSigner (X := X) (Y := Y) G bmsg).ssign_queries
  pub_noQuery := (falconBaseSigner (X := X) (Y := Y) G bmsg).pub_queries
  bverify_eq _ _ := rfl

/-- **Falcon-512's base verification and salt read no oracle** (`falconBaseSigner_oracleFree`,
`OracleFree.verifiesWithoutOracle`). -/
theorem falconBaseSigner_verifiesWithoutOracle :
    (falconBaseSigner (X := X) (Y := Y) G bmsg).VerifiesWithoutOracle :=
  (falconBaseSigner_oracleFree G bmsg).verifiesWithoutOracle

/-- **The public value of an honest Falcon-512 base signature is the drawn salt** for a signer
whose signatures carry it (`hG`). -/
theorem falconBaseSigner_pubOfCoins (hG : G.CarriesSalt) :
    (falconBaseSigner (X := X) (Y := Y) G bmsg).PubOfCoins Prod.fst := by
  intro H kc R i _ m c σ hσ
  change some (G.signWith _ (bmsg R m) c.1 c.2) = some σ at hσ
  obtain rfl := Option.some.inj hσ
  exact hG _ _ _ _

variable (msgLen) in
/-- **Some Falcon-512 signer carries the drawn salt**: the signer with one key and one private coin
whose signature is the salt with zero compressed bytes (`Sig.equiv`). -/
theorem exists_carriesSalt : ∃ G : Signer msgLen, G.CarriesSalt :=
  ⟨{ SK := Unit
     KeyCoins := Unit
     SignCoins := Unit
     keyGen := fun _ => (default, ())
     signWith := fun _ _ r _ => Sig.equiv.symm (r, Vector.replicate sigBytes 0) },
    fun _ _ _ _ => rfl⟩

end Falcon

section MLDSA

open _root_.MLDSA

variable (p : Params) (prims : Primitives p) [NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] (maxAttempts : ℕ)
  {len : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg] (bmsg : KeyRing (PublicKey p prims) N → RMsg → Bytes len)

/-- **The ML-DSA base signer is oracle-free**: its signers and public value make no queries and
its verification reads no oracle. -/
theorem mldsaBaseSigner_oracleFree :
    (mldsaBaseSigner (X := X) (Y := Y) p prims maxAttempts bmsg).OracleFree where
  bsign_noQuery := (mldsaBaseSigner (X := X) (Y := Y) p prims maxAttempts bmsg).bsign_queries
  ssign_noQuery := (mldsaBaseSigner (X := X) (Y := Y) p prims maxAttempts bmsg).ssign_queries
  pub_noQuery := (mldsaBaseSigner (X := X) (Y := Y) p prims maxAttempts bmsg).pub_queries
  bverify_eq _ _ := rfl

/-- **ML-DSA's base verification (`fipsVerify`) and public value (`Unit`) read no oracle**
(`mldsaBaseSigner_oracleFree`, `OracleFree.verifiesWithoutOracle`). -/
theorem mldsaBaseSigner_verifiesWithoutOracle :
    (mldsaBaseSigner (X := X) (Y := Y) p prims maxAttempts bmsg).VerifiesWithoutOracle :=
  (mldsaBaseSigner_oracleFree p prims maxAttempts bmsg).verifiesWithoutOracle

/-- **The ML-DSA base signer refuses with probability at most `1` at every input.** -/
theorem mldsaBaseSigner_refusal_le_one (H : X → Y) (kc : Bytes 32)
    (R : KeyRing (PublicKey p prims) N) (i : ℕ) (m : RMsg) :
    Pr[cb ~ PMF.uniformOfFintype (mldsaBaseSigner (X := X) (Y := Y) p prims maxAttempts bmsg).Coins :
      ((mldsaBaseSigner (X := X) (Y := Y) p prims maxAttempts bmsg).bsign
        ((mldsaBaseSigner (X := X) (Y := Y) p prims maxAttempts bmsg).sk kc) R i m cb).run H =
          none] ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by
  rw [ENNReal.coe_one]
  exact PMF.toOuterMeasure_apply_le_one _ _

/-! ### Correctness of the ML-DSA base signer -/

section Correctness

open GordieHowe.MLDSA LatticeCrypto TransformOps

/-- **A signature of the hedged signer verifies by FIPS 204** (Algorithm 8, `fipsVerify`) under
the key generated with it: for the key `(pk, sk)` of `seed` (Algorithm 6) with `‖s₂‖∞ ≤ η`, every
signature `fipsSignWith` outputs is accepted, given the signing and verification laws. The
argument of the vendored `fipsSign_fipsVerify_correct'` at the kept attempt. -/
theorem fipsVerify_of_fipsSignWith {p : Params} {prims : Primitives p} (h_laws : SigningLaws prims)
    (hv : VerifyLaws prims)
    {seed : Bytes 32} {pk : PublicKey p prims} {sk : SecretKey p}
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (hs2 : polyVecBounded sk.s2 p.eta)
    {maxAttempts : ℕ} {msg : List Byte} {rnd : Bytes 32} {σ : FIPSSignature p prims}
    (h : fipsSignWith p prims maxAttempts sk msg rnd = some σ) :
    fipsVerify p prims pk msg σ = true := by
  have hpk := congrArg Prod.fst hkeygen
  have hsk := congrArg Prod.snd hkeygen
  subst hpk hsk
  obtain ⟨i, hatt, -⟩ := exists_attempt_of_fipsSignWith p prims h
  have hrho : (keyGenFromSeed p prims seed).2.rho = (keyGenFromSeed p prims seed).1.rho := rfl
  rw [hrho] at hatt
  set aHat := prims.expandA (keyGenFromSeed p prims seed).1.rho
  set sk := (keyGenFromSeed p prims seed).2
  set pk := (keyGenFromSeed p prims seed).1
  have htr : sk.tr = prims.hashPublicKey pk.rho pk.t1 := rfl
  set mu := prims.hashMessage sk.tr msg
  set y := prims.expandMask (prims.hashPrivateSeed sk.key rnd mu) (i * p.l)
  set cT := prims.hashCommitment mu (prims.w1Encode (prims.highBitsVec (aHat * y)))
  set c := prims.sampleInBall cT
  unfold fipsSignAttempt at hatt
  dsimp only at hatt
  split_ifs at hatt with h_outer h_inner
  rw [Option.some.injEq] at hatt
  subst hatt
  obtain ⟨hz, hr0⟩ := h_outer
  obtain ⟨hct0, hw⟩ := h_inner
  have hcs2 : polyVecNorm (c • sk.s2) ≤ p.beta :=
    SigningLaws.polyVecNorm_sampleInBall_smul_le prims h_laws cT sk.s2 hs2
  have hrec : prims.useHintVec (prims.makeHintVec (-(c • sk.t0)) (aHat * y - c • sk.s2 + c • sk.t0))
      (computeWApprox p prims aHat c (y + c • sk.s1) pk.t1) = prims.highBitsVec (aHat * y) := by
    rw [hv.wApprox_eq prims (pk := pk) (sk := sk) seed rfl c y]
    refine useHintVec_makeHintVec_eq_highBitsVec p prims hv.useHint_makeHint h_laws.hide_low
      (aHat * y) (c • sk.s2) (c • sk.t0) hct0 hr0 fun j => ?_
    have hj : polyNorm ((c • sk.s2).get j) ≤ p.beta :=
      le_trans (LatticeCrypto.PolyVec.component_cInfNorm_le normOps (c • sk.s2) j) hcs2
    unfold polyNorm normOps at hj
    simpa [LatticeCrypto.zmodPolyNormOps, LatticeCrypto.normOpsOfCenteredView,
      LatticeCrypto.cInfNorm] using hj
  unfold fipsVerify
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hz, ?_⟩, hw⟩
  rw [← htr]
  exact congrArg (fun w => prims.hashCommitment mu (prims.w1Encode w)) hrec

/-- **A signature of the hedged signer passes the base verification** of `mldsaBaseSigner`
(`boundedOk p ρ c̃ && fipsVerify`) under the key generated with it: the bounded-sampling check
holds at `pk.ρ = sk.ρ` by the signer's filter (`boundedOk_of_fipsSignWith`), and FIPS 204
verification by `fipsVerify_of_fipsSignWith`. -/
theorem bverify_of_fipsSignWith {p : Params} {prims : Primitives p} (h_laws : SigningLaws prims)
    (hv : VerifyLaws prims)
    {seed : Bytes 32} (hs2 : polyVecBounded (keyGenFromSeed p prims seed).2.s2 p.eta)
    {maxAttempts : ℕ} {msg : List Byte} {rnd : Bytes 32} {σ : FIPSSignature p prims}
    (h : fipsSignWith p prims maxAttempts (keyGenFromSeed p prims seed).2 msg rnd = some σ) :
    (boundedOk p (keyGenFromSeed p prims seed).1.rho σ.cTilde &&
      fipsVerify p prims (keyGenFromSeed p prims seed).1 msg σ) = true := by
  have hrho : (keyGenFromSeed p prims seed).2.rho = (keyGenFromSeed p prims seed).1.rho := rfl
  rw [Bool.and_eq_true, ← hrho]
  exact ⟨boundedOk_of_fipsSignWith p prims h,
    fipsVerify_of_fipsSignWith h_laws hv rfl hs2 h⟩

variable (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
  (hs2 : ∀ seed, polyVecBounded (keyGenFromSeed p prims seed).2.s2 p.eta)

include h_laws hv hs2

/-- **The ML-DSA base signer has correctness error `0`** (`BaseSigner.CorrectWithin`): at every
oracle, key, ring and message, every signature the ring-aware signer outputs passes the base
verification, given the signing and verification laws and `‖s₂‖∞ ≤ η` for every generated key
(`bverify_of_fipsSignWith`). -/
theorem mldsaBaseSigner_correctWithin_zero :
    (mldsaBaseSigner (X := X) (Y := Y) p prims maxAttempts bmsg).CorrectWithin 0 := by
  intro H kc R i _ m
  refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
  refine Set.disjoint_left.2 fun c _ hc => ?_
  obtain ⟨σ, hσ, hver⟩ := hc
  have := bverify_of_fipsSignWith h_laws hv (hs2 kc) hσ
  exact Bool.noConfusion (this.symm.trans hver)

/-- **The ordinary ML-DSA signer has correctness error `0`** (`BaseSigner.StdCorrectWithin`):
at every oracle, key and base message, every signature the ordinary signer outputs passes the
base verification, under the hypotheses of `mldsaBaseSigner_correctWithin_zero`. -/
theorem mldsaBaseSigner_stdCorrectWithin_zero :
    (mldsaBaseSigner (X := X) (Y := Y) p prims maxAttempts bmsg).StdCorrectWithin 0 := by
  intro H kc bm
  refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
  refine Set.disjoint_left.2 fun c _ hc => ?_
  obtain ⟨σ, hσ, hver⟩ := hc
  have := bverify_of_fipsSignWith h_laws hv (hs2 kc) hσ
  exact Bool.noConfusion (this.symm.trans hver)

end Correctness

end MLDSA

/-! ### Correctness at the concrete primitives -/

section MLDSAConcrete

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA GordieHowe.MLDSA.Spec

variable {p : Params}

/-- **The signing laws do not read `ExpandS` or `ExpandMask`**: they hold at
`{P with expandS := eS, expandMask := eM}` when they hold at `P` (stated for an abstract bundle
`P`, so that no concrete primitive is unfolded). -/
theorem _root_.GordieHowe.MLDSA.SigningLaws.withSigning [NTTRingOps] {P : Primitives p}
    (h : SigningLaws P)    (eS : Bytes 64 → RqVec p.l × RqVec p.k) (eM : Bytes 64 → ℕ → RqVec p.l) :
    SigningLaws { P with expandS := eS, expandMask := eM } :=
  ⟨h.transform, h.hide_low, h.sampleInBall_smul_bound⟩

/-- **The verification laws do not read `ExpandS` or `ExpandMask`** (for an abstract bundle
`P`). -/
theorem _root_.GordieHowe.MLDSA.VerifyLaws.withSigning [NTTRingOps] {P : Primitives p}
    (h : VerifyLaws P)    (eS : Bytes 64 → RqVec p.l × RqVec p.k) (eM : Bytes 64 → ℕ → RqVec p.l) :
    VerifyLaws { P with expandS := eS, expandMask := eM } :=
  ⟨h.transform, h.power2Round_decomp, h.useHint_makeHint⟩

/-- **Key generation does not read `ExpandMask`**: the secret `s₂` generated at
`{P with expandS := eS, expandMask := eM}` is the one generated at `{P with expandS := eS}` (for
an abstract bundle `P`). -/
theorem keyGenFromSeed_s2_withSigning [NTTRingOps] (P : Primitives p)
    (eS : Bytes 64 → RqVec p.l × RqVec p.k) (eM : Bytes 64 → ℕ → RqVec p.l) (seed : Bytes 32) :
    (keyGenFromSeed p { P with expandS := eS, expandMask := eM } seed).2.s2 =
      (keyGenFromSeed p { P with expandS := eS } seed).2.s2 :=
  rfl

attribute [local instance] concreteNTTRingOps

/-- **The ML-DSA base signer at the concrete primitives with the FIPS 204 `ExpandS` and any
`ExpandMask` `eM` has correctness error `0`**, at every approved parameter set: the bundle
`{concretePrimitives p with expandS := expandS p, expandMask := eM}`
(`mldsaBaseSigner_correctWithin_zero` with `signingLaws_concrete`, `verifyLaws_concrete` and
`keyGenFromSeed_s2_bounded`). -/
theorem mldsaBaseSigner_correctWithin_zero_concrete (hp : p.isApproved)
    (eM : Bytes 64 → ℕ → RqVec p.l)
    [Fintype (Primitives.Power2High
      { concretePrimitives p with expandS := Spec.expandS p, expandMask := eM })]
    [DecidableEq (Primitives.Power2High
      { concretePrimitives p with expandS := Spec.expandS p, expandMask := eM })]
    [Fintype (Primitives.Hint
      { concretePrimitives p with expandS := Spec.expandS p, expandMask := eM })]
    [DecidableEq (Primitives.Hint
      { concretePrimitives p with expandS := Spec.expandS p, expandMask := eM })]
    (maxAttempts : ℕ) {len : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PublicKey p
      { concretePrimitives p with expandS := Spec.expandS p, expandMask := eM }) N →
      RMsg → Bytes len) :
    (mldsaBaseSigner (X := X) (Y := Y) p
      { concretePrimitives p with expandS := Spec.expandS p, expandMask := eM } maxAttempts
      bmsg).CorrectWithin 0 :=
  mldsaBaseSigner_correctWithin_zero p _ maxAttempts bmsg
    ((signingLaws_concrete p hp).withSigning _ eM)
    ((MLDSAW1.verifyLaws_concrete hp).withSigning _ eM)
    fun seed => (keyGenFromSeed_s2_withSigning _ _ eM seed).symm ▸
      keyGenFromSeed_s2_bounded hp seed

/-- **The ordinary ML-DSA signer at the concrete primitives with the FIPS 204 `ExpandS` and any
`ExpandMask` `eM` has correctness error `0`**, at every approved parameter set
(`mldsaBaseSigner_stdCorrectWithin_zero`). -/
theorem mldsaBaseSigner_stdCorrectWithin_zero_concrete (hp : p.isApproved)
    (eM : Bytes 64 → ℕ → RqVec p.l)
    [Fintype (Primitives.Power2High
      { concretePrimitives p with expandS := Spec.expandS p, expandMask := eM })]
    [DecidableEq (Primitives.Power2High
      { concretePrimitives p with expandS := Spec.expandS p, expandMask := eM })]
    [Fintype (Primitives.Hint
      { concretePrimitives p with expandS := Spec.expandS p, expandMask := eM })]
    [DecidableEq (Primitives.Hint
      { concretePrimitives p with expandS := Spec.expandS p, expandMask := eM })]
    (maxAttempts : ℕ) {len : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PublicKey p
      { concretePrimitives p with expandS := Spec.expandS p, expandMask := eM }) N →
      RMsg → Bytes len) :
    (mldsaBaseSigner (X := X) (Y := Y) p
      { concretePrimitives p with expandS := Spec.expandS p, expandMask := eM } maxAttempts
      bmsg).StdCorrectWithin 0 :=
  mldsaBaseSigner_stdCorrectWithin_zero p _ maxAttempts bmsg
    ((signingLaws_concrete p hp).withSigning _ eM)
    ((MLDSAW1.verifyLaws_concrete hp).withSigning _ eM)
    fun seed => (keyGenFromSeed_s2_withSigning _ _ eM seed).symm ▸
      keyGenFromSeed_s2_bounded hp seed

/-- **The ML-DSA base signer at the concrete primitives with the FIPS 204 `ExpandS`
(`concretePrimitivesKeyGen`) has correctness error `0`**, at every approved parameter set
(`mldsaBaseSigner_correctWithin_zero` with `signingLaws_concreteKeyGen`,
`verifyLaws_concreteKeyGen` and `keyGenFromSeed_s2_bounded`). -/
theorem mldsaBaseSigner_correctWithin_zero_concreteKeyGen (hp : p.isApproved)
    [Fintype (concretePrimitivesKeyGen p).Power2High]
    [DecidableEq (concretePrimitivesKeyGen p).Power2High]
    [Fintype (concretePrimitivesKeyGen p).Hint] [DecidableEq (concretePrimitivesKeyGen p).Hint]
    (maxAttempts : ℕ) {len : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PublicKey p (concretePrimitivesKeyGen p)) N → RMsg → Bytes len) :
    (mldsaBaseSigner (X := X) (Y := Y) p (concretePrimitivesKeyGen p) maxAttempts
      bmsg).CorrectWithin 0 :=
  mldsaBaseSigner_correctWithin_zero p _ maxAttempts bmsg (MLDSAW1.signingLaws_concreteKeyGen p hp)
    (MLDSAW1.verifyLaws_concreteKeyGen hp) (keyGenFromSeed_s2_bounded hp)

/-- **The ordinary ML-DSA signer at `concretePrimitivesKeyGen` has correctness error `0`**, at
every approved parameter set (`mldsaBaseSigner_stdCorrectWithin_zero`). -/
theorem mldsaBaseSigner_stdCorrectWithin_zero_concreteKeyGen (hp : p.isApproved)
    [Fintype (concretePrimitivesKeyGen p).Power2High]
    [DecidableEq (concretePrimitivesKeyGen p).Power2High]
    [Fintype (concretePrimitivesKeyGen p).Hint] [DecidableEq (concretePrimitivesKeyGen p).Hint]
    (maxAttempts : ℕ) {len : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PublicKey p (concretePrimitivesKeyGen p)) N → RMsg → Bytes len) :
    (mldsaBaseSigner (X := X) (Y := Y) p (concretePrimitivesKeyGen p) maxAttempts
      bmsg).StdCorrectWithin 0 :=
  mldsaBaseSigner_stdCorrectWithin_zero p _ maxAttempts bmsg
    (MLDSAW1.signingLaws_concreteKeyGen p hp) (MLDSAW1.verifyLaws_concreteKeyGen hp)
    (keyGenFromSeed_s2_bounded hp)

end MLDSAConcrete

end GordieHowe.Ring
