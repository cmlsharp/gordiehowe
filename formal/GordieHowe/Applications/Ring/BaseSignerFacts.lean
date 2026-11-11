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
  some signer carries the salt (`Falcon512.exists_carriesSalt`,
  `GordieHowe/Applications/Falcon512/Spec/Signer.lean`).
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

open GordieHowe.Falcon512 (Signer PublicKey)

variable {msgLen : ℕ} (G : Signer msgLen) {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  (bmsg : KeyRing PublicKey N → RMsg → (Fin msgLen → UInt8))

variable [Fintype G.SignCoins] [Nonempty G.SignCoins]

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

omit [Fintype G.SignCoins] [Nonempty G.SignCoins] in
/-- **The Falcon-512 base signer never refuses, as a function of the coins**: its refusals are the
empty predicate (`BaseSigner.RefusalOfCoins`). -/
theorem falconBaseSigner_refusalOfCoins :
    (falconBaseSigner (X := X) (Y := Y) G bmsg).RefusalOfCoins fun _ _ _ _ => False := by
  intro H kc R i _ m c
  exact ⟨fun h => Option.some_ne_none _ h, False.elim⟩

omit [Fintype G.SignCoins] [Nonempty G.SignCoins] in
/-- **The Falcon-512 base signer is oracle-free**: its signers and public value make no queries
and its verification reads no oracle. -/
theorem falconBaseSigner_oracleFree : (falconBaseSigner (X := X) (Y := Y) G bmsg).OracleFree where
  bsign_noQuery := (falconBaseSigner (X := X) (Y := Y) G bmsg).bsign_queries
  ssign_noQuery := (falconBaseSigner (X := X) (Y := Y) G bmsg).ssign_queries
  pub_noQuery := (falconBaseSigner (X := X) (Y := Y) G bmsg).pub_queries
  bverify_eq _ _ := rfl

omit [Fintype G.SignCoins] [Nonempty G.SignCoins] in
/-- **Falcon-512's base verification and salt read no oracle** (`falconBaseSigner_oracleFree`,
`OracleFree.verifiesWithoutOracle`). -/
theorem falconBaseSigner_verifiesWithoutOracle :
    (falconBaseSigner (X := X) (Y := Y) G bmsg).VerifiesWithoutOracle :=
  (falconBaseSigner_oracleFree G bmsg).verifiesWithoutOracle

omit [Fintype G.SignCoins] [Nonempty G.SignCoins] in
/-- **The public value of an honest Falcon-512 base signature is the drawn salt** for a signer
whose signatures carry it (`hG`). -/
theorem falconBaseSigner_pubOfCoins (hG : G.CarriesSalt) :
    (falconBaseSigner (X := X) (Y := Y) G bmsg).PubOfCoins Prod.fst := by
  intro H kc R i _ m c σ hσ
  change some (G.signWith _ (bmsg R m) c.1 c.2) = some σ at hσ
  obtain rfl := Option.some.inj hσ
  exact hG _ _ _ _

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
    ((verifyLaws_concrete hp).withSigning _ eM)
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
    ((verifyLaws_concrete hp).withSigning _ eM)
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
  mldsaBaseSigner_correctWithin_zero p _ maxAttempts bmsg (signingLaws_concreteKeyGen p hp)
    (verifyLaws_concreteKeyGen hp) (keyGenFromSeed_s2_bounded hp)

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
    (signingLaws_concreteKeyGen p hp) (verifyLaws_concreteKeyGen hp)
    (keyGenFromSeed_s2_bounded hp)

end MLDSAConcrete

end GordieHowe.Ring
