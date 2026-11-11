-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.ROMParams
public import GordieHowe.Applications.MLDSA44.Ring.RingBase
public import GordieHowe.Applications.Ring.MLDSARing
public import GordieHowe.Applications.MLDSA.Regularity.WeightTail44

@[expose] public section

/-!
# GordieHowe: the ML-DSA-44 ring signature of `MLDSA44.Ring.Native.ROMParams`

The ring signature `ofBase (mldsaBaseSigner mldsa44 P maxAttempts bmsg) PS adm` (BKM06
Definition 1, `GordieHowe/Applications/Ring/MLDSARing.lean`) at the FIPS 204 signer
`P = prims (Spec.expandS mldsa44) (Spec.expandMask mldsa44)` (`fipsPrims`, which is
`concretePrimitivesFIPS mldsa44` by `GordieHowe.MLDSA44.Ring.prims_fips`), whose proof system `PS`
is the compiled program of `GordieHoweCerts/Applications/MLDSA44/Ring/Native/ROMParams.lean` read at the
ring statements of the base signer (`GordieHowe.MLDSA44.Ring.ringVerifies` at `schemeVerifies`),
and its completeness and anonymity headlines, each an instance of a generic theorem of
`GordieHowe/Applications/Ring/MLDSARing.lean`. The unforgeability headlines are in
`GordieHoweCerts/Applications/MLDSA44/Ring/Native/ROMParams/RingForger.lean`.

The IOP `ringIop msgLen`, its transcript `ringTranscript msgLen` and the honest strategy
`honestStrategy msgLen` are stated at every message length; the setting's facts hold at
`msgLen ≤ 2^19` (`ringMergeBounds`, `ringProofFormat`).

* **The honest prover** `ringHonest msgLen C` at `honestStrategy msgLen`, without completeness
  error (`ringHonest_errorBound`).
* **The statements verify ML-DSA-44 signatures**: `schemeVerifies msgLen` (soundness by
  `ringStmtRel_sound`, the honest input of a pair of the ring relation the pair, `RingIn`), and
  `ringStmtVerifies` at the base signer.
* **The scheme** `scheme msgLen C TA hmsg maxAttempts bmsg` on the base signer `baseSigner` at a
  base message `bmsg`; its two shapes: `convertedScheme C TA maxAttempts` (`bmsg =
  convertedMsg`, `0 ‖ 0 ‖ m`, `2 + 32` bytes) and `bindingScheme C maxAttempts` (`bmsg =
  bindingMsg`, `0 ‖ 0 ‖ (m ‖ encode R)`, `2 + ringMsgLen` bytes, which binds the ring:
  `bindsRing_bindingMsg`).
* **The headlines**: `convertedScheme.completeWithin`, `bindingScheme.completeWithin` (at every
  number of attempts, refusal at most the per-message refusal term `mldsaRefuseMsg`, left symbolic,
  rejection at most spBCS's terms: the base signer has correctness error `0`,
  `mldsaBaseSigner_correctWithin_zero_concrete`, and the honest prover none);
  `convertedScheme.anonAdvantage_le`, `bindingScheme.anonAdvantage_le` (at every number of
  attempts, refusal at most `n` times the worst-message refusal term `mldsaRefuseAvg`, left
  symbolic, correctness error `0`). The per-key forms `convertedScheme.completeAtWithin`,
  `bindingScheme.completeAtWithin` (refusal at most `1`) remain.
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
  GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring GordieHowe.RingSignature
open Generated.MLDSA44.Ring.Native.ROMParams.Program (program)
open Generated.MLDSA44.Ring.Native.ROMParams (interp ready ProofSystems)
open scoped NNReal ENNReal

attribute [local instance] _root_.MLDSA.Concrete.concreteNTTRingOps

/- Generated data: unifying the figures' terms reads the generated program. -/
set_option maxRecDepth 8192

/-! ## The honest prover -/

variable (msgLen : ℕ) (C : ProofSystems)

/-- **The honest prover of `ringIop msgLen`** at the honest strategy `honestStrategy msgLen`
(`RealizedProgram.ProofSystem.fieldIopWithHonest`): the proof system's phased honest prover and
the forked domains' honest provers on the generic per-field domain proofs, read through the
program statement and checked. -/
noncomputable abbrev ringHonest :=
  C.fieldIopWithHonest (ringLowering C)
    (Native.stmtOf (program := program) (I := interp) (len := msgLen)) ringOk
    (honestStrategy msgLen).toHonestCore

/-- **The honest prover has completeness error `0`**
(`RealizedProgram.ProofSystem.FieldBranches.errorBound_honestAt`, `HonestStrategy.complete`,
`honestStrategy_delta`). -/
theorem ringHonest_errorBound :
    (ringHonest msgLen C).app.ErrorBound fun _ => 0 := by
  have h := ((C.fieldBranches ready).errorBound_honestAt (ringLowering C)
    (C.fieldHonestDomains ready)
    (C.fieldForkHonestDomains ready) (honestStrategy msgLen).toHonestCore
    (honestStrategy msgLen).complete).comapWith
      (Native.stmtOf (program := program) (I := interp) (len := msgLen)) ringOk
  rwa [honestStrategy_delta] at h

/-! ## The statements verify ML-DSA-44 signatures -/

/-- **The ring statements of `ringIop msgLen` verify ML-DSA-44 signatures** for the ring relation
on the supported rings (`GordieHowe.Ring.SchemeVerifies` at `ringAdm`): statements checked by
`ringOk`; a witness `f` of the IOP's relation gives the ring witness `ringWit x f`
(`ringStmtRel_sound`); the honest input of a pair of the ring relation is the pair (`RingIn`),
whose program statement is the frontend's (`Native.relH`). -/
def schemeVerifies :
    SchemeVerifies (MLDSA44.Ring.scheme msgLen) 64 (ringStmtRel msgLen)
      (ringHonestRel msgLen
        (Native.relH (msgLen := msgLen) program RealizedProgram.fq6 RealizedProgram.gf128))
      ringAdm where
  check := ringOk
  wit := ringWit
  sound := ringStmtRel_sound
  input x w h := ⟨x, w, h⟩
  check_eq_true x w h := RingIn.ringOk_x ⟨x, w, h⟩
  input_mem x w h := ⟨RingIn.ringOk_x ⟨x, w, h⟩, rfl⟩

/-! ## The base signer and the scheme -/

/-- **The FIPS 204 signer's primitives at ML-DSA-44**: the concrete primitives with FIPS 204's
`ExpandS` and `ExpandMask` (Algorithms 33, 34), `concretePrimitivesFIPS mldsa44`
(`prims_fips`). -/
abbrev fipsPrims : _root_.MLDSA.Primitives _root_.MLDSA.mldsa44 :=
  prims (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
    (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)

/-- The keys of the FIPS 204 signer at ML-DSA-44. -/
abbrev FipsKey : Type := _root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 fipsPrims

variable {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]

/-- **The ML-DSA-44 base signer of the scheme**: the FIPS 204 hedged signer with at most
`maxAttempts` attempts on the base message `bmsg R m` (`mldsaOn` at `fipsPrims`), on the compiled
oracle of `ringTranscript msgLen C` at `32`-byte salts. -/
abbrev baseSigner (maxAttempts : ℕ) (bmsg : KeyRing FipsKey 64 → RMsg → _root_.MLDSA.Bytes msgLen) :=
  mldsaOn _root_.MLDSA.mldsa44 fipsPrims maxAttempts (ringTranscript msgLen C) 32 bmsg

/-- **The supported rings of the base signer are decidable** (`adm`, at the base signer's key
type `(baseSigner msgLen C maxAttempts bmsg).PK`). -/
instance (maxAttempts : ℕ) (bmsg : KeyRing FipsKey 64 → RMsg → _root_.MLDSA.Bytes msgLen) :
    @DecidablePred (KeyRing (baseSigner msgLen C maxAttempts bmsg).PK 64)
      (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
        (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)) :=
  fun R => (inferInstance : DecidablePred (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
    (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))) R

/-- **The ring statements of the base signer verify its signatures** on the supported rings
`adm` (`GordieHowe.MLDSA44.Ring.ringVerifies` at `schemeVerifies msgLen`). -/
noncomputable abbrev ringStmtVerifies (maxAttempts : ℕ)
    (bmsg : KeyRing FipsKey 64 → RMsg → _root_.MLDSA.Bytes msgLen) :=
  MLDSA44.Ring.ringVerifies (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
    (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)
    (Bits (queryBits (ringTranscript msgLen C).k (2 * (ringTranscript msgLen C).k) 32 (2 ^ 40)))
    (XOut (ringTranscript msgLen C).k
      (Configurations.fsExtraBytes + (ringTranscript msgLen C).maxGrant))
    maxAttempts bmsg (schemeVerifies msgLen)

/-- **The ML-DSA-44 ring signature of `MLDSA44.Ring.Native.ROMParams`** at the base message `bmsg`:
`mldsaScheme` (`ofBase (baseSigner msgLen C maxAttempts bmsg) PS adm`) with `PS` the compiled
program read at the base signer's ring statements (`ringStmtVerifies`, the honest prover
`ringHonest msgLen C`, proofs in the format `max 3499 137`), on the supported rings `adm`. -/
noncomputable abbrev scheme (hmsg : msgLen ≤ 2 ^ 19)
    (maxAttempts : ℕ) (bmsg : KeyRing FipsKey 64 → RMsg → _root_.MLDSA.Bytes msgLen) :=
  mldsaScheme _root_.MLDSA.mldsa44 fipsPrims maxAttempts (ringHonest msgLen C)
    (ringMergeBounds C hmsg) (ringProofFormat C hmsg) (ringStmtVerifies msgLen C maxAttempts bmsg)

/-- The ring-binding base messages' length `2 + ringMsgLen` is within the setting's `2^19`
bytes. -/
theorem bindingLen_le : 2 + ringMsgLen ≤ 2 ^ 19 := by norm_num

variable {msgLen}

/-- **The converted ML-DSA-44 ring signature** (`bmsg = convertedMsg`: the `32`-byte ring message
as the representative `0 ‖ 0 ‖ m`). -/
noncomputable abbrev convertedScheme (maxAttempts : ℕ) :=
  scheme (2 + 32) C msgLen_le maxAttempts
    (convertedMsg (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
      (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))

/-- **The ring-binding ML-DSA-44 ring signature** (`bmsg = bindingMsg`: the representative
`0 ‖ 0 ‖ (m ‖ encode R)` of the `32`-byte ring message followed by the ring's bytes). -/
noncomputable abbrev bindingScheme (maxAttempts : ℕ) :=
  scheme (2 + ringMsgLen) C bindingLen_le maxAttempts
    (bindingMsg (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
      (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))

/-! ## The base signer's facts -/

variable (msgLen) in
/-- **The base signer has correctness error `0`** (`mldsaBaseSigner_correctWithin_zero_concrete`
at the approved parameter set ML-DSA-44). -/
theorem baseSigner_correctWithin (maxAttempts : ℕ)
    (bmsg : KeyRing FipsKey 64 → RMsg → _root_.MLDSA.Bytes msgLen) :
    (baseSigner msgLen C maxAttempts bmsg).CorrectWithin 0 :=
  mldsaBaseSigner_correctWithin_zero_concrete GordieHowe.MLDSA.Regularity.isApproved_mldsa44
    (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44) maxAttempts bmsg

/-! ## The headlines -/

/-- **Completeness of the converted ML-DSA-44 ring signature, averaged over honest rings**
(`mldsaScheme.completeWithin`): at every number of attempts, `convertedScheme` refuses with
probability at most the per-message refusal term `mldsaRefuseMsg` at `convertedMsg`
(`refuseWithin_mldsaRefuseMsg`, left symbolic) and is rejected with probability at most the base
signer's correctness error `0` (`baseSigner_correctWithin`) plus the honest prover's completeness
error `0`, spBCS's overrun and key-collision terms and `0 / 2^(8 · 32)`. -/
@[headline]
theorem convertedScheme.completeWithin (maxAttempts : ℕ) :
    (convertedScheme proofSystem maxAttempts).CompleteWithin
      (mldsaRefuseMsg _root_.MLDSA.mldsa44 fipsPrims maxAttempts
        (convertedMsg (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
          (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)))
      (0 + (((0 : ℝ≥0) : ℝ≥0∞) +
        ((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).model.overrun +
        SPBCS.keyCollision ((ringIop (2 + 32) proofSystem).term.size (ringIop (2 + 32) proofSystem).rounds)
          (ringTranscript (2 + 32) proofSystem).k + ((0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ (8 * 32))) :=
  mldsaScheme.completeWithin _ _ _ _ _ _ _ (ringHonest_errorBound _ proofSystem)
    (baseSigner_correctWithin _ proofSystem _ _)

/-- **Completeness of the ring-binding ML-DSA-44 ring signature, averaged over honest rings**
(`mldsaScheme.completeWithin`): as `convertedScheme.completeWithin`, for `bindingScheme`. -/
@[headline]
theorem bindingScheme.completeWithin (maxAttempts : ℕ) :
    (bindingScheme proofSystem maxAttempts).CompleteWithin
      (mldsaRefuseMsg _root_.MLDSA.mldsa44 fipsPrims maxAttempts
        (bindingMsg (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
          (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)))
      (0 + (((0 : ℝ≥0) : ℝ≥0∞) +
        ((ringTranscript (2 + ringMsgLen) proofSystem).setting 32 (ringMergeBounds proofSystem bindingLen_le)).model.overrun +
        SPBCS.keyCollision ((ringIop (2 + ringMsgLen) proofSystem).term.size (ringIop (2 + ringMsgLen) proofSystem).rounds)
          (ringTranscript (2 + ringMsgLen) proofSystem).k + ((0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ (8 * 32))) :=
  mldsaScheme.completeWithin _ _ _ _ _ _ _ (ringHonest_errorBound _ proofSystem)
    (baseSigner_correctWithin _ proofSystem _ _)

/-- **Completeness per key of the converted ML-DSA-44 ring signature**
(`mldsaScheme.completeAtWithin`): at every number of attempts, every key and every supported ring
holding it, `convertedScheme` refuses with probability at most `1` (`BaseSigner.refuseAtWithin_one`)
and is rejected with probability at most the base signer's correctness error `0` plus the honest
prover's completeness error `0`, spBCS's overrun and key-collision terms and `0 / 2^(8 · 32)`. -/
theorem convertedScheme.completeAtWithin (maxAttempts : ℕ) :
    (convertedScheme C maxAttempts).CompleteAtWithin 1
      (0 + (((0 : ℝ≥0) : ℝ≥0∞) +
        ((ringTranscript (2 + 32) C).setting 32 (ringMergeBounds C msgLen_le)).model.overrun +
        SPBCS.keyCollision ((ringIop (2 + 32) C).term.size (ringIop (2 + 32) C).rounds)
          (ringTranscript (2 + 32) C).k + ((0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ (8 * 32))) :=
  mldsaScheme.completeAtWithin _ _ _ _ _ _ _ (ringHonest_errorBound _ C)
    (BaseSigner.refuseAtWithin_one _ _) (baseSigner_correctWithin _ C _ _)

/-- **Completeness per key of the ring-binding ML-DSA-44 ring signature**
(`mldsaScheme.completeAtWithin`): as `convertedScheme.completeAtWithin`, for `bindingScheme`. -/
theorem bindingScheme.completeAtWithin (maxAttempts : ℕ) :
    (bindingScheme C maxAttempts).CompleteAtWithin 1
      (0 + (((0 : ℝ≥0) : ℝ≥0∞) +
        ((ringTranscript (2 + ringMsgLen) C).setting 32 (ringMergeBounds C bindingLen_le)).model.overrun +
        SPBCS.keyCollision ((ringIop (2 + ringMsgLen) C).term.size (ringIop (2 + ringMsgLen) C).rounds)
          (ringTranscript (2 + ringMsgLen) C).k + ((0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ (8 * 32))) :=
  mldsaScheme.completeAtWithin _ _ _ _ _ _ _ (ringHonest_errorBound _ C)
    (BaseSigner.refuseAtWithin_one _ _) (baseSigner_correctWithin _ C _ _)

/-- **Anonymity against full key exposure (BKM06 Definition 4, `Q` adaptive challenges) of the
converted ML-DSA-44 ring signature** (`mldsaScheme.anonAdvantage_le`): at every number of
attempts, every anonymity adversary (any oracle view, at most `t` queries) has advantage at most
`Q · wiError 0 (Q · |AnonRequest|) + 2Q · 0 + Q · n · mldsaRefuseAvg` (the honest prover has no
completeness error, the base signer has correctness error `0` and refuses with probability at most
the worst-message refusal term `mldsaRefuseAvg` averaged over the keys,
`refuseAvgWithin_mldsaRefuseAvg`, left symbolic). -/
@[headline]
theorem convertedScheme.anonAdvantage_le (maxAttempts : ℕ) {n : ℕ}
    {Vw : OracleView _ _} {t : ℕ}
    (A : AnonAdversary (convertedScheme proofSystem maxAttempts) n Vw t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * ((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).model.wiError 0
          (Q * Fintype.card (AnonRequest (convertedScheme proofSystem maxAttempts) n)) +
        2 * Q * ((0 : ℝ≥0) : ℝ) +
          Q * n * (mldsaRefuseAvg _root_.MLDSA.mldsa44 fipsPrims maxAttempts).toReal :=
  mldsaScheme.anonAdvantage_le _ _ _ _ _ _ _ (ringHonest_errorBound _ proofSystem)
    (by simpa using baseSigner_correctWithin _ proofSystem maxAttempts _) A Q

/-- **Anonymity against full key exposure (BKM06 Definition 4, `Q` adaptive challenges) of the
ring-binding ML-DSA-44 ring signature** (`mldsaScheme.anonAdvantage_le`): the bound of
`convertedScheme.anonAdvantage_le` for `bindingScheme`. -/
@[headline]
theorem bindingScheme.anonAdvantage_le (maxAttempts : ℕ) {n : ℕ}
    {Vw : OracleView _ _} {t : ℕ}
    (A : AnonAdversary (bindingScheme proofSystem maxAttempts) n Vw t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * ((ringTranscript (2 + ringMsgLen) proofSystem).setting 32
          (ringMergeBounds proofSystem bindingLen_le)).model.wiError 0
          (Q * Fintype.card (AnonRequest (bindingScheme proofSystem maxAttempts) n)) +
        2 * Q * ((0 : ℝ≥0) : ℝ) +
          Q * n * (mldsaRefuseAvg _root_.MLDSA.mldsa44 fipsPrims maxAttempts).toReal :=
  mldsaScheme.anonAdvantage_le _ _ _ _ _ _ _ (ringHonest_errorBound _ proofSystem)
    (by simpa using baseSigner_correctWithin _ proofSystem maxAttempts _) A Q

end GordieHowe.MLDSA44.Ring.Native.ROMParams
