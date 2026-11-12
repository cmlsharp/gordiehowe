-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.QROMParams.RingScheme

@[expose] public section

/-!
# The ML-DSA-44 ring signatures of `MLDSA44.Ring.Native.QROMParams` from MU-EUF-CMA^corr

The unforgeability headlines of the ring signatures of
`GordieHoweCerts/Applications/MLDSA44/Ring/Native/QROMParams/RingScheme.lean`, each an instance of a
generic theorem of `GordieHowe/Applications/Ring/MLDSARing.lean`.

- `bindingBase`, `bindingV`, `bindingPS`, `bindingQ'`, `bindingExtractor`: the base signer, the
  statement map and the proof system of `bindingScheme`, the number of multi-user requests of the
  reduction (`ringStdRequests`) and the binding route's extractor (`StmtVerifiesRing.ringExtractor`).
- `bindingScheme.insiderForgeProb_le`,
  `bindingScheme.jointForgeProb_le`
  (`mldsaScheme.insiderForgeProb_le_of_bindsRing`,
  `mldsaScheme.jointForgeProb_le_of_bindsRing` at `bindsRing_bindingMsg`): the forgery
  probability of BKM06 Definition 7 and of the joint-security game against `bindingScheme` is at most
  the success probability of the binding route's base-scheme forger (`insiderStdForger`,
  `jointStdForger` at `bindingExtractor`) in the base scheme's standard game `SignOracle.std`, with
  at most `Q` signing and corruption requests, plus spBCS's knowledge error `ksError` at the
  configuration's largest round error, at the default fallback forgery (the `_of` forms for every
  fallback forgery). The ring-oracle forms
  `bindingScheme.insiderForgeProb_le_muEufProbWithin`,
  `bindingScheme.jointForgeProb_le_muEufProbWithin` remain.
- `convertedBase`, `convertedV`, `convertedSim`: the base signer, the statement map and the
  simulator data of `convertedScheme`;
  `convertedV_zkFacts`: the facts of the zero-knowledge route at `convertedV` (the statement map is
  injective, `convertedMsg_injective`, and no statement of the empty ring is honest, `ringOk` needs
  `64` keys); `convertedArgument`: the zero-knowledge route's argument (simulator, extractor, test of
  the empty ring and fallback forgery) at `convertedV`.
- `convertedScheme.insiderForgeProb_le` (`mldsaScheme.insiderForgeProb_le`): the forgery
  probability of BKM06 Definition 7 against `convertedScheme`, at every number of attempts, is at
  most the success of the zero-knowledge route's multi-user forger `zkRouteForger`, plus the
  zero-knowledge, simulation-extraction and knowledge errors, `2Q · 0` and `Q · n · mldsaRefuseAvg`
  (the worst-message refusal term, left symbolic), at the canonical preimage table
  `convertedPreimages` and the default fallback forgery; `convertedScheme.insiderForgeProb_le_of`
  for every table and fallback forgery.
-/

namespace GordieHowe.MLDSA44.Ring.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
  GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring GordieHowe.RingSignature
open Generated.MLDSA44.Ring.Native.QROMParams.Program (program)
open Generated.MLDSA44.Ring.Native.QROMParams (interp ProofSystems)
open scoped NNReal ENNReal

attribute [local instance] _root_.MLDSA.Concrete.concreteNTTRingOps

variable (C : ProofSystems)

/-! ## The ring-binding scheme -/

/-- **The base signer of `bindingScheme`**: `baseSigner` at the ring-binding base message
`bindingMsg`. -/
abbrev bindingBase (maxAttempts : ℕ) :=
  baseSigner (2 + ringMsgLen) C maxAttempts
    (bindingMsg (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
      (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))

/-- **The statement map of `bindingScheme`** (`ringStmtVerifies` at `bindingMsg`). -/
noncomputable abbrev bindingV (maxAttempts : ℕ) :=
  ringStmtVerifies (2 + ringMsgLen) C maxAttempts
    (bindingMsg (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
      (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))

/-- **The proof system of `bindingScheme`**: the compiled program read at the ring statements of
the ring-binding base signer. -/
noncomputable abbrev bindingPS (maxAttempts : ℕ) :=
  (bindingV C maxAttempts).proofSystem (ringHonest (2 + ringMsgLen) C)
    (ringMergeBounds C bindingLen_le) (ringProofFormat C bindingLen_le)

/-- **The number of multi-user requests of the reduction** for `bindingScheme`: `ringStdRequests`
at the read verifier (`ringQ'` with relays of length `1 + qPub + PS.q`), for `Q` requests and the
schedule bound `S`, `w`, `P`. -/
noncomputable abbrev bindingQ' (maxAttempts Q S w P : ℕ) : ℕ :=
  ringStdRequests (bindingBase C maxAttempts) (bindingPS C maxAttempts)
    (StmtVerifiesRing.verifier (ringMergeBounds C bindingLen_le) (pB := max 4069 273) (bindingV C maxAttempts))
    Q S w P

/-- **The default multi-user forgery of `bindingBase`**, an explicit computable value: the public key
`(ρ, t₁) = (0, 0)`, the all-zero base message and the default signature (`MLDSA44.Ring.sigEquiv` of
the concrete signature's default); the fallback forgery of the binding-route headlines. -/
instance bindingBase_inhabited (maxAttempts : ℕ) : Inhabited (bindingBase C maxAttempts).MUForgery :=
  ⟨(⟨Vector.replicate _ 0, Vector.replicate _ (show fipsPrims.Power2High from (0 : _root_.MLDSA.Rq))⟩,
    default, (MLDSA44.Ring.sigEquiv _ _).symm default)⟩

/-- **The binding route's extractor of `bindingScheme`** (`StmtVerifiesRing.ringExtractor` at
`bindingV`): the compiled proof system's extractor list with the knowledge bound of the soundness
data `ringIopSound`, the default claim `c₀` and the fallback forgery `f₀`. -/
noncomputable def bindingExtractor (maxAttempts : ℕ)
    (c₀ : RingSignature.RingStmt (bindingBase C maxAttempts) ×
      Claim (RStmt (2 + ringMsgLen))
        (bindingSetting C).model.NIProof)
    (f₀ : (bindingBase C maxAttempts).MUForgery) :=
  (bindingV C maxAttempts).ringExtractor (ringHonest (2 + ringMsgLen) C) (ringMergeBounds C bindingLen_le)
    (ringProofFormat C bindingLen_le) (ringIopSound _ C) c₀ f₀

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring-binding
ML-DSA-44 ring signature from MU-EUF-CMA^corr** (`mldsaScheme.insiderForgeProb_le_muEufProbWithin`
at `bindsRing_bindingMsg` and `ringIopSound`): at every number of attempts, for an adversary with
the schedule bound `S`, `w`, `P` (`hS`), the forgery probability is at most the success
probability of the multi-user forger with `max n 2` users, `bindingQ'` requests and at most `Q`
signing and corruption requests, plus spBCS's knowledge error at `t + Q · (qPub + PS.q) + kq`
queries and the largest round error. The headline form is
`bindingScheme.insiderForgeProb_le`. -/
theorem bindingScheme.insiderForgeProb_le_muEufProbWithin (maxAttempts : ℕ) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase C maxAttempts) ×
      Claim (RStmt (2 + ringMsgLen))
        (bindingSetting C).model.NIProof)
    (f₀ : (bindingBase C maxAttempts).PK × (bindingBase C maxAttempts).BMsg ×
      (bindingBase C maxAttempts).BSig)
    (A : InsiderAdversary (bindingScheme C maxAttempts) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      Signature.muEufProbWithin (ringMUForger (bindingBase C maxAttempts) (bindingPS C maxAttempts)
          (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
            (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat C bindingLen_le) _
            (bindingV C maxAttempts).stmt (bindingV C maxAttempts).check
            (bindingV C maxAttempts).input) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds C bindingLen_le) (bindingV C maxAttempts))
          f₀ (embedAdversary (le_max_left n 2) A)
          (insiderFam (bindingBase C maxAttempts) (bindingPS C maxAttempts)
            (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
              (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)) (max n 2)) 1 Q
          (bindingQ' C maxAttempts Q S w P)) (bindingQ' C maxAttempts Q S w P) Q +
        SPBCS.knowledgeError (ringTranscript (2 + ringMsgLen) C).k
          (Configurations.fsExtraBytes + (ringTranscript (2 + ringMsgLen) C).maxGrant)
          (kqOf (ringIop (2 + ringMsgLen) C).merges (ringIop (2 + ringMsgLen) C).rounds
            (max 4069 273) (max 4069 273))
          (t + Q * ((bindingBase C maxAttempts).qPub + (bindingPS C maxAttempts).q) +
            kqOf (ringIop (2 + ringMsgLen) C).merges (ringIop (2 + ringMsgLen) C).rounds
              (max 4069 273) (max 4069 273))
          (bindingSetting C).model.senc.digestsPerInput
          (ringIop (2 + ringMsgLen) C).merges.nJ (maxError (ringIopSound (2 + ringMsgLen) C).error) :=
  mldsaScheme.insiderForgeProb_le_muEufProbWithin _ _ _ _ _ _ _
    (bindsRing_bindingMsg _ _ maxAttempts) (ringIopSound _ C) c₀ f₀ A hS Q

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring-binding ML-DSA-44 ring signature from the standard MU-EUF-CMA^corr
game** (`mldsaScheme.insiderForgeProb_le_of_bindsRing` at `bindsRing_bindingMsg` and `ringIopSound`): at every number of
attempts, for an adversary with the schedule bound `S`, `w`, `P` (`hS`), the forgery probability is
at most the success probability of the binding route's base-scheme forger `insiderStdForger` at
`bindingExtractor` in the base scheme's own game (`SignOracle.std`), with `bindingQ'` requests and
at most `Q` signing and corruption requests, plus spBCS's knowledge error `ksError` at the
configuration's largest round error and `ringSignQueries` (`t + Q · (qPub + PS.q)`) queries.
This holds for every fallback forgery `f₀`; the headline
`bindingScheme.insiderForgeProb_le` is its instance at `default`. -/
theorem bindingScheme.insiderForgeProb_le_of (maxAttempts : ℕ) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase proofSystem maxAttempts) ×
      Claim (RStmt (2 + ringMsgLen)) (bindingSetting proofSystem).model.NIProof)
    (f₀ : (bindingBase proofSystem maxAttempts).MUForgery)
    (A : InsiderAdversary (bindingScheme proofSystem maxAttempts) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      Signature.muEufProbWithin (insiderStdForger (bindingExtractor proofSystem maxAttempts c₀ f₀) A Q S w P)
          (bindingQ' proofSystem maxAttempts Q S w P) Q +
        (bindingSetting proofSystem).model.ksError (max 4069 273) (max 4069 273)
          (ringIopSound (2 + ringMsgLen) proofSystem).error
          (ringSignQueries (bindingBase proofSystem maxAttempts) (bindingPS proofSystem maxAttempts) t Q) :=
  mldsaScheme.insiderForgeProb_le_of_bindsRing _ _ _ _ _ _ _
    (bindsRing_bindingMsg _ _ maxAttempts) (ringIopSound _ proofSystem) c₀ f₀ A hS Q

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring-binding ML-DSA-44 ring signature from the standard MU-EUF-CMA^corr
game** (`mldsaScheme.insiderForgeProb_le_of_bindsRing` at `bindsRing_bindingMsg` and `ringIopSound`): at every number of
attempts, for an adversary with the schedule bound `S`, `w`, `P` (`hS`), the forgery probability is
at most the success probability of the binding route's base-scheme forger `insiderStdForger` at
`bindingExtractor` in the base scheme's own game (`SignOracle.std`), with `bindingQ'` requests and
at most `Q` signing and corruption requests, plus spBCS's knowledge error `ksError` at the
configuration's largest round error and `ringSignQueries` (`t + Q · (qPub + PS.q)`) queries.
At the default fallback forgery (`bindingScheme.insiderForgeProb_le_of`: every fallback
forgery). -/
@[headline]
theorem bindingScheme.insiderForgeProb_le (maxAttempts : ℕ) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase proofSystem maxAttempts) ×
      Claim (RStmt (2 + ringMsgLen)) (bindingSetting proofSystem).model.NIProof)
    (A : InsiderAdversary (bindingScheme proofSystem maxAttempts) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      Signature.muEufProbWithin (insiderStdForger (bindingExtractor proofSystem maxAttempts c₀ default) A Q S w P)
          (bindingQ' proofSystem maxAttempts Q S w P) Q +
        (bindingSetting proofSystem).model.ksError (max 4069 273) (max 4069 273)
          (ringIopSound (2 + ringMsgLen) proofSystem).error
          (ringSignQueries (bindingBase proofSystem maxAttempts) (bindingPS proofSystem maxAttempts) t Q) :=
  bindingScheme.insiderForgeProb_le_of maxAttempts c₀ default A hS Q

/-- **Joint-security unforgeability of the ring-binding ML-DSA-44 ring signature from
MU-EUF-CMA^corr** (`mldsaScheme.jointForgeProb_le_muEufProbWithin` at `bindsRing_bindingMsg`):
the bound of `bindingScheme.insiderForgeProb_le_muEufProbWithin` for the joint-security game, the
multi-user forger with the ring-aware and the ordinary signing oracle. The headline form is `bindingScheme.jointForgeProb_le`. -/
theorem bindingScheme.jointForgeProb_le_muEufProbWithin (maxAttempts : ℕ) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase C maxAttempts) ×
      Claim (RStmt (2 + ringMsgLen))
        (bindingSetting C).model.NIProof)
    (f₀ : (bindingBase C maxAttempts).PK × (bindingBase C maxAttempts).BMsg ×
      (bindingBase C maxAttempts).BSig)
    (A : JointAdversary (bindingBase C maxAttempts) (bindingPS C maxAttempts)
      (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
        (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    jointForgeProb A Q ≤
      Signature.muEufProbWithin (ringMUForger (bindingBase C maxAttempts) (bindingPS C maxAttempts)
          (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
            (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat C bindingLen_le) _
            (bindingV C maxAttempts).stmt (bindingV C maxAttempts).check
            (bindingV C maxAttempts).input) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds C bindingLen_le) (bindingV C maxAttempts))
          f₀ (embedAdversary (le_max_left n 2) A)
          (jointFam (bindingBase C maxAttempts) (bindingPS C maxAttempts)
            (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
              (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)) (max n 2)) 1 Q
          (bindingQ' C maxAttempts Q S w P)) (bindingQ' C maxAttempts Q S w P) Q +
        SPBCS.knowledgeError (ringTranscript (2 + ringMsgLen) C).k
          (Configurations.fsExtraBytes + (ringTranscript (2 + ringMsgLen) C).maxGrant)
          (kqOf (ringIop (2 + ringMsgLen) C).merges (ringIop (2 + ringMsgLen) C).rounds
            (max 4069 273) (max 4069 273))
          (t + Q * ((bindingBase C maxAttempts).qPub + (bindingPS C maxAttempts).q) +
            kqOf (ringIop (2 + ringMsgLen) C).merges (ringIop (2 + ringMsgLen) C).rounds
              (max 4069 273) (max 4069 273))
          (bindingSetting C).model.senc.digestsPerInput
          (ringIop (2 + ringMsgLen) C).merges.nJ (maxError (ringIopSound (2 + ringMsgLen) C).error) :=
  mldsaScheme.jointForgeProb_le_muEufProbWithin _ _ _ _ _ _ _
    (bindsRing_bindingMsg _ _ maxAttempts) (ringIopSound _ C) c₀ f₀ A hS Q

/-- **Joint-security unforgeability of the ring-binding ML-DSA-44 ring signature from the standard MU-EUF-CMA^corr
game** (`mldsaScheme.jointForgeProb_le_of_bindsRing` at `bindsRing_bindingMsg` and `ringIopSound`): at every number of
attempts, for an adversary with the schedule bound `S`, `w`, `P` (`hS`), the forgery probability is
at most the success probability of the binding route's base-scheme forger `jointStdForger` at
`bindingExtractor` in the base scheme's own game (`SignOracle.std`), with `bindingQ'` requests and
at most `Q` signing and corruption requests, plus spBCS's knowledge error `ksError` at the
configuration's largest round error and `ringSignQueries` (`t + Q · (qPub + PS.q)`) queries.
This holds for every fallback forgery `f₀`; the headline
`bindingScheme.jointForgeProb_le` is its instance at `default`. -/
theorem bindingScheme.jointForgeProb_le_of (maxAttempts : ℕ) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase proofSystem maxAttempts) ×
      Claim (RStmt (2 + ringMsgLen)) (bindingSetting proofSystem).model.NIProof)
    (f₀ : (bindingBase proofSystem maxAttempts).MUForgery)
    (A : JointAdversary (bindingBase proofSystem maxAttempts) (bindingPS proofSystem maxAttempts)
      (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
        (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    jointForgeProb A Q ≤
      Signature.muEufProbWithin (jointStdForger (bindingExtractor proofSystem maxAttempts c₀ f₀) A Q S w P)
          (bindingQ' proofSystem maxAttempts Q S w P) Q +
        (bindingSetting proofSystem).model.ksError (max 4069 273) (max 4069 273)
          (ringIopSound (2 + ringMsgLen) proofSystem).error
          (ringSignQueries (bindingBase proofSystem maxAttempts) (bindingPS proofSystem maxAttempts) t Q) :=
  mldsaScheme.jointForgeProb_le_of_bindsRing _ _ _ _ _ _ _
    (bindsRing_bindingMsg _ _ maxAttempts) (ringIopSound _ proofSystem) c₀ f₀ A hS Q

/-- **Joint-security unforgeability of the ring-binding ML-DSA-44 ring signature from the standard MU-EUF-CMA^corr
game** (`mldsaScheme.jointForgeProb_le_of_bindsRing` at `bindsRing_bindingMsg` and `ringIopSound`): at every number of
attempts, for an adversary with the schedule bound `S`, `w`, `P` (`hS`), the forgery probability is
at most the success probability of the binding route's base-scheme forger `jointStdForger` at
`bindingExtractor` in the base scheme's own game (`SignOracle.std`), with `bindingQ'` requests and
at most `Q` signing and corruption requests, plus spBCS's knowledge error `ksError` at the
configuration's largest round error and `ringSignQueries` (`t + Q · (qPub + PS.q)`) queries.
At the default fallback forgery (`bindingScheme.jointForgeProb_le_of`: every fallback
forgery). -/
@[headline]
theorem bindingScheme.jointForgeProb_le (maxAttempts : ℕ) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase proofSystem maxAttempts) ×
      Claim (RStmt (2 + ringMsgLen)) (bindingSetting proofSystem).model.NIProof)
    (A : JointAdversary (bindingBase proofSystem maxAttempts) (bindingPS proofSystem maxAttempts)
      (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
        (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    jointForgeProb A Q ≤
      Signature.muEufProbWithin (jointStdForger (bindingExtractor proofSystem maxAttempts c₀ default) A Q S w P)
          (bindingQ' proofSystem maxAttempts Q S w P) Q +
        (bindingSetting proofSystem).model.ksError (max 4069 273) (max 4069 273)
          (ringIopSound (2 + ringMsgLen) proofSystem).error
          (ringSignQueries (bindingBase proofSystem maxAttempts) (bindingPS proofSystem maxAttempts) t Q) :=
  bindingScheme.jointForgeProb_le_of maxAttempts c₀ default A hS Q

/-! ## The converted scheme -/

/-- **The base signer of `convertedScheme`**: `baseSigner` at the converted base message
`convertedMsg`. -/
abbrev convertedBase (maxAttempts : ℕ) :=
  baseSigner (2 + 32) C maxAttempts
    (convertedMsg (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
      (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))

/-- The ring messages of `convertedBase` (`32` bytes) are inhabited. -/
instance (maxAttempts : ℕ) : Nonempty (convertedBase C maxAttempts).Msg :=
  ⟨(default : _root_.MLDSA.Bytes 32)⟩

/-- The signatures of `convertedBase` are inhabited (`nonempty_bsig`). -/
instance (maxAttempts : ℕ) : Nonempty (convertedBase C maxAttempts).BSig :=
  nonempty_bsig _ _ _ _

/-- **The statement map of `convertedScheme`** (`ringStmtVerifies` at `convertedMsg`). -/
noncomputable abbrev convertedV (maxAttempts : ℕ) :=
  ringStmtVerifies (2 + 32) C maxAttempts
    (convertedMsg (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
      (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))

/-- **The statements of the empty ring are tested by the emptiness of the statement's ring** at
`convertedV` (`MLDSA44.Ring.ringVerifies_emptyRingTest`). -/
def convertedV_emptyRingTest (maxAttempts : ℕ) :
    RingSignature.EmptyRingTest (convertedV C maxAttempts).stmt :=
  MLDSA44.Ring.ringVerifies_emptyRingTest _ _ _ _ _

/-- **The facts of the zero-knowledge route at `convertedV`**: the test of the statements of the
empty ring (`convertedV_emptyRingTest`), the injectivity of the statement map
(`MLDSA44.Ring.ringVerifies_stmt_injective`) and no honest statement of the empty ring
(`MLDSA44.Ring.not_mem_of_nil`). -/
def convertedV_zkFacts (maxAttempts : ℕ) : (convertedV C maxAttempts).ZKFacts :=
  ⟨convertedV_emptyRingTest C maxAttempts,
    ringVerifies_stmt_injective _ _ _ _ _ (convertedMsg_injective _ _),
    not_mem_of_nil _ _ _ _ _ fun _ _ h => h.1⟩

/-- **The simulator data of the converted scheme's IOP**
(`RealizedProgram.ProofSystem.fieldIopWithSimData`): the computable simulator data whose simulator
the runtime smoke test compiles and runs (`scripts/test_runtime_smoke.py`). -/
abbrev convertedSim :=
  C.fieldIopWithSimData (ringLowering C)
    (Native.stmtOf (program := program) (I := interp) (len := 2 + 32)) ringOk

/-- **The default multi-user forgery of `convertedBase`**, an explicit computable value: the public key
`(ρ, t₁) = (0, 0)`, the all-zero base message and the default signature (`MLDSA44.Ring.sigEquiv` of
the concrete signature's default); the fallback forgery of the converted forgery headlines. -/
instance convertedBase_inhabited (maxAttempts : ℕ) : Inhabited (convertedBase C maxAttempts).MUForgery :=
  ⟨(⟨Vector.replicate _ 0, Vector.replicate _ (show fipsPrims.Power2High from (0 : _root_.MLDSA.Rq))⟩,
    default, (MLDSA44.Ring.sigEquiv _ _).symm default)⟩

/-- **The zero-knowledge route's argument of `convertedScheme`** (`StmtVerifiesRing.ringArgument` at
`convertedV`): the IOP's simulator with the setting's view encoder and the preimages `T`, zero
knowledge from the honest prover without completeness error (`ringHonest_errorBound`), the IOP's
round-by-round extractor (`ringIopSound`), the facts `convertedV_zkFacts` and the fallback forgery
`f₀`. -/
noncomputable def convertedArgument (maxAttempts : ℕ)
    (T : (convertedSetting C).model.Preimages)
    (f₀ : (convertedBase C maxAttempts).MUForgery) :=
  (convertedV C maxAttempts).ringArgument (ringHonest (2 + 32) C) (ringMergeBounds C msgLen_le)
    (ringHonest_errorBound _ C) (ringIopSound _ C) (convertedV_zkFacts C maxAttempts) T f₀

/-- **The non-interactive proofs of `convertedSetting` are inhabited**
(`SPBCS.ProofSystemTranscript.nonempty_niProof`): the simulator data `convertedSim` at the ring
statement `default` (`MLDSA44.Ring.RStmt.instInhabited`). -/
instance convertedNIProof_nonempty : Nonempty (convertedNIProof C) :=
  (ringTranscript (2 + 32) C).nonempty_niProof (convertedSim C) _ _

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the converted
ML-DSA-44 ring signature from zero knowledge, simulation extraction and MU-EUF-CMA^corr**
(`mldsaScheme.insiderForgeProb_le` at `convertedArgument`; no ring-binding base message needed): at
every number of attempts, for `convertedScheme` and an adversary with the schedule bound `S`, `w`,
`P'` (`hS`), the forgery probability is at most the success of the zero-knowledge route's
multi-user forger `zkRouteForger` (no refusals predicted, public value `()`) with `zkRouteRequests`
requests, plus the zero-knowledge error `ringZkError` at completeness error `0`, the
simulation-extraction error `ringSimExtError`, spBCS's knowledge error `ksError` at
`t + Q · q` queries, `2Q · 0` (the base signer's correctness error, `baseSigner_correctWithin`)
and `Q · n · mldsaRefuseAvg` (the worst-message refusal term averaged over the keys, left
symbolic).
This holds for every preimage table `T` and fallback forgery `f₀`; the headline
`convertedScheme.insiderForgeProb_le` is its instance at `convertedPreimages` and `default`. -/
theorem convertedScheme.insiderForgeProb_le_of (maxAttempts : ℕ)
    (T : (convertedSetting proofSystem).model.Preimages)
    {n t : ℕ} (A : InsiderAdversary (convertedScheme proofSystem maxAttempts) n (OracleView.queriesOnly _ _) t)
    [NeZero n]
    (Q : ℕ)
    (f₀ : (convertedBase proofSystem maxAttempts).MUForgery)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    insiderForgeProb A Q ≤
      Signature.muEufProb
          (Insider.zkRouteForger A (convertedV proofSystem maxAttempts).wit
            (convertedArgument proofSystem maxAttempts T f₀) (convertedBase proofSystem maxAttempts).noRefusal
            unitPub Q)
          (Insider.zkRouteRequests A (convertedArgument proofSystem maxAttempts T f₀) Q S w P') +
        Insider.ringZkError (convertedSetting proofSystem).model
          0 t Q +
        Insider.ringSimExtError A (convertedArgument proofSystem maxAttempts T f₀) Q +
        (convertedSetting proofSystem).model.ksError
          (max 4069 273) (max 4069 273) (ringIopSound (2 + 32) proofSystem).error (t + Q * (convertedScheme proofSystem maxAttempts).q) +
        2 * Q * 0 + Q * (n * mldsaRefuseAvg _root_.MLDSA.mldsa44 fipsPrims maxAttempts) :=
  mldsaScheme.insiderForgeProb_le _ _ _ _ _ _ _ (hk := ⟨Nat.succ_ne_zero 47⟩)
    (ringHonest_errorBound _ proofSystem) (ringIopSound _ proofSystem)
    (baseSigner_correctWithin _ proofSystem _ _) (convertedV_zkFacts proofSystem maxAttempts) T A Q f₀ hS

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the converted
ML-DSA-44 ring signature from zero knowledge, simulation extraction and MU-EUF-CMA^corr**
(`mldsaScheme.insiderForgeProb_le` at `convertedArgument`; no ring-binding base message needed): at
every number of attempts, for `convertedScheme` and an adversary with the schedule bound `S`, `w`,
`P'` (`hS`), the forgery probability is at most the success of the zero-knowledge route's
multi-user forger `zkRouteForger` (no refusals predicted, public value `()`) with `zkRouteRequests`
requests, plus the zero-knowledge error `ringZkError` at completeness error `0`, the
simulation-extraction error `ringSimExtError`, spBCS's knowledge error `ksError` at
`t + Q · q` queries, `2Q · 0` (the base signer's correctness error, `baseSigner_correctWithin`)
and `Q · n · mldsaRefuseAvg` (the worst-message refusal term averaged over the keys, left
symbolic).
At the canonical preimage table `convertedPreimages` and the default fallback forgery
(`convertedScheme.insiderForgeProb_le_of`: every table and fallback forgery). -/
@[headline]
theorem convertedScheme.insiderForgeProb_le (maxAttempts : ℕ)
    {n t : ℕ} (A : InsiderAdversary (convertedScheme proofSystem maxAttempts) n (OracleView.queriesOnly _ _) t)
    [NeZero n]
    (Q : ℕ)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    insiderForgeProb A Q ≤
      Signature.muEufProb
          (Insider.zkRouteForger A (convertedV proofSystem maxAttempts).wit
            (convertedArgument proofSystem maxAttempts (convertedPreimages proofSystem) default) (convertedBase proofSystem maxAttempts).noRefusal
            unitPub Q)
          (Insider.zkRouteRequests A (convertedArgument proofSystem maxAttempts (convertedPreimages proofSystem) default) Q S w P') +
        Insider.ringZkError (convertedSetting proofSystem).model
          0 t Q +
        Insider.ringSimExtError A (convertedArgument proofSystem maxAttempts (convertedPreimages proofSystem) default) Q +
        (convertedSetting proofSystem).model.ksError
          (max 4069 273) (max 4069 273) (ringIopSound (2 + 32) proofSystem).error (t + Q * (convertedScheme proofSystem maxAttempts).q) +
        2 * Q * 0 + Q * (n * mldsaRefuseAvg _root_.MLDSA.mldsa44 fipsPrims maxAttempts) :=
  convertedScheme.insiderForgeProb_le_of maxAttempts _ A Q default hS

end GordieHowe.MLDSA44.Ring.Native.QROMParams
