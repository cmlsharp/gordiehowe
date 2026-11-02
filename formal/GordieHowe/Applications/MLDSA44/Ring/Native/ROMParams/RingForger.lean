-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.ROMParams.RingScheme

@[expose] public section

/-!
# The ML-DSA-44 ring signatures of `MLDSA44.Ring.Native.ROMParams` from MU-EUF-CMA^corr

The unforgeability headlines of the ring signatures of
`GordieHowe/Applications/MLDSA44/Ring/Native/ROMParams/RingScheme.lean`, each an instance of a
generic theorem of `GordieHowe/Applications/Ring/MLDSARing.lean`.

- `bindingBase`, `bindingV`, `bindingPS`, `bindingQ'`: the base signer, the statement map and the
  proof system of `bindingScheme`, and the number of multi-user requests of the reduction.
- `bindingScheme.insiderForgeProb_le`,
  `bindingScheme.keyReuseForgeProb_le`
  (`mldsaScheme.insiderForgeProb_le_of_bindsRing`,
  `mldsaScheme.keyReuseForgeProb_le_of_bindsRing` at `bindsRing_bindingMsg`): the forgery
  probability of BKM06 Definition 7 and of the key-reuse game against `bindingScheme` is at most
  the success probability of the multi-user forger `ringMUForger`, relayed to the base scheme's
  standard game `SignOracle.std`, with at most `Q` signing and corruption requests, plus spBCS's
  knowledge error at the configuration's largest round error. The ring-oracle forms
  `bindingScheme.insiderForgeProb_le_muEufProbWithin`,
  `bindingScheme.keyReuseForgeProb_le_muEufProbWithin` remain.
- `convertedBase`, `convertedV`, `convertedSim`: the base signer, the statement map and the
  simulator data of `convertedScheme`;
  `convertedScheme.insiderForgeProb_le`
  (`mldsaScheme.insiderForgeProb_le`): the forgery probability of
  BKM06 Definition 7 against `convertedScheme`, at every number of attempts, is at most the success
  of the multi-user forger `zkForger`, plus the zero-knowledge, simulation-extraction and knowledge
  errors, `2Q · 0` and `Q · n · mldsaRefuseAvg` (the worst-message refusal term, left symbolic); the
  statement map is injective (`convertedMsg_injective`) and no statement of the empty ring is honest
  (`ringOk` needs `64` keys).
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
  GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring GordieHowe.RingSignature
open Generated.MLDSA44.Ring.Native.ROMParams.Program (program)
open Generated.MLDSA44.Ring.Native.ROMParams (interp ProofSystems)
open scoped NNReal ENNReal

attribute [local instance] _root_.MLDSA.Concrete.concreteNTTRingOps

/- Generated data: unifying the figures' terms reads the generated program. -/
set_option maxRecDepth 8192

variable (C : ProofSystems)

/-! ## The ring-binding scheme -/

/-- **The base signer of `bindingScheme`**: `baseSigner` at the ring-binding base message
`bindingMsg`. -/
noncomputable abbrev bindingBase (maxAttempts : ℕ) :=
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

/-- **The number of multi-user requests of the reduction** for `bindingScheme` (`ringQ'` at the
read verifier and relays of length `1 + qPub + PS.q`), for `Q` requests and the schedule bound
`S`, `w`, `P`. -/
noncomputable abbrev bindingQ' (maxAttempts Q S w P : ℕ) :
    ℕ :=
  ringQ' (StmtVerifiesRing.verifier (ringMergeBounds C bindingLen_le) (pB := max 3193 137)
      (bindingV C maxAttempts)) Q S w P
    (1 + ((bindingBase C maxAttempts).qPub + (bindingPS C maxAttempts).q))

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
        ((ringTranscript (2 + ringMsgLen) C).setting 32 (ringMergeBounds C bindingLen_le)).model.NIProof)
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
            (max 3193 137) (max 3193 137))
          (t + Q * ((bindingBase C maxAttempts).qPub + (bindingPS C maxAttempts).q) +
            kqOf (ringIop (2 + ringMsgLen) C).merges (ringIop (2 + ringMsgLen) C).rounds
              (max 3193 137) (max 3193 137))
          ((ringTranscript (2 + ringMsgLen) C).setting 32
            (ringMergeBounds C bindingLen_le)).model.senc.digestsPerInput
          (ringIop (2 + ringMsgLen) C).merges.nJ (maxError (ringIopSound (2 + ringMsgLen) C).error) :=
  mldsaScheme.insiderForgeProb_le_muEufProbWithin _ _ _ _ _ _ _
    (bindsRing_bindingMsg _ _ maxAttempts) (ringIopSound _ C) c₀ f₀ A hS Q

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring-binding
ML-DSA-44 ring signature from the standard MU-EUF-CMA^corr game**
(`mldsaScheme.insiderForgeProb_le_of_bindsRing` at `bindsRing_bindingMsg` and
`ringIopSound`): the bound of `bindingScheme.insiderForgeProb_le_muEufProbWithin` with the
multi-user forger relayed to the base scheme's own game (`SignOracle.std`, `Signature.ringToStd`;
the ML-DSA base signer signs a ring as the ordinary signer on the base message,
`mldsaBaseSigner_ringSignsStd`), with the same numbers of requests and of signing and corruption
requests. -/
@[headline]
theorem bindingScheme.insiderForgeProb_le (maxAttempts : ℕ) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase proofSystem maxAttempts) ×
      Claim (RStmt (2 + ringMsgLen))
        ((ringTranscript (2 + ringMsgLen) proofSystem).setting 32 (ringMergeBounds proofSystem bindingLen_le)).model.NIProof)
    (f₀ : (bindingBase proofSystem maxAttempts).PK × (bindingBase proofSystem maxAttempts).BMsg ×
      (bindingBase proofSystem maxAttempts).BSig)
    (A : InsiderAdversary (bindingScheme proofSystem maxAttempts) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      Signature.muEufProbWithin (Signature.ringToStd 0 (ringMUForger (bindingBase proofSystem maxAttempts) (bindingPS proofSystem maxAttempts)
          (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
            (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat proofSystem bindingLen_le) _
            (bindingV proofSystem maxAttempts).stmt (bindingV proofSystem maxAttempts).check
            (bindingV proofSystem maxAttempts).input) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds proofSystem bindingLen_le) (bindingV proofSystem maxAttempts))
          f₀ (embedAdversary (le_max_left n 2) A)
          (insiderFam (bindingBase proofSystem maxAttempts) (bindingPS proofSystem maxAttempts)
            (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
              (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)) (max n 2)) 1 Q
          (bindingQ' proofSystem maxAttempts Q S w P))
          (bindingQ' proofSystem maxAttempts Q S w P))
        (bindingQ' proofSystem maxAttempts Q S w P) Q +
        SPBCS.knowledgeError (ringTranscript (2 + ringMsgLen) proofSystem).k
          (Configurations.fsExtraBytes + (ringTranscript (2 + ringMsgLen) proofSystem).maxGrant)
          (kqOf (ringIop (2 + ringMsgLen) proofSystem).merges (ringIop (2 + ringMsgLen) proofSystem).rounds
            (max 3193 137) (max 3193 137))
          (t + Q * ((bindingBase proofSystem maxAttempts).qPub + (bindingPS proofSystem maxAttempts).q) +
            kqOf (ringIop (2 + ringMsgLen) proofSystem).merges (ringIop (2 + ringMsgLen) proofSystem).rounds
              (max 3193 137) (max 3193 137))
          ((ringTranscript (2 + ringMsgLen) proofSystem).setting 32
            (ringMergeBounds proofSystem bindingLen_le)).model.senc.digestsPerInput
          (ringIop (2 + ringMsgLen) proofSystem).merges.nJ (maxError (ringIopSound (2 + ringMsgLen) proofSystem).error) :=
  mldsaScheme.insiderForgeProb_le_of_bindsRing _ _ _ _ _ _ _
    (bindsRing_bindingMsg _ _ maxAttempts) (ringIopSound _ proofSystem) c₀ f₀ A hS Q

/-- **Key-reuse unforgeability of the ring-binding ML-DSA-44 ring signature from
MU-EUF-CMA^corr** (`mldsaScheme.keyReuseForgeProb_le_muEufProbWithin` at `bindsRing_bindingMsg`):
the bound of `bindingScheme.insiderForgeProb_le_muEufProbWithin` for the key-reuse game, the
multi-user forger with the ring-aware and the ordinary signing oracle. The headline form is `bindingScheme.keyReuseForgeProb_le`. -/
theorem bindingScheme.keyReuseForgeProb_le_muEufProbWithin (maxAttempts : ℕ) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase C maxAttempts) ×
      Claim (RStmt (2 + ringMsgLen))
        ((ringTranscript (2 + ringMsgLen) C).setting 32 (ringMergeBounds C bindingLen_le)).model.NIProof)
    (f₀ : (bindingBase C maxAttempts).PK × (bindingBase C maxAttempts).BMsg ×
      (bindingBase C maxAttempts).BSig)
    (A : KeyReuseAdversary (bindingBase C maxAttempts) (bindingPS C maxAttempts)
      (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
        (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      Signature.muEufProbWithin (ringMUForger (bindingBase C maxAttempts) (bindingPS C maxAttempts)
          (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
            (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat C bindingLen_le) _
            (bindingV C maxAttempts).stmt (bindingV C maxAttempts).check
            (bindingV C maxAttempts).input) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds C bindingLen_le) (bindingV C maxAttempts))
          f₀ (embedAdversary (le_max_left n 2) A)
          (keyReuseFam (bindingBase C maxAttempts) (bindingPS C maxAttempts)
            (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
              (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)) (max n 2)) 1 Q
          (bindingQ' C maxAttempts Q S w P)) (bindingQ' C maxAttempts Q S w P) Q +
        SPBCS.knowledgeError (ringTranscript (2 + ringMsgLen) C).k
          (Configurations.fsExtraBytes + (ringTranscript (2 + ringMsgLen) C).maxGrant)
          (kqOf (ringIop (2 + ringMsgLen) C).merges (ringIop (2 + ringMsgLen) C).rounds
            (max 3193 137) (max 3193 137))
          (t + Q * ((bindingBase C maxAttempts).qPub + (bindingPS C maxAttempts).q) +
            kqOf (ringIop (2 + ringMsgLen) C).merges (ringIop (2 + ringMsgLen) C).rounds
              (max 3193 137) (max 3193 137))
          ((ringTranscript (2 + ringMsgLen) C).setting 32
            (ringMergeBounds C bindingLen_le)).model.senc.digestsPerInput
          (ringIop (2 + ringMsgLen) C).merges.nJ (maxError (ringIopSound (2 + ringMsgLen) C).error) :=
  mldsaScheme.keyReuseForgeProb_le_muEufProbWithin _ _ _ _ _ _ _
    (bindsRing_bindingMsg _ _ maxAttempts) (ringIopSound _ C) c₀ f₀ A hS Q

/-- **Key-reuse unforgeability of the ring-binding
ML-DSA-44 ring signature from the standard MU-EUF-CMA^corr game**
(`mldsaScheme.keyReuseForgeProb_le_of_bindsRing` at `bindsRing_bindingMsg` and
`ringIopSound`): the bound of `bindingScheme.keyReuseForgeProb_le_muEufProbWithin` with the
multi-user forger relayed to the base scheme's own game (`SignOracle.std`, `Signature.ringStdToStd`;
the ML-DSA base signer signs a ring as the ordinary signer on the base message,
`mldsaBaseSigner_ringSignsStd`), with the same numbers of requests and of signing and corruption
requests. -/
@[headline]
theorem bindingScheme.keyReuseForgeProb_le (maxAttempts : ℕ) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase proofSystem maxAttempts) ×
      Claim (RStmt (2 + ringMsgLen))
        ((ringTranscript (2 + ringMsgLen) proofSystem).setting 32 (ringMergeBounds proofSystem bindingLen_le)).model.NIProof)
    (f₀ : (bindingBase proofSystem maxAttempts).PK × (bindingBase proofSystem maxAttempts).BMsg ×
      (bindingBase proofSystem maxAttempts).BSig)
    (A : KeyReuseAdversary (bindingBase proofSystem maxAttempts) (bindingPS proofSystem maxAttempts)
      (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
        (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      Signature.muEufProbWithin (Signature.ringStdToStd 0 (ringMUForger (bindingBase proofSystem maxAttempts) (bindingPS proofSystem maxAttempts)
          (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
            (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat proofSystem bindingLen_le) _
            (bindingV proofSystem maxAttempts).stmt (bindingV proofSystem maxAttempts).check
            (bindingV proofSystem maxAttempts).input) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds proofSystem bindingLen_le) (bindingV proofSystem maxAttempts))
          f₀ (embedAdversary (le_max_left n 2) A)
          (keyReuseFam (bindingBase proofSystem maxAttempts) (bindingPS proofSystem maxAttempts)
            (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
              (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44)) (max n 2)) 1 Q
          (bindingQ' proofSystem maxAttempts Q S w P))
          (bindingQ' proofSystem maxAttempts Q S w P))
        (bindingQ' proofSystem maxAttempts Q S w P) Q +
        SPBCS.knowledgeError (ringTranscript (2 + ringMsgLen) proofSystem).k
          (Configurations.fsExtraBytes + (ringTranscript (2 + ringMsgLen) proofSystem).maxGrant)
          (kqOf (ringIop (2 + ringMsgLen) proofSystem).merges (ringIop (2 + ringMsgLen) proofSystem).rounds
            (max 3193 137) (max 3193 137))
          (t + Q * ((bindingBase proofSystem maxAttempts).qPub + (bindingPS proofSystem maxAttempts).q) +
            kqOf (ringIop (2 + ringMsgLen) proofSystem).merges (ringIop (2 + ringMsgLen) proofSystem).rounds
              (max 3193 137) (max 3193 137))
          ((ringTranscript (2 + ringMsgLen) proofSystem).setting 32
            (ringMergeBounds proofSystem bindingLen_le)).model.senc.digestsPerInput
          (ringIop (2 + ringMsgLen) proofSystem).merges.nJ (maxError (ringIopSound (2 + ringMsgLen) proofSystem).error) :=
  mldsaScheme.keyReuseForgeProb_le_of_bindsRing _ _ _ _ _ _ _
    (bindsRing_bindingMsg _ _ maxAttempts) (ringIopSound _ proofSystem) c₀ f₀ A hS Q

/-! ## The converted scheme -/

/-- **The base signer of `convertedScheme`**: `baseSigner` at the converted base message
`convertedMsg`. -/
noncomputable abbrev convertedBase (maxAttempts : ℕ) :=
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
`convertedV` (`MLDSA44.Ring.ringVerifies_emptyRingTest`; instance search does not unfold the
abbreviations to `ringVerifies`). -/
instance convertedV_emptyRingTest (maxAttempts : ℕ) :
    RingSignature.EmptyRingTest (convertedV C maxAttempts).stmt :=
  MLDSA44.Ring.ringVerifies_emptyRingTest _ _ _ _ _

/-- **The simulator data of the converted scheme's IOP**
(`RealizedProgram.ProofSystem.fieldIopWithSimData`). -/
abbrev convertedSim :=
  C.fieldIopWithSimData (ringLowering C)
    (Native.stmtOf (program := program) (I := interp) (len := 2 + 32)) ringOk

set_option maxRecDepth 100000 in
open Classical in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the converted
ML-DSA-44 ring signature from zero knowledge, simulation extraction and MU-EUF-CMA^corr**
(`mldsaScheme.insiderForgeProb_le`; no ring-binding base message
needed): at every number of attempts, for `convertedScheme` and an adversary with the schedule
bound `S`, `w`, `P'` (`hS`), the forgery probability is at most the success of the multi-user
forger `zkForger` with `zkQ'` requests, plus `zkError 0 t Q`, the simulation-extraction error,
spBCS's knowledge error, `2Q · 0` (the base signer's correctness error, `baseSigner_correctWithin`)
and `Q · n · mldsaRefuseAvg` (the worst-message refusal term averaged over the keys, left
symbolic). The statement map is injective (`ringVerifies_stmt_injective`, `convertedMsg_injective`),
no statement of the empty ring is honest (`not_mem_of_nil`), and the statements of the empty ring
are tested by the emptiness of their ring (`ringVerifies_emptyRingTest`). -/
@[headline]
theorem convertedScheme.insiderForgeProb_le (maxAttempts : ℕ)
    (T : ((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).model.Preimages)
    {n t : ℕ} (A : InsiderAdversary (convertedScheme proofSystem maxAttempts) n (OracleView.queriesOnly _ _) t)
    [NeZero n]
    [Nonempty (SPBCS.NIProof (k := (ringTranscript (2 + 32) proofSystem).k)
      (kN := 2 * (ringTranscript (2 + 32) proofSystem).k) (kS := 32) (L := 2 ^ 40)
      (e := Configurations.fsExtraBytes + (ringTranscript (2 + 32) proofSystem).maxGrant)
      ((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).model)] (Q : ℕ)
    (f₀ : (convertedBase proofSystem maxAttempts).PK × (convertedBase proofSystem maxAttempts).BMsg × (convertedBase proofSystem maxAttempts).BSig)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    insiderForgeProb A Q ≤
      Signature.muEufProb (RingSignature.Insider.zkForger A (wit := (convertedV proofSystem maxAttempts).wit)
          (fun _ _ _ _ => False) (fun _ => ()) Q
          (RingSignature.Insider.zkPsim (ert := convertedV_emptyRingTest proofSystem maxAttempts) n
            ((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).layout
            (ringProofFormat proofSystem msgLen_le)
            (RealizedProgram.ProofSystem.IOP.honest (ringHonest (2 + 32) proofSystem))
            (convertedV proofSystem maxAttempts).stmt (convertedV proofSystem maxAttempts).check (convertedV proofSystem maxAttempts).input
            (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
              (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))
            ((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).viewEncoder id
            (RealizedProgram.ProofSystem.IOP.simulator (convertedSim proofSystem)) T)
          (ringIop (2 + 32) proofSystem).extractor
          (kqOf (ringIop (2 + 32) proofSystem).merges (ringIop (2 + 32) proofSystem).rounds (max 3193 137)
            (max 3193 137)) f₀)
        (RingSignature.Insider.zkQ' (ert := convertedV_emptyRingTest proofSystem maxAttempts) n
          ((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).layout
          (ringProofFormat proofSystem msgLen_le)
          (RealizedProgram.ProofSystem.IOP.honest (ringHonest (2 + 32) proofSystem))
          (convertedV proofSystem maxAttempts).stmt (convertedV proofSystem maxAttempts).check (convertedV proofSystem maxAttempts).input
          (adm (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
            (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44))
          ((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).viewEncoder id
          (RealizedProgram.ProofSystem.IOP.simulator (convertedSim proofSystem)) T Q S w P') +
        ENNReal.ofReal
          (((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).model.zkError 0
            t Q) +
        ((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).model.simExtractionError
          (kqOf (ringIop (2 + 32) proofSystem).merges (ringIop (2 + 32) proofSystem).rounds (max 3193 137)
            (max 3193 137))
          (maxError (ringIopSound (2 + 32) proofSystem).error)
          (((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).model.niJointSimulatorProg
            ((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).layout
            ((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).viewEncoder.toViewRead
            (max 3193 137) id (RealizedProgram.ProofSystem.IOP.simulator (convertedSim proofSystem)) T).q t Q +
        SPBCS.knowledgeError (ringTranscript (2 + 32) proofSystem).k
          (Configurations.fsExtraBytes + (ringTranscript (2 + 32) proofSystem).maxGrant)
          (kqOf (ringIop (2 + 32) proofSystem).merges (ringIop (2 + 32) proofSystem).rounds (max 3193 137)
            (max 3193 137))
          (t + Q * (convertedScheme proofSystem maxAttempts).q +
            kqOf (ringIop (2 + 32) proofSystem).merges (ringIop (2 + 32) proofSystem).rounds (max 3193 137)
              (max 3193 137))
          ((ringTranscript (2 + 32) proofSystem).setting 32 (ringMergeBounds proofSystem msgLen_le)).model.senc.digestsPerInput
          (ringIop (2 + 32) proofSystem).merges.nJ (maxError (ringIopSound (2 + 32) proofSystem).error) +
        2 * Q * 0 + Q * (n * mldsaRefuseAvg _root_.MLDSA.mldsa44 fipsPrims maxAttempts) :=
  mldsaScheme.insiderForgeProb_le _ _ _ _ _ _ _
    (show 0 < (ringTranscript (2 + 32) proofSystem).k from Nat.succ_pos 31) (ringHonest_errorBound _ proofSystem)
    (ringIopSound _ proofSystem) (baseSigner_correctWithin _ proofSystem _ _)
    (ringVerifies_stmt_injective _ _ _ _ _ (convertedMsg_injective _ _))
    (not_mem_of_nil _ _ _ _ _ fun _ _ h => h.1) T A Q f₀ hS

end GordieHowe.MLDSA44.Ring.Native.ROMParams
