-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Carrier.QROMParams.RingScheme
public import GordieHowe.Applications.Ring.BaseSignerFacts
public import GordieHowe.Applications.Ring.RingForgerSPBCS
public import GordieHowe.Applications.Ring.RingForgerZKStmt
public import GordieHowe.Applications.Ring.RingSignsStdFacts

@[expose] public section

/-!
# The ring-binding Falcon-512 ring signature from MU-EUF-CMA^corr

The bounds of `GordieHowe/Applications/Ring/RingForgerSPBCS.lean`
(`Ring.StmtVerifiesRing.insiderForgeProb_le_muEufProb`, `…keyReuseForgeProb_le_muEufProb`) for
`bindingScheme` of `GordieHowe/Applications/Falcon512/Ring/Carrier/QROMParams/RingScheme.lean`: the
Falcon-512 base signer is oracle-free (`Ring.falconBaseSigner_oracleFree`) and its base message
binds the ring (`bindsRing_encodeRingMsg`), so the forgery probability of BKM06 Definition 7 and of
the key-reuse game is at most the success probability in MU-EUF-CMA^corr of the explicit
multi-user forger `ringMUForger`, plus spBCS's knowledge error at the configuration's largest round
error.

- `bindingPS`, `bindingQ'`: the proof system of `bindingScheme` and the number of multi-user
  requests.
- `bindingScheme.insiderForgeProb_le_muEufProb`, `bindingScheme.keyReuseForgeProb_le_muEufProb`.
- `bindingScheme.insiderForgeProb_le_muEufProbWithin`,
  `bindingScheme.keyReuseForgeProb_le_muEufProbWithin`: the same bounds with the multi-user forger
  winning with at most `Q` signing and corruption requests (`Signature.muEufProbWithin`).
- `bindingScheme.insiderForgeProb_le`,
  `bindingScheme.keyReuseForgeProb_le`: the same bounds from the standard
  multi-user game (`SignOracle.std`), the Falcon-512 base signer signing a ring as the ordinary
  signer on the base message (`falconBaseSigner_ringSignsStd`).
-/

namespace GordieHowe.Falcon512.Ring.Carrier.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
  GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring GordieHowe.RingSignature
open Generated.Falcon512.Ring.Carrier.QROMParams.Program (program)
open Generated.Falcon512.Ring.Carrier.QROMParams (interp ProofSystems)
open _root_.GordieHowe.Falcon512.Ring.Native (Signer CoreWit)
open scoped NNReal ENNReal

variable (C : ProofSystems)

/-- **The proof system of `bindingScheme`**: the configuration's compiled program read at the
ring statements of the ring-binding base signer. -/
noncomputable abbrev bindingPS (G : Signer ringMsgLen) :=
  (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp).proofSystem
    (ringHonest G C) (ringMergeBounds C ringMsgLen_le) (ringProofFormat C ringMsgLen_le)

/-- **The number of multi-user requests of the reduction** for `bindingScheme` (`ringQ'` at the read
verifier and relays of length `1 + qPub + PS.q`), for `Q` requests and the schedule bound `S`, `w`,
`P`. -/
noncomputable abbrev bindingQ' (G : Signer ringMsgLen)
    (Q S w P : ℕ) : ℕ :=
  ringQ' (StmtVerifiesRing.verifier (ringMergeBounds C ringMsgLen_le) (pB := max 3072 201)
      (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)) Q S w P
    (1 + ((baseSigner G C encodeRingMsg).qPub + (bindingPS C G).q))

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring-binding
Falcon-512 ring signature from MU-EUF-CMA^corr**
(`Ring.StmtVerifiesRing.insiderForgeProb_le_muEufProb` at `bindsRing_encodeRingMsg` and
`Ring.falconBaseSigner_oracleFree`): for an adversary with the schedule bound `S`, `w`, `P`
(`hS`), the forgery probability is at most the success probability of the multi-user forger with
`max n 2` users and `bindingQ'` requests, plus spBCS's knowledge error at
`t + Q · (qPub + PS.q) + kq` queries. -/
theorem bindingScheme.insiderForgeProb_le_muEufProb (G : Signer ringMsgLen) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (baseSigner G C encodeRingMsg) ×
      Claim (Ring.RStmt G)
        ((ringTranscript G C).setting 48 (ringMergeBounds C ringMsgLen_le)).model.NIProof)
    (f₀ : (baseSigner G C encodeRingMsg).PK × (baseSigner G C encodeRingMsg).BMsg ×
      (baseSigner G C encodeRingMsg).BSig)
    (A : InsiderAdversary (bindingScheme C G) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      Signature.muEufProb (ringMUForger (baseSigner G C encodeRingMsg) (bindingPS C G)
          Falcon512.Ring.adm64
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat C ringMsgLen_le) _ _ _ _) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds C ringMsgLen_le)
            (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)) f₀
          (embedAdversary (le_max_left n 2) A)
          (insiderFam (baseSigner G C encodeRingMsg) (bindingPS C G) Falcon512.Ring.adm64
            (max n 2)) 1 Q (bindingQ' C G Q S w P)) (bindingQ' C G Q S w P) +
        SPBCS.knowledgeError (ringTranscript G C).k
          (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant)
          (kqOf (ringIop G C).merges (ringIop G C).rounds (max 3072 201) (max 3072 201))
          (t + Q * ((baseSigner G C encodeRingMsg).qPub + (bindingPS C G).q) +
            kqOf (ringIop G C).merges (ringIop G C).rounds (max 3072 201) (max 3072 201))
          ((ringTranscript G C).setting 48
            (ringMergeBounds C ringMsgLen_le)).model.senc.digestsPerInput
          (ringIop G C).merges.nJ (maxError (ringIopSound G C).error) :=
  Ring.StmtVerifiesRing.insiderForgeProb_le_muEufProb (ringHonest G C)
    (ringMergeBounds C ringMsgLen_le) (ringProofFormat C ringMsgLen_le)
    (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)
    (bindsRing_encodeRingMsg G) (Ring.falconBaseSigner_oracleFree G encodeRingMsg)
    (ringIopSound G C) c₀ f₀ A hS Q

/-- **The bound of `bindingScheme.insiderForgeProb_le_muEufProb` with at most `Q` signing and
corruption requests**:
the multi-user forger wins with at most `Q` signing and corruption requests
(`Signature.muEufProbWithin`), `Q` the requests of the adversary of the ring game. The forger
asks at most `Q` signing and corruption requests on every branch
(`muLaw_ringMUForger_signCorruptCount`), and on the bridge each of them is a logged request of
the relayed forger (`mem_requests_of_bridgeLogs`). -/
theorem bindingScheme.insiderForgeProb_le_muEufProbWithin (G : Signer ringMsgLen) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (baseSigner G C encodeRingMsg) ×
      Claim (Ring.RStmt G)
        ((ringTranscript G C).setting 48 (ringMergeBounds C ringMsgLen_le)).model.NIProof)
    (f₀ : (baseSigner G C encodeRingMsg).PK × (baseSigner G C encodeRingMsg).BMsg ×
      (baseSigner G C encodeRingMsg).BSig)
    (A : InsiderAdversary (bindingScheme C G) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      Signature.muEufProbWithin (ringMUForger (baseSigner G C encodeRingMsg) (bindingPS C G)
          Falcon512.Ring.adm64
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat C ringMsgLen_le) _ _ _ _) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds C ringMsgLen_le)
            (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)) f₀
          (embedAdversary (le_max_left n 2) A)
          (insiderFam (baseSigner G C encodeRingMsg) (bindingPS C G) Falcon512.Ring.adm64
            (max n 2)) 1 Q (bindingQ' C G Q S w P)) (bindingQ' C G Q S w P) Q +
        SPBCS.knowledgeError (ringTranscript G C).k
          (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant)
          (kqOf (ringIop G C).merges (ringIop G C).rounds (max 3072 201) (max 3072 201))
          (t + Q * ((baseSigner G C encodeRingMsg).qPub + (bindingPS C G).q) +
            kqOf (ringIop G C).merges (ringIop G C).rounds (max 3072 201) (max 3072 201))
          ((ringTranscript G C).setting 48
            (ringMergeBounds C ringMsgLen_le)).model.senc.digestsPerInput
          (ringIop G C).merges.nJ (maxError (ringIopSound G C).error) :=
  Ring.StmtVerifiesRing.insiderForgeProb_le_muEufProbWithin (ringHonest G C)
    (ringMergeBounds C ringMsgLen_le) (ringProofFormat C ringMsgLen_le)
    (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)
    (bindsRing_encodeRingMsg G) (Ring.falconBaseSigner_oracleFree G encodeRingMsg)
    (ringIopSound G C) c₀ f₀ A hS Q

/-- **Key-reuse unforgeability of the ring-binding Falcon-512 ring signature from MU-EUF-CMA^corr
with the ring-aware and the ordinary signing oracle**
(`Ring.StmtVerifiesRing.keyReuseForgeProb_le_muEufProb`): the bound of
`bindingScheme.insiderForgeProb_le_muEufProb` for the key-reuse game. -/
theorem bindingScheme.keyReuseForgeProb_le_muEufProb (G : Signer ringMsgLen) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (baseSigner G C encodeRingMsg) ×
      Claim (Ring.RStmt G)
        ((ringTranscript G C).setting 48 (ringMergeBounds C ringMsgLen_le)).model.NIProof)
    (f₀ : (baseSigner G C encodeRingMsg).PK × (baseSigner G C encodeRingMsg).BMsg ×
      (baseSigner G C encodeRingMsg).BSig)
    (A : KeyReuseAdversary (baseSigner G C encodeRingMsg) (bindingPS C G) Falcon512.Ring.adm64
      n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      Signature.muEufProb (ringMUForger (baseSigner G C encodeRingMsg) (bindingPS C G)
          Falcon512.Ring.adm64
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat C ringMsgLen_le) _ _ _ _) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds C ringMsgLen_le)
            (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)) f₀
          (embedAdversary (le_max_left n 2) A)
          (keyReuseFam (baseSigner G C encodeRingMsg) (bindingPS C G) Falcon512.Ring.adm64
            (max n 2)) 1 Q (bindingQ' C G Q S w P)) (bindingQ' C G Q S w P) +
        SPBCS.knowledgeError (ringTranscript G C).k
          (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant)
          (kqOf (ringIop G C).merges (ringIop G C).rounds (max 3072 201) (max 3072 201))
          (t + Q * ((baseSigner G C encodeRingMsg).qPub + (bindingPS C G).q) +
            kqOf (ringIop G C).merges (ringIop G C).rounds (max 3072 201) (max 3072 201))
          ((ringTranscript G C).setting 48
            (ringMergeBounds C ringMsgLen_le)).model.senc.digestsPerInput
          (ringIop G C).merges.nJ (maxError (ringIopSound G C).error) :=
  Ring.StmtVerifiesRing.keyReuseForgeProb_le_muEufProb (ringHonest G C)
    (ringMergeBounds C ringMsgLen_le) (ringProofFormat C ringMsgLen_le)
    (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)
    (bindsRing_encodeRingMsg G) (Ring.falconBaseSigner_oracleFree G encodeRingMsg)
    (ringIopSound G C) c₀ f₀ A hS Q

/-- **The bound of `bindingScheme.keyReuseForgeProb_le_muEufProb` with at most `Q` signing and
corruption requests**:
the multi-user forger wins with at most `Q` signing and corruption requests
(`Signature.muEufProbWithin`), `Q` the requests of the adversary of the ring game. The forger
asks at most `Q` signing and corruption requests on every branch
(`muLaw_ringMUForger_signCorruptCount`), and on the bridge each of them is a logged request of
the relayed forger (`mem_requests_of_bridgeLogs`). -/
theorem bindingScheme.keyReuseForgeProb_le_muEufProbWithin (G : Signer ringMsgLen) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (baseSigner G C encodeRingMsg) ×
      Claim (Ring.RStmt G)
        ((ringTranscript G C).setting 48 (ringMergeBounds C ringMsgLen_le)).model.NIProof)
    (f₀ : (baseSigner G C encodeRingMsg).PK × (baseSigner G C encodeRingMsg).BMsg ×
      (baseSigner G C encodeRingMsg).BSig)
    (A : KeyReuseAdversary (baseSigner G C encodeRingMsg) (bindingPS C G) Falcon512.Ring.adm64
      n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      Signature.muEufProbWithin (ringMUForger (baseSigner G C encodeRingMsg) (bindingPS C G)
          Falcon512.Ring.adm64
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat C ringMsgLen_le) _ _ _ _) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds C ringMsgLen_le)
            (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)) f₀
          (embedAdversary (le_max_left n 2) A)
          (keyReuseFam (baseSigner G C encodeRingMsg) (bindingPS C G) Falcon512.Ring.adm64
            (max n 2)) 1 Q (bindingQ' C G Q S w P)) (bindingQ' C G Q S w P) Q +
        SPBCS.knowledgeError (ringTranscript G C).k
          (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant)
          (kqOf (ringIop G C).merges (ringIop G C).rounds (max 3072 201) (max 3072 201))
          (t + Q * ((baseSigner G C encodeRingMsg).qPub + (bindingPS C G).q) +
            kqOf (ringIop G C).merges (ringIop G C).rounds (max 3072 201) (max 3072 201))
          ((ringTranscript G C).setting 48
            (ringMergeBounds C ringMsgLen_le)).model.senc.digestsPerInput
          (ringIop G C).merges.nJ (maxError (ringIopSound G C).error) :=
  Ring.StmtVerifiesRing.keyReuseForgeProb_le_muEufProbWithin (ringHonest G C)
    (ringMergeBounds C ringMsgLen_le) (ringProofFormat C ringMsgLen_le)
    (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)
    (bindsRing_encodeRingMsg G) (Ring.falconBaseSigner_oracleFree G encodeRingMsg)
    (ringIopSound G C) c₀ f₀ A hS Q

/-- **Key-reuse unforgeability of the ring-binding Falcon-512 ring signature from the standard
MU-EUF-CMA^corr game**: `bindingScheme.keyReuseForgeProb_le_muEufProbWithin` with the combined
oracle reduced to the ordinary one (`muEufProbWithin_ringStd_le_std`, the Falcon-512 base signer
signing a ring as the ordinary signer on the base message, `falconBaseSigner_ringSignsStd`), with
the same numbers of requests and of signing and corruption requests. -/
@[headline]
theorem bindingScheme.keyReuseForgeProb_le (G : Signer ringMsgLen) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (baseSigner G proofSystem encodeRingMsg) ×
      Claim (Ring.RStmt G)
        ((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem ringMsgLen_le)).model.NIProof)
    (f₀ : (baseSigner G proofSystem encodeRingMsg).PK × (baseSigner G proofSystem encodeRingMsg).BMsg ×
      (baseSigner G proofSystem encodeRingMsg).BSig)
    (A : KeyReuseAdversary (baseSigner G proofSystem encodeRingMsg) (bindingPS proofSystem G) Falcon512.Ring.adm64
      n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      Signature.muEufProbWithin (Signature.ringStdToStd 0 (ringMUForger (baseSigner G proofSystem
        encodeRingMsg) (bindingPS proofSystem G)
          Falcon512.Ring.adm64
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat proofSystem ringMsgLen_le) _ _ _ _) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds proofSystem ringMsgLen_le)
            (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)) f₀
          (embedAdversary (le_max_left n 2) A)
          (keyReuseFam (baseSigner G proofSystem encodeRingMsg) (bindingPS proofSystem G) Falcon512.Ring.adm64
            (max n 2)) 1 Q (bindingQ' proofSystem G Q S w P))
          (bindingQ' proofSystem G Q S w P))
        (bindingQ' proofSystem G Q S w P) Q +
        SPBCS.knowledgeError (ringTranscript G proofSystem).k
          (Configurations.fsExtraBytes + (ringTranscript G proofSystem).maxGrant)
          (kqOf (ringIop G proofSystem).merges (ringIop G proofSystem).rounds (max 3072 201) (max 3072 201))
          (t + Q * ((baseSigner G proofSystem encodeRingMsg).qPub + (bindingPS proofSystem G).q) +
            kqOf (ringIop G proofSystem).merges (ringIop G proofSystem).rounds (max 3072 201) (max 3072 201))
          ((ringTranscript G proofSystem).setting 48
            (ringMergeBounds proofSystem ringMsgLen_le)).model.senc.digestsPerInput
          (ringIop G proofSystem).merges.nJ (maxError (ringIopSound G proofSystem).error) :=
  (bindingScheme.keyReuseForgeProb_le_muEufProbWithin proofSystem G c₀ f₀ A hS Q).trans
    (add_le_add (Signature.muEufProbWithin_ringStd_le_std
      (Ring.falconBaseSigner_ringSignsStd G encodeRingMsg) 0 _ _ _) le_rfl)

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the
ring-binding Falcon-512 ring signature from the standard
MU-EUF-CMA^corr game**: `bindingScheme.insiderForgeProb_le_muEufProbWithin` with the ring-aware
oracle reduced to the ordinary one (`muEufProbWithin_ring_le_std`, the Falcon-512 base signer
signing a ring as the ordinary signer on the base message, `falconBaseSigner_ringSignsStd`), with
the same numbers of requests and of signing and corruption requests. -/
@[headline]
theorem bindingScheme.insiderForgeProb_le (G : Signer ringMsgLen) {n t : ℕ}
    (c₀ : RingSignature.RingStmt (baseSigner G proofSystem encodeRingMsg) ×
      Claim (Ring.RStmt G)
        ((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem ringMsgLen_le)).model.NIProof)
    (f₀ : (baseSigner G proofSystem encodeRingMsg).PK × (baseSigner G proofSystem encodeRingMsg).BMsg ×
      (baseSigner G proofSystem encodeRingMsg).BSig)
    (A : InsiderAdversary (bindingScheme proofSystem G) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      Signature.muEufProbWithin (Signature.ringToStd 0 (ringMUForger (baseSigner G proofSystem
        encodeRingMsg) (bindingPS proofSystem G)
          Falcon512.Ring.adm64
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat proofSystem ringMsgLen_le) _ _ _ _) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds proofSystem ringMsgLen_le)
            (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)) f₀
          (embedAdversary (le_max_left n 2) A)
          (insiderFam (baseSigner G proofSystem encodeRingMsg) (bindingPS proofSystem G) Falcon512.Ring.adm64
            (max n 2)) 1 Q (bindingQ' proofSystem G Q S w P))
          (bindingQ' proofSystem G Q S w P))
        (bindingQ' proofSystem G Q S w P) Q +
        SPBCS.knowledgeError (ringTranscript G proofSystem).k
          (Configurations.fsExtraBytes + (ringTranscript G proofSystem).maxGrant)
          (kqOf (ringIop G proofSystem).merges (ringIop G proofSystem).rounds (max 3072 201) (max 3072 201))
          (t + Q * ((baseSigner G proofSystem encodeRingMsg).qPub + (bindingPS proofSystem G).q) +
            kqOf (ringIop G proofSystem).merges (ringIop G proofSystem).rounds (max 3072 201) (max 3072 201))
          ((ringTranscript G proofSystem).setting 48
            (ringMergeBounds proofSystem ringMsgLen_le)).model.senc.digestsPerInput
          (ringIop G proofSystem).merges.nJ (maxError (ringIopSound G proofSystem).error) :=
  (bindingScheme.insiderForgeProb_le_muEufProbWithin proofSystem G c₀ f₀ A hS Q).trans
    (add_le_add (Signature.muEufProbWithin_ring_le_std
      (Ring.falconBaseSigner_ringSignsStd G encodeRingMsg) 0 _ _ _) le_rfl)

open Classical in
/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the converted
Falcon-512 ring signature from zero knowledge, simulation extraction and MU-EUF-CMA^corr**
(`Ring.StmtVerifiesRing.insiderForgeProb_le_zk_muEufProb`; no ring-binding base message needed):
the bound of `convertedScheme.insiderForgeProb_le_zkForgerTerm` with the extraction forger's term bounded by
the success probability of the explicit multi-user forger `zkForger` with `zkQ'` requests, for a
signer carrying the salt (`hG`), correctness error `εc` (`hcorr`) and an adversary with the schedule
bound `S`, `w`, `P'` (`hS`). The forger's multi-user requests are `publicKey 0` or corruptions
among the adversary's first `Q` requests (`zk_bridge_requests`). -/
@[headline]
theorem convertedScheme.insiderForgeProb_le {msgLen : ℕ} (G : Signer msgLen)
    (hmsg : msgLen ≤ 2 ^ 19) (hG : G.CarriesSalt) {εc : ℝ≥0∞}
    (hcorr : (baseSigner G proofSystem (RMsg := Fin msgLen → UInt8) fun _ m => m).CorrectWithin εc)
    (T : ((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem hmsg)).model.Preimages) {n t : ℕ}
      [NeZero n]
    [Nonempty (SPBCS.NIProof (k := (ringTranscript G proofSystem).k) (kN := 2 * (ringTranscript G proofSystem).k)
      (kS := 48) (L := 2 ^ 40) (e := Configurations.fsExtraBytes + (ringTranscript G proofSystem).maxGrant)
      ((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem hmsg)).model)]
    (A : InsiderAdversary (convertedScheme G proofSystem hmsg) n (OracleView.queriesOnly _ _) t)
    (Q : ℕ)
    (f₀ : (baseSigner G proofSystem (RMsg := Fin msgLen → UInt8) fun _ m => m).PK ×
      (baseSigner G proofSystem (RMsg := Fin msgLen → UInt8) fun _ m => m).BMsg ×
      (baseSigner G proofSystem (RMsg := Fin msgLen → UInt8) fun _ m => m).BSig)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    insiderForgeProb A Q ≤
      Signature.muEufProb (RingSignature.Insider.zkForger A (wit := (Falcon512.Ring.ringVerifies G
        (fun _ m => m) _ _ program interp).wit)
          (fun _ _ _ _ => False) Prod.fst Q
          (RingSignature.Insider.zkPsim n
            ((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem hmsg)).layout (ringProofFormat proofSystem
              hmsg)
            (RealizedProgram.ProofSystem.IOP.honest (ringHonest G proofSystem))
              (Falcon512.Ring.ringVerifies G (fun _ m => m) _ _ program interp).stmt
            (Falcon512.Ring.ringVerifies G (fun _ m => m) _ _ program interp).check
              (Falcon512.Ring.ringVerifies G (fun _ m => m) _ _ program interp).input
              Falcon512.Ring.adm64 ((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem
              hmsg)).viewEncoder id
            (RealizedProgram.ProofSystem.IOP.simulator
                (proofSystem.fieldIopWithSimData (forkLowering proofSystem) (Ring.stmtOf (G := G))
                  (Ring.ringOk (G := G)))) T)
          (ringIop G proofSystem).extractor (kqOf (ringIop G proofSystem).merges (ringIop G proofSystem).rounds (max 3072 201)
            (max 3072 201)) f₀)
        (RingSignature.Insider.zkQ' n
          ((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem hmsg)).layout (ringProofFormat proofSystem hmsg)
          (RealizedProgram.ProofSystem.IOP.honest (ringHonest G proofSystem)) (Falcon512.Ring.ringVerifies
            G (fun _ m => m) _ _ program interp).stmt
          (Falcon512.Ring.ringVerifies G (fun _ m => m) _ _ program interp).check
            (Falcon512.Ring.ringVerifies G (fun _ m => m) _ _ program interp).input
            Falcon512.Ring.adm64 ((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem
            hmsg)).viewEncoder id
          (RealizedProgram.ProofSystem.IOP.simulator
            (proofSystem.fieldIopWithSimData (forkLowering proofSystem) (Ring.stmtOf (G := G))
              (Ring.ringOk (G := G)))) T Q S w P') +
        ENNReal.ofReal (((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem hmsg)).model.zkError 0
          t Q) +
        ((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem hmsg)).model.simExtractionError
          (kqOf (ringIop G proofSystem).merges (ringIop G proofSystem).rounds (max 3072 201) (max 3072 201))
          (maxError (ringIopSound G proofSystem).error)
          (((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem hmsg)).model.niJointSimulatorProg
            ((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem hmsg)).layout
            ((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem hmsg)).viewEncoder.toViewRead
            (max 3072 201) id
            (RealizedProgram.ProofSystem.IOP.simulator
            (proofSystem.fieldIopWithSimData (forkLowering proofSystem) (Ring.stmtOf (G := G))
              (Ring.ringOk (G := G)))) T).q t Q +
        SPBCS.knowledgeError (ringTranscript G proofSystem).k
          (Configurations.fsExtraBytes + (ringTranscript G proofSystem).maxGrant)
          (kqOf (ringIop G proofSystem).merges (ringIop G proofSystem).rounds (max 3072 201) (max 3072 201))
          (t + Q * (convertedScheme G proofSystem hmsg).q +
            (kqOf (ringIop G proofSystem).merges (ringIop G proofSystem).rounds (max 3072 201) (max 3072 201)))
          ((ringTranscript G proofSystem).setting 48 (ringMergeBounds proofSystem hmsg)).model.senc.digestsPerInput
          (ringIop G proofSystem).merges.nJ (maxError (ringIopSound G proofSystem).error) +
        2 * Q * εc := by
  have h := StmtVerifiesRing.insiderForgeProb_le_zk_muEufProb (ringHonest G proofSystem)
    (ringMergeBounds proofSystem hmsg) (ringProofFormat proofSystem hmsg) _
    (show 0 < (ringTranscript G proofSystem).k from Nat.succ_pos 47)
    (ringHonest_errorBound G proofSystem) (ringIopSound G proofSystem)
    (falconBaseSigner_oracleFree G _) (falconBaseSigner_pubOfCoins G _ hG)
    (falconBaseSigner_refusalOfCoins G _) hcorr
    (Falcon512.Ring.ringVerifies_stmt_injective G _ _ _ program interp fun _ =>
      Function.injective_id)
    (Falcon512.Ring.not_mem_ringHonestRelOf_nil G _ program interp) T A Q f₀ hS
  -- the terms of `h` and of the statement differ in the spelling of the setting's parameters
  convert h using 6 <;> first | with_reducible_and_instances rfl | (congr 1; done) | rfl

end GordieHowe.Falcon512.Ring.Carrier.QROMParams
