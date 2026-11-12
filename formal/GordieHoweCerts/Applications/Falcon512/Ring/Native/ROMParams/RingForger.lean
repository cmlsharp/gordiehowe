-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.Falcon512.Ring.Native.ROMParams.RingScheme
public import GordieHowe.Applications.Ring.BaseSignerFacts
public import GordieHowe.Applications.Ring.RingForgerSPBCS
public import GordieHowe.Applications.Ring.RingForgerZKStmt
public import GordieHowe.Applications.Ring.RingSignsStdFacts

@[expose] public section

/-!
# The ring-binding Falcon-512 ring signature from MU-EUF-CMA^corr

The bounds of `GordieHowe/Applications/Ring/RingForgerSPBCS.lean`
(`Ring.StmtVerifiesRing.insiderForgeProb_le_muEufProb`, `…jointForgeProb_le_muEufProb`) for
`bindingScheme` of `GordieHoweCerts/Applications/Falcon512/Ring/Native/ROMParams/RingScheme.lean`: the
Falcon-512 base signer is oracle-free (`Ring.falconBaseSigner_oracleFree`) and its base message
binds the ring (`bindsRing_encodeRingMsg`), so the forgery probability of BKM06 Definition 7 and of
the joint-security game is at most the success probability in MU-EUF-CMA^corr of the explicit
multi-user forger `ringMUForger`, plus spBCS's knowledge error at the configuration's largest round
error.

- `bindingPS`, `bindingV`, `bindingQ'`, `bindingExtractor`: the proof system and the statement map
  of `bindingScheme`, the number of multi-user requests (`ringStdRequests`) and the binding route's
  extractor (`StmtVerifiesRing.ringExtractor`).
- `bindingScheme.insiderForgeProb_le_muEufProb`, `bindingScheme.jointForgeProb_le_muEufProb`.
- `bindingScheme.insiderForgeProb_le_muEufProbWithin`,
  `bindingScheme.jointForgeProb_le_muEufProbWithin`: the same bounds with the multi-user forger
  winning with at most `Q` signing and corruption requests (`Signature.muEufProbWithin`).
- `bindingScheme.insiderForgeProb_le`,
  `bindingScheme.jointForgeProb_le`: the same bounds from the standard
  multi-user game (`SignOracle.std`), the Falcon-512 base signer signing a ring as the ordinary
  signer on the base message (`falconBaseSigner_ringSignsStd`), stated with the binding route's
  base-scheme forgers `insiderStdForger`, `jointStdForger` at `bindingExtractor` and spBCS's
  knowledge error `ksError`, at the default fallback forgery (the `_of` forms for every fallback
  forgery).
- `convertedV`, `convertedV_zkFacts`, `convertedArgument`: the statement map of `convertedScheme`,
  the facts of the zero-knowledge route at it and the route's argument;
  `convertedScheme.insiderForgeProb_le` (`Ring.StmtVerifiesRing.insiderForgeProb_le_zk_muEufProb`):
  the forgery probability of BKM06 Definition 7 against `convertedScheme` is at most the success of
  the zero-knowledge route's multi-user forger `zkRouteForger`, plus the zero-knowledge,
  simulation-extraction and knowledge errors and `2Q · εc`, at the canonical preimage table
  `convertedPreimages` and the default fallback forgery (`convertedScheme.insiderForgeProb_le_of`
  for every table and fallback forgery).
-/

namespace GordieHowe.Falcon512.Ring.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
  GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring GordieHowe.RingSignature
open Generated.Falcon512.Ring.Native.ROMParams.Program (program)
open Generated.Falcon512.Ring.Native.ROMParams (interp ProofSystems)
open _root_.GordieHowe.Falcon512.Ring.Native (CoreWit)
open scoped NNReal ENNReal

variable (C : ProofSystems)

/-- **The proof system of `bindingScheme`**: the configuration's compiled program read at the
ring statements of the ring-binding base signer. -/
noncomputable abbrev bindingPS (G : Signer ringMsgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins] :=
  (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp).proofSystem
    (ringHonest G C) (ringMergeBounds C ringMsgLen_le) (ringProofFormat C ringMsgLen_le)

/-- **The statement map of `bindingScheme`** (`Falcon512.Ring.ringVerifies` at the ring-binding
base message `encodeRingMsg`, on the configuration's oracle at `32`-byte salts). -/
noncomputable abbrev bindingV (G : Signer ringMsgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins] :=
  Falcon512.Ring.ringVerifies G encodeRingMsg
    (Bits (queryBits (ringTranscript G C).k (2 * (ringTranscript G C).k) 32 (2 ^ 40)))
    (XOut (ringTranscript G C).k (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant))
    program interp

/-- **The number of multi-user requests of the reduction** for `bindingScheme`: `ringStdRequests`
at the read verifier (`ringQ'` with relays of length `1 + qPub + PS.q`), for `Q` requests and the
schedule bound `S`, `w`, `P`. -/
noncomputable abbrev bindingQ' (G : Signer ringMsgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins]
    (Q S w P : ℕ) : ℕ :=
  ringStdRequests (bindingBase C G) (bindingPS C G)
    (StmtVerifiesRing.verifier (ringMergeBounds C ringMsgLen_le) (pB := max 1506 89) (bindingV C G)) Q S w P

/-- **The default multi-user forgery of `bindingBase`**, an explicit computable value: the all-zero public
key (`Falcon512.PublicKey`'s default), the all-zero base message and the signature of zero bytes
(`Falcon512.Sig`'s default); the fallback forgery of the binding-route headlines. -/
instance bindingBase_inhabited (G : Signer ringMsgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins] :
    Inhabited (bindingBase C G).MUForgery :=
  ⟨(default, fun _ => 0, default)⟩

/-- **The binding route's extractor of `bindingScheme`** (`StmtVerifiesRing.ringExtractor` at
`bindingV`): the compiled proof system's extractor list with the knowledge bound of the soundness
data `ringIopSound`, the default claim `c₀` and the fallback forgery `f₀`. -/
noncomputable def bindingExtractor (G : Signer ringMsgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins]
    (c₀ : RingSignature.RingStmt (bindingBase C G) ×
      Claim (Ring.RStmt G)
        (bindingSetting C G).model.NIProof)
    (f₀ : (bindingBase C G).MUForgery) :=
  (bindingV C G).ringExtractor (ringHonest G C) (ringMergeBounds C ringMsgLen_le)
    (ringProofFormat C ringMsgLen_le) (ringIopSound G C) c₀ f₀

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring-binding
Falcon-512 ring signature from MU-EUF-CMA^corr**
(`Ring.StmtVerifiesRing.insiderForgeProb_le_muEufProb` at `bindsRing_encodeRingMsg` and
`Ring.falconBaseSigner_oracleFree`): for an adversary with the schedule bound `S`, `w`, `P`
(`hS`), the forgery probability is at most the success probability of the multi-user forger with
`max n 2` users and `bindingQ'` requests, plus spBCS's knowledge error at
`t + Q · (qPub + PS.q) + kq` queries. -/
theorem bindingScheme.insiderForgeProb_le_muEufProb (G : Signer ringMsgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins] {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase C G) ×
      Claim (Ring.RStmt G)
        (bindingSetting C G).model.NIProof)
    (f₀ : (bindingBase C G).PK × (bindingBase C G).BMsg ×
      (bindingBase C G).BSig)
    (A : InsiderAdversary (bindingScheme C G) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      Signature.muEufProb (ringMUForger (bindingBase C G) (bindingPS C G)
          Falcon512.Ring.adm64
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat C ringMsgLen_le) _ _ _ _) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds C ringMsgLen_le)
            (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)) f₀
          (embedAdversary (le_max_left n 2) A)
          (insiderFam (bindingBase C G) (bindingPS C G) Falcon512.Ring.adm64
            (max n 2)) 1 Q (bindingQ' C G Q S w P)) (bindingQ' C G Q S w P) +
        SPBCS.knowledgeError (ringTranscript G C).k
          (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant)
          (kqOf (ringIop G C).merges (ringIop G C).rounds (max 1506 89) (max 1506 89))
          (t + Q * ((bindingBase C G).qPub + (bindingPS C G).q) +
            kqOf (ringIop G C).merges (ringIop G C).rounds (max 1506 89) (max 1506 89))
          (bindingSetting C G).model.senc.digestsPerInput
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
theorem bindingScheme.insiderForgeProb_le_muEufProbWithin (G : Signer ringMsgLen)
    [Fintype G.KeyCoins] [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins]
    [DecidableEq G.SignCoins] [Nonempty G.SignCoins] {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase C G) ×
      Claim (Ring.RStmt G)
        (bindingSetting C G).model.NIProof)
    (f₀ : (bindingBase C G).PK × (bindingBase C G).BMsg ×
      (bindingBase C G).BSig)
    (A : InsiderAdversary (bindingScheme C G) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      Signature.muEufProbWithin (ringMUForger (bindingBase C G) (bindingPS C G)
          Falcon512.Ring.adm64
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat C ringMsgLen_le) _ _ _ _) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds C ringMsgLen_le)
            (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)) f₀
          (embedAdversary (le_max_left n 2) A)
          (insiderFam (bindingBase C G) (bindingPS C G) Falcon512.Ring.adm64
            (max n 2)) 1 Q (bindingQ' C G Q S w P)) (bindingQ' C G Q S w P) Q +
        SPBCS.knowledgeError (ringTranscript G C).k
          (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant)
          (kqOf (ringIop G C).merges (ringIop G C).rounds (max 1506 89) (max 1506 89))
          (t + Q * ((bindingBase C G).qPub + (bindingPS C G).q) +
            kqOf (ringIop G C).merges (ringIop G C).rounds (max 1506 89) (max 1506 89))
          (bindingSetting C G).model.senc.digestsPerInput
          (ringIop G C).merges.nJ (maxError (ringIopSound G C).error) :=
  Ring.StmtVerifiesRing.insiderForgeProb_le_muEufProbWithin (ringHonest G C)
    (ringMergeBounds C ringMsgLen_le) (ringProofFormat C ringMsgLen_le)
    (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)
    (bindsRing_encodeRingMsg G) (Ring.falconBaseSigner_oracleFree G encodeRingMsg)
    (ringIopSound G C) c₀ f₀ A hS Q

/-- **Joint-security unforgeability of the ring-binding Falcon-512 ring signature from MU-EUF-CMA^corr
with the ring-aware and the ordinary signing oracle**
(`Ring.StmtVerifiesRing.jointForgeProb_le_muEufProb`): the bound of
`bindingScheme.insiderForgeProb_le_muEufProb` for the joint-security game. -/
theorem bindingScheme.jointForgeProb_le_muEufProb (G : Signer ringMsgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins] {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase C G) ×
      Claim (Ring.RStmt G)
        (bindingSetting C G).model.NIProof)
    (f₀ : (bindingBase C G).PK × (bindingBase C G).BMsg ×
      (bindingBase C G).BSig)
    (A : JointAdversary (bindingBase C G) (bindingPS C G) Falcon512.Ring.adm64
      n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    jointForgeProb A Q ≤
      Signature.muEufProb (ringMUForger (bindingBase C G) (bindingPS C G)
          Falcon512.Ring.adm64
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat C ringMsgLen_le) _ _ _ _) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds C ringMsgLen_le)
            (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)) f₀
          (embedAdversary (le_max_left n 2) A)
          (jointFam (bindingBase C G) (bindingPS C G) Falcon512.Ring.adm64
            (max n 2)) 1 Q (bindingQ' C G Q S w P)) (bindingQ' C G Q S w P) +
        SPBCS.knowledgeError (ringTranscript G C).k
          (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant)
          (kqOf (ringIop G C).merges (ringIop G C).rounds (max 1506 89) (max 1506 89))
          (t + Q * ((bindingBase C G).qPub + (bindingPS C G).q) +
            kqOf (ringIop G C).merges (ringIop G C).rounds (max 1506 89) (max 1506 89))
          (bindingSetting C G).model.senc.digestsPerInput
          (ringIop G C).merges.nJ (maxError (ringIopSound G C).error) :=
  Ring.StmtVerifiesRing.jointForgeProb_le_muEufProb (ringHonest G C)
    (ringMergeBounds C ringMsgLen_le) (ringProofFormat C ringMsgLen_le)
    (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)
    (bindsRing_encodeRingMsg G) (Ring.falconBaseSigner_oracleFree G encodeRingMsg)
    (ringIopSound G C) c₀ f₀ A hS Q

/-- **The bound of `bindingScheme.jointForgeProb_le_muEufProb` with at most `Q` signing and
corruption requests**:
the multi-user forger wins with at most `Q` signing and corruption requests
(`Signature.muEufProbWithin`), `Q` the requests of the adversary of the ring game. The forger
asks at most `Q` signing and corruption requests on every branch
(`muLaw_ringMUForger_signCorruptCount`), and on the bridge each of them is a logged request of
the relayed forger (`mem_requests_of_bridgeLogs`). -/
theorem bindingScheme.jointForgeProb_le_muEufProbWithin (G : Signer ringMsgLen)
    [Fintype G.KeyCoins] [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins]
    [DecidableEq G.SignCoins] [Nonempty G.SignCoins] {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase C G) ×
      Claim (Ring.RStmt G)
        (bindingSetting C G).model.NIProof)
    (f₀ : (bindingBase C G).PK × (bindingBase C G).BMsg ×
      (bindingBase C G).BSig)
    (A : JointAdversary (bindingBase C G) (bindingPS C G) Falcon512.Ring.adm64
      n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    jointForgeProb A Q ≤
      Signature.muEufProbWithin (ringMUForger (bindingBase C G) (bindingPS C G)
          Falcon512.Ring.adm64
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat C ringMsgLen_le) _ _ _ _) c₀
          (StmtVerifiesRing.extractorList (ringMergeBounds C ringMsgLen_le)
            (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)) f₀
          (embedAdversary (le_max_left n 2) A)
          (jointFam (bindingBase C G) (bindingPS C G) Falcon512.Ring.adm64
            (max n 2)) 1 Q (bindingQ' C G Q S w P)) (bindingQ' C G Q S w P) Q +
        SPBCS.knowledgeError (ringTranscript G C).k
          (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant)
          (kqOf (ringIop G C).merges (ringIop G C).rounds (max 1506 89) (max 1506 89))
          (t + Q * ((bindingBase C G).qPub + (bindingPS C G).q) +
            kqOf (ringIop G C).merges (ringIop G C).rounds (max 1506 89) (max 1506 89))
          (bindingSetting C G).model.senc.digestsPerInput
          (ringIop G C).merges.nJ (maxError (ringIopSound G C).error) :=
  Ring.StmtVerifiesRing.jointForgeProb_le_muEufProbWithin (ringHonest G C)
    (ringMergeBounds C ringMsgLen_le) (ringProofFormat C ringMsgLen_le)
    (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)
    (bindsRing_encodeRingMsg G) (Ring.falconBaseSigner_oracleFree G encodeRingMsg)
    (ringIopSound G C) c₀ f₀ A hS Q

/-- **Joint-security unforgeability of the ring-binding Falcon-512 ring signature from the standard MU-EUF-CMA^corr
game** (`Ring.StmtVerifiesRing.jointForgeProb_le_muEufProbWithin_std` at `bindsRing_encodeRingMsg`; the base signer is
oracle-free, `falconBaseSigner_oracleFree`, and signs a ring as the ordinary signer on the base
message, `falconBaseSigner_ringSignsStd`): for an adversary with the schedule bound `S`, `w`, `P`
(`hS`), the forgery probability is at most the success probability of the binding route's
base-scheme forger `jointStdForger` at `bindingExtractor` in the base scheme's own game
(`SignOracle.std`), with `bindingQ'` requests and at most `Q` signing and corruption requests, plus
spBCS's knowledge error `ksError` at the configuration's largest round error and `ringSignQueries`
(`t + Q · (qPub + PS.q)`) queries.
This holds for every fallback forgery `f₀`; the headline
`bindingScheme.jointForgeProb_le` is its instance at `default`. -/
theorem bindingScheme.jointForgeProb_le_of (G : Signer ringMsgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins] {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase proofSystem G) ×
      Claim (Ring.RStmt G) (bindingSetting proofSystem G).model.NIProof)
    (f₀ : (bindingBase proofSystem G).MUForgery)
    (A : JointAdversary (bindingBase proofSystem G) (bindingPS proofSystem G) Falcon512.Ring.adm64
      n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    jointForgeProb A Q ≤
      Signature.muEufProbWithin (jointStdForger (bindingExtractor proofSystem G c₀ f₀) A Q S w P)
          (bindingQ' proofSystem G Q S w P) Q +
        (bindingSetting proofSystem G).model.ksError (max 1506 89) (max 1506 89) (ringIopSound G proofSystem).error
          (ringSignQueries (bindingBase proofSystem G) (bindingPS proofSystem G) t Q) :=
  Ring.StmtVerifiesRing.jointForgeProb_le_muEufProbWithin_std (ringHonest G proofSystem)
    (ringMergeBounds proofSystem ringMsgLen_le) (ringProofFormat proofSystem ringMsgLen_le) (bindingV proofSystem G)
    (bindsRing_encodeRingMsg G) (Ring.falconBaseSigner_oracleFree G encodeRingMsg)
    (Ring.falconBaseSigner_ringSignsStd G encodeRingMsg) (ringIopSound G proofSystem) c₀ f₀ A hS Q

/-- **Joint-security unforgeability of the ring-binding Falcon-512 ring signature from the standard MU-EUF-CMA^corr
game** (`Ring.StmtVerifiesRing.jointForgeProb_le_muEufProbWithin_std` at `bindsRing_encodeRingMsg`; the base signer is
oracle-free, `falconBaseSigner_oracleFree`, and signs a ring as the ordinary signer on the base
message, `falconBaseSigner_ringSignsStd`): for an adversary with the schedule bound `S`, `w`, `P`
(`hS`), the forgery probability is at most the success probability of the binding route's
base-scheme forger `jointStdForger` at `bindingExtractor` in the base scheme's own game
(`SignOracle.std`), with `bindingQ'` requests and at most `Q` signing and corruption requests, plus
spBCS's knowledge error `ksError` at the configuration's largest round error and `ringSignQueries`
(`t + Q · (qPub + PS.q)`) queries.
At the default fallback forgery (`bindingScheme.jointForgeProb_le_of`: every fallback
forgery). -/
@[headline]
theorem bindingScheme.jointForgeProb_le (G : Signer ringMsgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins] {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase proofSystem G) ×
      Claim (Ring.RStmt G) (bindingSetting proofSystem G).model.NIProof)
    (A : JointAdversary (bindingBase proofSystem G) (bindingPS proofSystem G) Falcon512.Ring.adm64
      n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    jointForgeProb A Q ≤
      Signature.muEufProbWithin (jointStdForger (bindingExtractor proofSystem G c₀ default) A Q S w P)
          (bindingQ' proofSystem G Q S w P) Q +
        (bindingSetting proofSystem G).model.ksError (max 1506 89) (max 1506 89) (ringIopSound G proofSystem).error
          (ringSignQueries (bindingBase proofSystem G) (bindingPS proofSystem G) t Q) :=
  bindingScheme.jointForgeProb_le_of G c₀ default A hS Q

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring-binding Falcon-512 ring signature from the standard MU-EUF-CMA^corr
game** (`Ring.StmtVerifiesRing.insiderForgeProb_le_muEufProbWithin_std` at `bindsRing_encodeRingMsg`; the base signer is
oracle-free, `falconBaseSigner_oracleFree`, and signs a ring as the ordinary signer on the base
message, `falconBaseSigner_ringSignsStd`): for an adversary with the schedule bound `S`, `w`, `P`
(`hS`), the forgery probability is at most the success probability of the binding route's
base-scheme forger `insiderStdForger` at `bindingExtractor` in the base scheme's own game
(`SignOracle.std`), with `bindingQ'` requests and at most `Q` signing and corruption requests, plus
spBCS's knowledge error `ksError` at the configuration's largest round error and `ringSignQueries`
(`t + Q · (qPub + PS.q)`) queries.
This holds for every fallback forgery `f₀`; the headline
`bindingScheme.insiderForgeProb_le` is its instance at `default`. -/
theorem bindingScheme.insiderForgeProb_le_of (G : Signer ringMsgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins] {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase proofSystem G) ×
      Claim (Ring.RStmt G) (bindingSetting proofSystem G).model.NIProof)
    (f₀ : (bindingBase proofSystem G).MUForgery)
    (A : InsiderAdversary (bindingScheme proofSystem G) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      Signature.muEufProbWithin (insiderStdForger (bindingExtractor proofSystem G c₀ f₀) A Q S w P)
          (bindingQ' proofSystem G Q S w P) Q +
        (bindingSetting proofSystem G).model.ksError (max 1506 89) (max 1506 89) (ringIopSound G proofSystem).error
          (ringSignQueries (bindingBase proofSystem G) (bindingPS proofSystem G) t Q) :=
  Ring.StmtVerifiesRing.insiderForgeProb_le_muEufProbWithin_std (ringHonest G proofSystem)
    (ringMergeBounds proofSystem ringMsgLen_le) (ringProofFormat proofSystem ringMsgLen_le) (bindingV proofSystem G)
    (bindsRing_encodeRingMsg G) (Ring.falconBaseSigner_oracleFree G encodeRingMsg)
    (Ring.falconBaseSigner_ringSignsStd G encodeRingMsg) (ringIopSound G proofSystem) c₀ f₀ A hS Q

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring-binding Falcon-512 ring signature from the standard MU-EUF-CMA^corr
game** (`Ring.StmtVerifiesRing.insiderForgeProb_le_muEufProbWithin_std` at `bindsRing_encodeRingMsg`; the base signer is
oracle-free, `falconBaseSigner_oracleFree`, and signs a ring as the ordinary signer on the base
message, `falconBaseSigner_ringSignsStd`): for an adversary with the schedule bound `S`, `w`, `P`
(`hS`), the forgery probability is at most the success probability of the binding route's
base-scheme forger `insiderStdForger` at `bindingExtractor` in the base scheme's own game
(`SignOracle.std`), with `bindingQ'` requests and at most `Q` signing and corruption requests, plus
spBCS's knowledge error `ksError` at the configuration's largest round error and `ringSignQueries`
(`t + Q · (qPub + PS.q)`) queries.
At the default fallback forgery (`bindingScheme.insiderForgeProb_le_of`: every fallback
forgery). -/
@[headline]
theorem bindingScheme.insiderForgeProb_le (G : Signer ringMsgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins] {n t : ℕ}
    (c₀ : RingSignature.RingStmt (bindingBase proofSystem G) ×
      Claim (Ring.RStmt G) (bindingSetting proofSystem G).model.NIProof)
    (A : InsiderAdversary (bindingScheme proofSystem G) n (OracleView.queriesOnly _ _) t)
    {S w P : ℕ} (hS : GameAdversary.ScheduleLE A S w P) (Q : ℕ) :
    insiderForgeProb A Q ≤
      Signature.muEufProbWithin (insiderStdForger (bindingExtractor proofSystem G c₀ default) A Q S w P)
          (bindingQ' proofSystem G Q S w P) Q +
        (bindingSetting proofSystem G).model.ksError (max 1506 89) (max 1506 89) (ringIopSound G proofSystem).error
          (ringSignQueries (bindingBase proofSystem G) (bindingPS proofSystem G) t Q) :=
  bindingScheme.insiderForgeProb_le_of G c₀ default A hS Q

/-- **The statement map of `convertedScheme`** (`Falcon512.Ring.ringVerifies` at the ring message as
the base message, on the configuration's oracle at `32`-byte salts). -/
noncomputable abbrev convertedV {msgLen : ℕ} (G : Signer msgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins] :=
  Falcon512.Ring.ringVerifies G (fun _ (m : Fin msgLen → UInt8) => m)
    (Bits (queryBits (ringTranscript G C).k (2 * (ringTranscript G C).k) 32 (2 ^ 40)))
    (XOut (ringTranscript G C).k (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant))
    program interp

/-- **The facts of the zero-knowledge route at `convertedV`**: the test of the statements of the
empty ring (`Falcon512.Ring.ringVerifies_emptyRingTest`), the injectivity of the statement map
(`Falcon512.Ring.ringVerifies_stmt_injective`, the base message is the ring message) and no honest
statement of the empty ring (`Falcon512.Ring.not_mem_ringHonestRelOf_nil`). -/
noncomputable def convertedV_zkFacts {msgLen : ℕ} (G : Signer msgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins] :
    (convertedV C G).ZKFacts :=
  ⟨Falcon512.Ring.ringVerifies_emptyRingTest .., Falcon512.Ring.ringVerifies_stmt_injective G _ _ _
    program interp fun _ => Function.injective_id, Falcon512.Ring.not_mem_ringHonestRelOf_nil G _ program interp⟩

/-- **The default multi-user forgery of `convertedBase`**, an explicit computable value: the all-zero public
key (`Falcon512.PublicKey`'s default), the all-zero base message and the signature of zero bytes
(`Falcon512.Sig`'s default); the fallback forgery of the converted forgery headlines. -/
instance convertedBase_inhabited {msgLen : ℕ} (G : Signer msgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins] :
    Inhabited (convertedBase G C).MUForgery :=
  ⟨(default, fun _ => 0, default)⟩

/-- **The zero-knowledge route's argument of `convertedScheme`** (`StmtVerifiesRing.ringArgument` at
`convertedV`): the IOP's simulator with the setting's view encoder and the preimages `T`, zero
knowledge from the honest prover without completeness error (`ringHonest_errorBound`), the IOP's
round-by-round extractor (`ringIopSound`), the facts `convertedV_zkFacts` and the fallback forgery
`f₀`. -/
noncomputable def convertedArgument {msgLen : ℕ} (G : Signer msgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins]
    (hmsg : msgLen ≤ 2 ^ 19)
    (T : (convertedSetting G C hmsg).model.Preimages)
    (f₀ : (convertedBase G C).MUForgery) :=
  (convertedV C G).ringArgument (ringHonest G C) (ringMergeBounds C hmsg) (ringHonest_errorBound G C)
    (ringIopSound G C) (convertedV_zkFacts C G) T f₀

/-- **The non-interactive proofs of `convertedSetting` are inhabited**
(`SPBCS.ProofSystemTranscript.nonempty_niProof`): the simulator data of `ringIop` at the ring
statement `default` (`Falcon512.Ring.RStmt.instInhabited`). A theorem, not an instance: instance
search cannot supply the proof `hmsg`. -/
theorem convertedNIProof_nonempty {msgLen : ℕ} (G : Signer msgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins] (hmsg : msgLen ≤ 2 ^ 19) :
    Nonempty (convertedNIProof G C hmsg) :=
  (ringTranscript G C).nonempty_niProof
    (C.fieldIopWithSimData (forkLowering C) (Ring.stmtOf (G := G)) (Ring.ringOk (G := G))) _ _

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the converted
Falcon-512 ring signature from zero knowledge, simulation extraction and MU-EUF-CMA^corr**
(`Ring.StmtVerifiesRing.insiderForgeProb_le_zk_muEufProb` at `convertedArgument`; no ring-binding
base message needed): for a signer carrying the salt (`hG`), correctness error `εc` (`hcorr`) and an
adversary with the schedule bound `S`, `w`, `P'` (`hS`), the forgery probability is at most the
success of the zero-knowledge route's multi-user forger `zkRouteForger` (no refusals predicted, the
public value of a signature its salt) with `zkRouteRequests` requests, plus the zero-knowledge error
`ringZkError` at completeness error `0`, the simulation-extraction error `ringSimExtError`, spBCS's
knowledge error `ksError` at `t + Q · q` queries and `2Q · εc`. The forger's multi-user requests
are `publicKey 0` or corruptions among the adversary's first `Q` requests (`zk_bridge_requests`).
This holds for every preimage table `T` and fallback forgery `f₀`; the headline
`convertedScheme.insiderForgeProb_le` is its instance at `convertedPreimages` and `default`. -/
theorem convertedScheme.insiderForgeProb_le_of {msgLen : ℕ} (G : Signer msgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins]
    (hmsg : msgLen ≤ 2 ^ 19) (hG : G.CarriesSalt) {εc : ℝ≥0∞}
    (hcorr : (convertedBase G proofSystem).CorrectWithin εc)
    (T : (convertedSetting G proofSystem hmsg).model.Preimages) {n t : ℕ}
      [NeZero n]
    (A : InsiderAdversary (convertedScheme G proofSystem hmsg) n (OracleView.queriesOnly _ _) t)
    (Q : ℕ)
    (f₀ : (convertedBase G proofSystem).MUForgery)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    haveI := convertedNIProof_nonempty proofSystem G hmsg
    insiderForgeProb A Q ≤
      Signature.muEufProb
          (Insider.zkRouteForger A (convertedV proofSystem G).wit (convertedArgument proofSystem G hmsg T f₀)
            (convertedBase G proofSystem).noRefusal Prod.fst Q)
          (Insider.zkRouteRequests A (convertedArgument proofSystem G hmsg T f₀) Q S w P') +
        Insider.ringZkError (convertedSetting G proofSystem hmsg).model 0 t Q +
        Insider.ringSimExtError A (convertedArgument proofSystem G hmsg T f₀) Q +
        (convertedSetting G proofSystem hmsg).model.ksError (max 1506 89) (max 1506 89)
          (ringIopSound G proofSystem).error (t + Q * (convertedScheme G proofSystem hmsg).q) +
        2 * Q * εc :=
  have := convertedNIProof_nonempty proofSystem G hmsg
  StmtVerifiesRing.insiderForgeProb_le_zk_muEufProb (ringHonest G proofSystem)
    (ringMergeBounds proofSystem hmsg) (ringProofFormat proofSystem hmsg) _
    (hk := ⟨Nat.succ_ne_zero 31⟩) (ringHonest_errorBound G proofSystem) (ringIopSound G proofSystem)
    (falconBaseSigner_oracleFree G _) (falconBaseSigner_pubOfCoins G _ hG)
    (falconBaseSigner_refusalOfCoins G _) hcorr (convertedV_zkFacts proofSystem G) T A Q f₀ hS

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the converted
Falcon-512 ring signature from zero knowledge, simulation extraction and MU-EUF-CMA^corr**
(`Ring.StmtVerifiesRing.insiderForgeProb_le_zk_muEufProb` at `convertedArgument`; no ring-binding
base message needed): for a signer carrying the salt (`hG`), correctness error `εc` (`hcorr`) and an
adversary with the schedule bound `S`, `w`, `P'` (`hS`), the forgery probability is at most the
success of the zero-knowledge route's multi-user forger `zkRouteForger` (no refusals predicted, the
public value of a signature its salt) with `zkRouteRequests` requests, plus the zero-knowledge error
`ringZkError` at completeness error `0`, the simulation-extraction error `ringSimExtError`, spBCS's
knowledge error `ksError` at `t + Q · q` queries and `2Q · εc`. The forger's multi-user requests
are `publicKey 0` or corruptions among the adversary's first `Q` requests (`zk_bridge_requests`).
At the canonical preimage table `convertedPreimages` and the default fallback forgery
(`convertedScheme.insiderForgeProb_le_of`: every table and fallback forgery). -/
@[headline]
theorem convertedScheme.insiderForgeProb_le {msgLen : ℕ} (G : Signer msgLen) [Fintype G.KeyCoins]
    [DecidableEq G.KeyCoins] [Nonempty G.KeyCoins] [Fintype G.SignCoins] [DecidableEq G.SignCoins]
    [Nonempty G.SignCoins]
    (hmsg : msgLen ≤ 2 ^ 19) (hG : G.CarriesSalt) {εc : ℝ≥0∞}
    (hcorr : (convertedBase G proofSystem).CorrectWithin εc)
    {n t : ℕ} [NeZero n]
    (A : InsiderAdversary (convertedScheme G proofSystem hmsg) n (OracleView.queriesOnly _ _) t)
    (Q : ℕ)
    {S w P' : ℕ} (hS : GameAdversary.ScheduleLE A S w P') :
    haveI := convertedNIProof_nonempty proofSystem G hmsg
    insiderForgeProb A Q ≤
      Signature.muEufProb
          (Insider.zkRouteForger A (convertedV proofSystem G).wit (convertedArgument proofSystem G hmsg (convertedPreimages G proofSystem hmsg) default)
            (convertedBase G proofSystem).noRefusal Prod.fst Q)
          (Insider.zkRouteRequests A (convertedArgument proofSystem G hmsg (convertedPreimages G proofSystem hmsg) default) Q S w P') +
        Insider.ringZkError (convertedSetting G proofSystem hmsg).model 0 t Q +
        Insider.ringSimExtError A (convertedArgument proofSystem G hmsg (convertedPreimages G proofSystem hmsg) default) Q +
        (convertedSetting G proofSystem hmsg).model.ksError (max 1506 89) (max 1506 89)
          (ringIopSound G proofSystem).error (t + Q * (convertedScheme G proofSystem hmsg).q) +
        2 * Q * εc :=
  convertedScheme.insiderForgeProb_le_of G hmsg hG hcorr _ A Q default hS

end GordieHowe.Falcon512.Ring.Native.ROMParams
