-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Carrier.ROMParams
public import GordieHowe.Applications.Falcon512.Ring.RingBase
public import GordieHowe.Applications.Falcon512.Ring.RingEncoding
public import GordieHowe.Applications.Ring.StmtAnon
public import GordieHowe.Applications.Ring.RingInsiderStmt

@[expose] public section

/-!
# GordieHowe: the Falcon-512 ring signature of `Falcon512.Ring.Carrier.ROMParams`

The ring signature `ofBase (falconBaseSigner G bmsg) PS adm64` (BKM06 Definition 1,
`GordieHowe/Model/RingSignature/Base.lean`) whose proof system `PS` is the configuration's compiled
program (`GordieHowe/Applications/Falcon512/Ring/Carrier/ROMParams.lean`) read at the ring statements of
the base signer (`Ring.StmtVerifiesRing.proofSystem` at `Falcon512.Ring.ringVerifies`), and its
completeness, anonymity and unforgeability headlines, each an instance of a generic theorem of
`GordieHowe/Applications/Ring/StmtBase.lean` or `GordieHowe/Applications/Ring/StmtAnon.lean`.

The configuration's IOP, transcript and honest strategy are stated at a Falcon signer with
`32`-byte messages. The program statement `Ring.stmtOf` holds the message only through the
coefficients of `HashToPoint(r ‖ m)`, and the transcript writes the ring statement with the
statement codec `Native.stmtCodecN`. The definitions are restated here at a signer
`G : Signer msgLen` of every message length (`ringIop`, `ringIopSound`, `ringTranscript`,
`ringHonestStrategy`), equal to the configuration's at `msgLen = 32` (`ringIop_eq`,
`ringTranscript_eq`, `ringHonestStrategy_eq`). The setting's facts hold at `msgLen ≤ 2^19`, with
the statement writes within `2^20` bytes (`ringTranscript_bounds`).

* **The setting**: `ringTranscript_bounds`, `ringMergeBounds` (at `msgLen ≤ 2^19`),
  `ringFigures` (the configuration's figures), `ringProofFormat` (proofs in the format `max 2560 96`).
* **The honest prover** `ringHonest G C`: the configuration's at the honest strategy
  `ringHonestStrategy G` (its completeness errors sum to `0`: `ringHonestStrategy_delta`), without
  completeness error (`ringHonest_errorBound`), at the proof system's acceptance of the honest
  inputs (`accept`, proved from the certificate at `proofSystem`: `GordieHowe/Generated/Falcon512/Ring/Carrier/ROMParams/Certified.lean`).
* **The scheme** `scheme G C hmsg bmsg` on the base signer `baseSigner G C bmsg` at any base
  message `bmsg` of the ring and a ring message; its two shapes: `convertedScheme G C hmsg`
  (`bmsg R m = m`, converted signatures) and `bindingScheme C G` (`bmsg = encodeRingMsg`, the
  message followed by the ring, at `ringMsgLen`, which binds the ring: `bindsRing_encodeRingMsg`).
* **The headlines**: `convertedScheme.completeAtWithin`, `bindingScheme.completeAtWithin`
  (`StmtVerifiesRing.completeAtWithin`: refusal `0`, rejection at most the signer's correctness
  error plus spBCS's terms) and their averaged forms `convertedScheme.completeWithin`,
  `bindingScheme.completeWithin` (`StmtVerifiesRing.completeWithin` at
  `RefuseAtWithin.refuseWithin`); `convertedScheme.anonAdvantage_le`,
  `bindingScheme.anonAdvantage_le` (`StmtVerifiesRing.anonAdvantage_le_of_pubOfCoins`: the salt is
  read off the coins for a signer carrying it, `Signer.CarriesSalt`, satisfiable by
  `exists_carriesSalt`; no refusal; at most `card (AnonRequest …)` valid challenges).
* **The extraction-forger bounds** `bindingScheme.insiderForgeProb_le_extractionSuccess`,
  `bindingScheme.keyReuseForgeProb_le_extractionSuccess` (`StmtVerifiesRing.insiderForgeProb_le`,
  `StmtVerifiesRing.keyReuseForgeProb_le`: the extraction forger's success plus spBCS's knowledge
  error at the configuration's largest round error); `convertedScheme.insiderForgeProb_le_zkForgerTerm`
  (`StmtVerifiesRing.insiderForgeProb_le_zk`: unforgeability of `convertedScheme` with no
  ring-binding message, by zero knowledge and simulation extraction: the extraction forger's term,
  `zkError 0 t Q`, the simulation-extraction and knowledge errors and `2Q · εc`, for a signer
  carrying the salt). Their forms by MU-EUF-CMA^corr,
  `bindingScheme.insiderForgeProb_le_muEufProbWithin`,
  `bindingScheme.keyReuseForgeProb_le_muEufProbWithin` and
  `convertedScheme.insiderForgeProb_le`, are the unforgeability headlines.
-/

namespace GordieHowe.Falcon512.Ring.Carrier.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
  GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring GordieHowe.RingSignature
open Generated.Falcon512.Ring.Carrier.ROMParams.Program (program)
open Generated.Falcon512.Ring.Carrier.ROMParams (interp ready ProofSystems figures figures_eq
  figuresOk numbers branchName branchName_le
  fieldBytes msgB_le samplerReaders chalLoadMax
  chalLoad_le grantMax)
open Generated.Falcon512.Ring.Carrier.ROMParams.Facts (interpModel)
open _root_.GordieHowe.Falcon512.Ring.Native (Signer CoreWit)
open scoped NNReal ENNReal

variable {msgLen : ℕ} (G : Signer msgLen) (C : ProofSystems)

/-! ## The IOP, its transcript and the setting at every message length -/

/-- **The configuration's multi-circuit IOP with forked domains at the ring statements of `G`**
(`forkIop` at every message length): the generic per-field domain proofs with the proof system's
application phase, the statement read as its program statement and checked
(`RealizedProgram.ProofSystem.IOP.comapWith Ring.stmtOf Ring.ringOk`). -/
abbrev ringIop : RealizedProgram.ProofSystem.IOP (Ring.RStmt G)
    (program.Valuation interp → CoreWit) (Ring.ringStmtRelOf G program interp) :=
  C.fieldIopWith ready (forkLowering C) Ring.stmtOf Ring.ringOk

/-- The soundness data of `ringIop` (`forkIopSound` at every message length). -/
noncomputable abbrev ringIopSound : (ringIop G C).Sound :=
  ((C.fieldBranches ready).soundIOPSound
    (C.fieldBranchesSound ready) source_rbr_knowledge_soundness
    sourceError_final).comapWith Ring.stmtOf Ring.ringOk

/-- **The configuration's transcript at the ring statements of `G`** (`forkTranscript` at every
message length): the label, `figures.k`-byte digests, the ring statement's writes
(`Native.stmtCodecN` at `64` keys), the branch name, the phase's and the domain's codecs and
readers. The largest grant of a round is `grantMax`. -/
abbrev ringTranscript : ProofSystemTranscript (ringIop G C) :=
  C.fieldForkTranscriptWith ready (forkLowering C) Ring.stmtOf numbers.cod
    (numbers.fits C.enforce)
    Ring.ringOk label figures.k (_root_.GordieHowe.Falcon512.Ring.Native.stmtCodecN G 64)
    (fun a => branchName a.1) (program.appWrites fieldBytes msgB_le)
    (program.appReaders samplerReaders (fun _ => chalLoadMax) chalLoad_le) grantMax

/-- **At `32`-byte messages `ringIop` is the configuration's IOP.** -/
theorem ringIop_eq (G : Signer 32) : ringIop G C = forkIop G C :=
  rfl

/-- **At `32`-byte messages `ringTranscript` is the configuration's transcript.** -/
theorem ringTranscript_eq (G : Signer 32) : ringTranscript G C = forkTranscript G C :=
  rfl

variable {G} in
/-- **The facts the setting is built from** at messages of at most `2^19` bytes (`hmsg`): the
statement writes within `2^20` bytes, the label and the branch name, the rest from the generated
check (`RealizedProgram.ProgramFigures.Check.transcriptWith_bounds`). -/
theorem ringTranscript_bounds (hmsg : msgLen ≤ 2 ^ 19) : (ringTranscript G C).Bounds :=
  figuresOk.transcriptWith_bounds Ring.ringOk (fun x => (_root_.GordieHowe.Falcon512.Ring.Native.length_ser_stmtCodecN_le x).trans
      (by omega))
    (Nat.le_of_ble_eq_true rfl) (fun a => branchName_le a.1)

variable {G} in
/-- **The setting's facts with `32`-byte salts** at messages of at most `2^19` bytes. -/
theorem ringMergeBounds (hmsg : msgLen ≤ 2 ^ 19) : (ringTranscript G C).MergeBounds 32 :=
  ⟨ringTranscript_bounds C hmsg, by norm_num⟩

/-- **The figures of `ringIop`** (`RealizedProgram.ProgramFigures.Check.figuresWith`, the generated
figures),
the configuration's: at most `955` rounds, trees of at most `2560` leaves, `96` queried leaves,
`3160` verifier queries, `958` digests per input and `2560` positions. -/
theorem ringFigures : (ringIop G C).Figures 955 2560 96 3160 958 2560 :=
  by simpa only [figures_eq] using
    figuresOk.figuresWith (B := C) (Lw := forkLowering C) (f := Ring.stmtOf) Ring.ringOk

variable {G} in
/-- **The proof format `max 2560 96`**: every tree has at most `2560` leaves and every query phase opens
at most `96` positions (`ringFigures`). -/
theorem ringProofFormat (hmsg : msgLen ≤ 2 ^ 19) :
    (ringTranscript G C).ProofFormat 32 (ringMergeBounds C hmsg) (max 2560 96) :=
  ProofSystemTranscript.formatBounds (ringMergeBounds C hmsg)
    (fun d => ((ringFigures G C).leaves_le d).trans (le_max_left _ _))
    fun ch => ((ringFigures G C).queries_le ch).trans (le_max_right _ _)

/-! ## The honest prover -/

/-- **The honest strategy at the ring statements of `G`** (`honestStrategy` at every message
length): `RealizedProgram.HonestStrategy.ofCompletionReady` at the execution
`Ring.carrierSourceExecution`. -/
noncomputable def ringHonestStrategy :
    program.HonestStrategy interp (Ring.relH G program interp) :=
  RealizedProgram.HonestStrategy.ofCompletionReady completionReady
    (Ring.carrierSourceExecution program interp _ interpModel.registered interpModel.lawful
      completionReady.facts.committed completionReady.facts.boundNoCopy completionReady.roles
      completionReady.oneNodes interpModel.bitNodes Generated.Falcon512.Ring.Carrier.ROMParams.Completion.noFieldForm)

/-- **At `32`-byte messages `ringHonestStrategy` is the configuration's.** -/
theorem ringHonestStrategy_eq (G : Signer 32) : ringHonestStrategy G = honestStrategy G :=
  rfl

/-- **The honest strategy's completeness errors are `0`.** -/
theorem ringHonestStrategy_delta : ∑ k, (ringHonestStrategy G).δ k = 0 := by
  rw [ringHonestStrategy, RealizedProgram.HonestStrategy.ofCompletionReady_δ, Ring.carrierSourceExecution_δ (I := interp)]
  simp

/-- **The honest prover of `ringIop`** at the honest strategy `ringHonestStrategy G`
(`RealizedProgram.ProofSystem.fieldIopWithHonest`): the proof system's phased honest prover and the
forked domain's honest prover on the generic per-field domain proofs, read through the program
statement and checked. -/
noncomputable abbrev ringHonest :=
  C.fieldIopWithHonest (forkLowering C) (Ring.stmtOf (G := G))
    (Ring.ringOk (G := G)) (ringHonestStrategy G).toHonestCore

/-- **The honest prover has completeness error `0`**
(`RealizedProgram.ProofSystem.FieldBranches.errorBound_honestAt`, `HonestStrategy.complete`,
`ringHonestStrategy_delta`). -/
theorem ringHonest_errorBound :
    (ringHonest G C).app.ErrorBound fun _ => 0 := by
  have h := ((C.fieldBranches ready).errorBound_honestAt (forkLowering C)
    (C.fieldHonestDomains ready)
    (C.fieldForkHonestDomains ready) (ringHonestStrategy G).toHonestCore
    (ringHonestStrategy G).complete).comapWith (Ring.stmtOf (G := G)) (Ring.ringOk (G := G))
  rwa [ringHonestStrategy_delta] at h

/-! ## The scheme -/

variable {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]

/-- The Falcon-512 base signer of the scheme: `falconBaseSigner G bmsg` on the compiled oracle of
`ringTranscript G C` at `32`-byte salts. -/
abbrev baseSigner (bmsg : KeyRing _root_.GordieHowe.Falcon512.Ring.Native.PublicKey 64 → RMsg →
    (Fin msgLen → UInt8)) :=
  falconBaseSigner («X» := Bits (queryBits (ringTranscript G C).k (2 * (ringTranscript G C).k) 32
      (2 ^ 40)))
    («Y» := XOut (ringTranscript G C).k (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant))
    (N := 64) G bmsg

/-- **The Falcon-512 ring signature of `Falcon512.Ring.Carrier.ROMParams`** at the base message `bmsg`:
`ofBase (falconBaseSigner G bmsg) PS adm64` with `PS` the configuration's compiled
program read at the base signer's ring statements (`StmtVerifiesRing.proofSystem` at
`Falcon512.Ring.ringVerifies`, the honest prover `ringHonest G C`, proofs in the format `max 2560 96`),
on rings of exactly `64` keys. -/
noncomputable abbrev scheme (hmsg : msgLen ≤ 2 ^ 19)
    (bmsg : KeyRing _root_.GordieHowe.Falcon512.Ring.Native.PublicKey 64 → RMsg →
      (Fin msgLen → UInt8)) :=
  ofBase (baseSigner G C bmsg)
    ((Falcon512.Ring.ringVerifies G bmsg _ _ program interp).proofSystem (ringHonest G C)
      (ringMergeBounds C hmsg) (ringProofFormat C hmsg)) Falcon512.Ring.adm64

/-- **The converted Falcon-512 ring signature** (`bmsg R m = m`): `scheme` at the ring message as
the base message. -/
noncomputable abbrev convertedScheme
    (hmsg : msgLen ≤ 2 ^ 19) :=
  scheme G C hmsg (RMsg := Fin msgLen → UInt8) fun _ m => m

/-- **The ring-binding Falcon-512 ring signature** (`bmsg = encodeRingMsg`: the `32`-byte message
followed by the ring, `ringMsgLen` bytes): `scheme` at a signer of `ringMsgLen`-byte messages. -/
noncomputable abbrev bindingScheme (G : Signer ringMsgLen) :=
  scheme G C ringMsgLen_le encodeRingMsg

/-! ## The headlines -/

/-- **Completeness per key of the converted Falcon-512 ring signature**
(`StmtVerifiesRing.completeAtWithin`): for a Falcon signer whose base signer has correctness error
`εc` (`hc`), at every key and every ring of `64` keys holding it, `convertedScheme` refuses with
probability `0` (`falconBaseSigner_refuseAtWithin`) and is rejected with probability at most
`εc` plus the honest prover's completeness error `0`, spBCS's overrun and key-collision terms
and `0 / 2^(8 · 32)`. -/
@[headline]
theorem convertedScheme.completeAtWithin
    (hmsg : msgLen ≤ 2 ^ 19) {εc : ℝ≥0∞}
    (hc : (baseSigner G proofSystem (RMsg := Fin msgLen → UInt8) fun _ m => m).CorrectWithin εc) :
    (convertedScheme G proofSystem hmsg).CompleteAtWithin 0
      (εc + (((0 : ℝ≥0) : ℝ≥0∞) + ((ringTranscript G proofSystem).setting 32 (ringMergeBounds proofSystem hmsg)).model.overrun +
        SPBCS.keyCollision ((ringIop G proofSystem).term.size (ringIop G proofSystem).rounds) (ringTranscript G proofSystem).k +
          ((0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ (8 * 32))) :=
  StmtVerifiesRing.completeAtWithin (ringHonest G proofSystem) (ringMergeBounds proofSystem hmsg)
    (ringProofFormat proofSystem hmsg) _ (ringHonest_errorBound G proofSystem)
    (falconBaseSigner_refuseAtWithin G _ _) hc

/-- **Completeness per key of the ring-binding Falcon-512 ring signature**
(`StmtVerifiesRing.completeAtWithin`): as `convertedScheme.completeAtWithin`, for `bindingScheme`. -/
@[headline]
theorem bindingScheme.completeAtWithin (G : Signer ringMsgLen) {εc : ℝ≥0∞}
    (hc : (baseSigner G proofSystem encodeRingMsg).CorrectWithin εc) :
    (bindingScheme proofSystem G).CompleteAtWithin 0
      (εc + (((0 : ℝ≥0) : ℝ≥0∞) +
        ((ringTranscript G proofSystem).setting 32 (ringMergeBounds proofSystem ringMsgLen_le)).model.overrun +
        SPBCS.keyCollision ((ringIop G proofSystem).term.size (ringIop G proofSystem).rounds) (ringTranscript G proofSystem).k +
          ((0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ (8 * 32))) :=
  StmtVerifiesRing.completeAtWithin (ringHonest G proofSystem) (ringMergeBounds proofSystem ringMsgLen_le)
    (ringProofFormat proofSystem ringMsgLen_le) _ (ringHonest_errorBound G proofSystem)
    (falconBaseSigner_refuseAtWithin G _ _) hc

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring-binding
Falcon-512 ring signature** (`StmtVerifiesRing.insiderForgeProb_le` at
`bindsRing_encodeRingMsg`): the forgery probability of an adversary of BKM06 Definition 7 against
`bindingScheme` (start input the honest public keys, the oracle by at most `t` queries, `Q`
requests) is at most the success probability of the extraction forger in MU-EUF-CMA^corr with the
ring-aware signing oracle plus spBCS's knowledge error at the configuration's largest round error
and `t + Q · q + kq` queries. -/
theorem bindingScheme.insiderForgeProb_le_extractionSuccess (G : Signer ringMsgLen) {n t : ℕ}
    (A : InsiderAdversary (bindingScheme C G) n (OracleView.queriesOnly _ _) t) (Q : ℕ) :
    insiderForgeProb A Q ≤
      extractionSuccess (insiderRelay (baseSigner G C encodeRingMsg) _ _) A Q
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat C ringMsgLen_le) _ _ _ _)
          (StmtVerifiesRing.extractor (ringMergeBounds C ringMsgLen_le)
            (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)) +
        SPBCS.knowledgeError (ringTranscript G C).k
          (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant)
          (kqOf (ringIop G C).merges (ringIop G C).rounds (max 2560 96) (max 2560 96))
          (t + Q * (bindingScheme C G).q + kqOf (ringIop G C).merges (ringIop G C).rounds (max 2560 96) (max 2560 96))
          ((ringTranscript G C).setting 32 (ringMergeBounds C ringMsgLen_le)).model.senc.digestsPerInput
          (ringIop G C).merges.nJ (maxError (ringIopSound G C).error) :=
  StmtVerifiesRing.insiderForgeProb_le (ringHonest G C) (ringMergeBounds C ringMsgLen_le)
    (ringProofFormat C ringMsgLen_le) _ (bindsRing_encodeRingMsg G) (ringIopSound G C) A Q

/-- **Key-reuse unforgeability of the ring-binding Falcon-512 ring signature**
(`StmtVerifiesRing.keyReuseForgeProb_le` at `bindsRing_encodeRingMsg`): the bound of
`bindingScheme.insiderForgeProb_le_extractionSuccess` for the key-reuse game, the extraction forger in
MU-EUF-CMA^corr with the ring-aware and the ordinary signing oracle. -/
theorem bindingScheme.keyReuseForgeProb_le_extractionSuccess (G : Signer ringMsgLen) {n t : ℕ}
    (A : KeyReuseAdversary (baseSigner G C encodeRingMsg)
      ((Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp).proofSystem
        (ringHonest G C) (ringMergeBounds C ringMsgLen_le) (ringProofFormat C ringMsgLen_le))
      Falcon512.Ring.adm64 n (OracleView.queriesOnly _ _) t) (Q : ℕ) :
    keyReuseForgeProb A Q ≤
      extractionSuccess (keyReuseRelay (baseSigner G C encodeRingMsg) _ _) A Q
          (compiledBy_spbcsComapProofSystem _ _ _ (ringProofFormat C ringMsgLen_le) _ _ _ _)
          (StmtVerifiesRing.extractor (ringMergeBounds C ringMsgLen_le)
            (Falcon512.Ring.ringVerifies G encodeRingMsg _ _ program interp)) +
        SPBCS.knowledgeError (ringTranscript G C).k
          (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant)
          (kqOf (ringIop G C).merges (ringIop G C).rounds (max 2560 96) (max 2560 96))
          (t + Q * (bindingScheme C G).q + kqOf (ringIop G C).merges (ringIop G C).rounds (max 2560 96) (max 2560 96))
          ((ringTranscript G C).setting 32 (ringMergeBounds C ringMsgLen_le)).model.senc.digestsPerInput
          (ringIop G C).merges.nJ (maxError (ringIopSound G C).error) :=
  StmtVerifiesRing.keyReuseForgeProb_le (ringHonest G C) (ringMergeBounds C ringMsgLen_le)
    (ringProofFormat C ringMsgLen_le) _ (bindsRing_encodeRingMsg G) (ringIopSound G C) A Q

/-- **Completeness of the converted Falcon-512 ring signature, averaged over honest rings**
(`StmtVerifiesRing.completeWithin` at `RefuseAtWithin.refuseWithin` of
`falconBaseSigner_refuseAtWithin`): refusal `0`, rejection as in
`convertedScheme.completeAtWithin`. -/
@[headline]
theorem convertedScheme.completeWithin
    (hmsg : msgLen ≤ 2 ^ 19) {εc : ℝ≥0∞}
    (hc : (baseSigner G proofSystem (RMsg := Fin msgLen → UInt8) fun _ m => m).CorrectWithin εc) :
    (convertedScheme G proofSystem hmsg).CompleteWithin 0
      (εc + (((0 : ℝ≥0) : ℝ≥0∞) + ((ringTranscript G proofSystem).setting 32 (ringMergeBounds proofSystem hmsg)).model.overrun +
        SPBCS.keyCollision ((ringIop G proofSystem).term.size (ringIop G proofSystem).rounds) (ringTranscript G proofSystem).k +
          ((0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ (8 * 32))) :=
  StmtVerifiesRing.completeWithin (ringHonest G proofSystem) (ringMergeBounds proofSystem hmsg)
    (ringProofFormat proofSystem hmsg) _ (ringHonest_errorBound G proofSystem)
    (falconBaseSigner_refuseAtWithin G _ _).refuseWithin hc

/-- **Completeness of the ring-binding Falcon-512 ring signature, averaged over honest rings**
(`StmtVerifiesRing.completeWithin` at `RefuseAtWithin.refuseWithin`). -/
@[headline]
theorem bindingScheme.completeWithin (G : Signer ringMsgLen) {εc : ℝ≥0∞}
    (hc : (baseSigner G proofSystem encodeRingMsg).CorrectWithin εc) :
    (bindingScheme proofSystem G).CompleteWithin 0
      (εc + (((0 : ℝ≥0) : ℝ≥0∞) +
        ((ringTranscript G proofSystem).setting 32 (ringMergeBounds proofSystem ringMsgLen_le)).model.overrun +
        SPBCS.keyCollision ((ringIop G proofSystem).term.size (ringIop G proofSystem).rounds) (ringTranscript G proofSystem).k +
          ((0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ (8 * 32))) :=
  StmtVerifiesRing.completeWithin (ringHonest G proofSystem) (ringMergeBounds proofSystem ringMsgLen_le)
    (ringProofFormat proofSystem ringMsgLen_le) _ (ringHonest_errorBound G proofSystem)
    (falconBaseSigner_refuseAtWithin G _ _).refuseWithin hc

/-- **Anonymity against full key exposure (BKM06 Definition 4, `Q` adaptive challenges) of the
converted Falcon-512 ring signature** (`StmtVerifiesRing.anonAdvantage_le_of_pubOfCoins`): for a
signer whose signatures carry the drawn salt (`hG`) and whose base signer has correctness error
`εc` (`hcorr`), every anonymity adversary (any oracle view, at most `t` queries) has advantage at
most `Q · wiError 0 (Q · |AnonRequest|) + 2Q · εc + 2Q · 0` (the honest prover has no completeness
error and the signer never refuses). -/
@[headline]
theorem convertedScheme.anonAdvantage_le
    (hmsg : msgLen ≤ 2 ^ 19) (hG : G.CarriesSalt) {εc : ℝ≥0}
    (hcorr : (baseSigner G proofSystem (RMsg := Fin msgLen → UInt8) fun _ m => m).CorrectWithin εc) {n : ℕ}
    {Vw : OracleView (Bits (queryBits (ringTranscript G proofSystem).k (2 * (ringTranscript G proofSystem).k) 32
      (2 ^ 40))) (XOut (ringTranscript G proofSystem).k
        (Configurations.fsExtraBytes + (ringTranscript G proofSystem).maxGrant))} {t : ℕ}
    (A : AnonAdversary (convertedScheme G proofSystem hmsg) n Vw t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * ((ringTranscript G proofSystem).setting 32 (ringMergeBounds proofSystem hmsg)).model.wiError 0
          (Q * Fintype.card (AnonRequest (convertedScheme G proofSystem hmsg) n)) +
        2 * Q * εc + 2 * Q * ((0 : ℝ≥0) : ℝ) :=
  StmtVerifiesRing.anonAdvantage_le_of_pubOfCoins (ringHonest G proofSystem) (ringMergeBounds proofSystem hmsg)
    (ringProofFormat proofSystem hmsg) _ (ringHonest_errorBound G proofSystem) (falconBaseSigner_oracleFree G _)
    (fun _ => Finset.card_filter_le _ _) (falconBaseSigner_pubOfCoins G _ hG) hcorr
    (fun H kc Rg m _ => falconBaseSigner_refusal_le_zero G _ H kc Rg _ m) A Q

/-- **Anonymity against full key exposure (BKM06 Definition 4, `Q` adaptive challenges) of the
ring-binding Falcon-512 ring signature** (`StmtVerifiesRing.anonAdvantage_le_of_pubOfCoins`): the
bound of `convertedScheme.anonAdvantage_le` for `bindingScheme`. -/
@[headline]
theorem bindingScheme.anonAdvantage_le (G : Signer ringMsgLen) (hG : G.CarriesSalt) {εc : ℝ≥0}
    (hcorr : (baseSigner G proofSystem encodeRingMsg).CorrectWithin εc) {n : ℕ}
    {Vw : OracleView (Bits (queryBits (ringTranscript G proofSystem).k (2 * (ringTranscript G proofSystem).k) 32
      (2 ^ 40))) (XOut (ringTranscript G proofSystem).k
        (Configurations.fsExtraBytes + (ringTranscript G proofSystem).maxGrant))} {t : ℕ}
    (A : AnonAdversary (bindingScheme proofSystem G) n Vw t) (Q : ℕ) :
    anonAdvantage A Q ≤
      Q * ((ringTranscript G proofSystem).setting 32 (ringMergeBounds proofSystem ringMsgLen_le)).model.wiError 0
          (Q * Fintype.card (AnonRequest (bindingScheme proofSystem G) n)) +
        2 * Q * εc + 2 * Q * ((0 : ℝ≥0) : ℝ) :=
  StmtVerifiesRing.anonAdvantage_le_of_pubOfCoins (ringHonest G proofSystem)
    (ringMergeBounds proofSystem ringMsgLen_le) (ringProofFormat proofSystem ringMsgLen_le) _
    (ringHonest_errorBound G proofSystem) (falconBaseSigner_oracleFree G _)
    (fun _ => Finset.card_filter_le _ _) (falconBaseSigner_pubOfCoins G _ hG) hcorr
    (fun H kc Rg m _ => falconBaseSigner_refusal_le_zero G _ H kc Rg _ m) A Q

/-- The converted base signer's messages are inhabited (`Falcon512.Ring.nonempty_msg`). -/
instance baseSigner_nonempty_msg :
    Nonempty (baseSigner G C (RMsg := Fin msgLen → UInt8) fun _ m => m).Msg :=
  Falcon512.Ring.nonempty_msg G _

/-- The base signer's public values are inhabited (`Falcon512.Ring.nonempty_pub`). -/
instance baseSigner_nonempty_pub
    (bmsg : KeyRing _root_.GordieHowe.Falcon512.Ring.Native.PublicKey 64 → RMsg →
      (Fin msgLen → UInt8)) :
    Nonempty (baseSigner G C bmsg).Pub :=
  Falcon512.Ring.nonempty_pub G bmsg

/-- The base signer's signatures are inhabited (`Falcon512.Ring.nonempty_bsig`). -/
instance baseSigner_nonempty_bsig
    (bmsg : KeyRing _root_.GordieHowe.Falcon512.Ring.Native.PublicKey 64 → RMsg →
      (Fin msgLen → UInt8)) :
    Nonempty (baseSigner G C bmsg).BSig :=
  Falcon512.Ring.nonempty_bsig G bmsg

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the converted
Falcon-512 ring signature, by zero knowledge and simulation extraction**
(`StmtVerifiesRing.insiderForgeProb_le_zk`; no ring-binding base message needed): for a signer
whose signatures carry the drawn salt (`hG`) and whose base signer has correctness error `εc`
(`hcorr`), the forgery probability of an adversary of BKM06 Definition 7 against `convertedScheme`
is at most the extraction forger's term (`zkForgerTerm`, refusals empty, public values the salts),
`zkError 0 t Q` (the honest prover has no completeness error), the simulation-extraction error,
spBCS's knowledge error at the configuration's largest round error, and `2 Q εc`. `T`: the
preimage table of the joint simulator. -/
theorem convertedScheme.insiderForgeProb_le_zkForgerTerm
    (hmsg : msgLen ≤ 2 ^ 19) (hG : G.CarriesSalt) {εc : ℝ≥0∞}
    (hcorr : (baseSigner G C (RMsg := Fin msgLen → UInt8) fun _ m => m).CorrectWithin εc)
    (T : ((ringTranscript G C).setting 32 (ringMergeBounds C hmsg)).model.Preimages) {n t : ℕ}
    (A : InsiderAdversary (convertedScheme G C hmsg) n (OracleView.queriesOnly _ _) t)
    (Q : ℕ) :
    insiderForgeProb A Q ≤
      RingSignature.Insider.zkForgerTerm A
          (Falcon512.Ring.ringVerifies G (fun _ m => m) _ _ program interp).wit
          (fun _ _ _ _ => False) Prod.fst
          ((ringTranscript G C).setting 32 (ringMergeBounds C hmsg)).viewEncoder id
          (RealizedProgram.ProofSystem.IOP.simulator
            (C.fieldIopWithSimData (forkLowering C) (Ring.stmtOf (G := G))
              (Ring.ringOk (G := G))))
          T (ringIop G C).extractor Q +
        ENNReal.ofReal (((ringTranscript G C).setting 32 (ringMergeBounds C hmsg)).model.zkError 0
          t Q) +
        ((ringTranscript G C).setting 32 (ringMergeBounds C hmsg)).model.simExtractionError
          (kqOf (ringIop G C).merges (ringIop G C).rounds (max 2560 96) (max 2560 96))
          (maxError (ringIopSound G C).error)
          (((ringTranscript G C).setting 32 (ringMergeBounds C hmsg)).model.niJointSimulatorProg
            ((ringTranscript G C).setting 32 (ringMergeBounds C hmsg)).layout
            ((ringTranscript G C).setting 32 (ringMergeBounds C hmsg)).viewEncoder.toViewRead
            (max 2560 96) id
            (RealizedProgram.ProofSystem.IOP.simulator
              (C.fieldIopWithSimData (forkLowering C) (Ring.stmtOf (G := G))
                (Ring.ringOk (G := G)))) T).q t Q +
        SPBCS.knowledgeError (ringTranscript G C).k
          (Configurations.fsExtraBytes + (ringTranscript G C).maxGrant)
          (kqOf (ringIop G C).merges (ringIop G C).rounds (max 2560 96) (max 2560 96))
          (t + Q * (convertedScheme G C hmsg).q +
            kqOf (ringIop G C).merges (ringIop G C).rounds (max 2560 96) (max 2560 96))
          ((ringTranscript G C).setting 32 (ringMergeBounds C hmsg)).model.senc.digestsPerInput
          (ringIop G C).merges.nJ (maxError (ringIopSound G C).error) +
        2 * Q * εc :=
  StmtVerifiesRing.insiderForgeProb_le_zk (ringHonest G C) (ringMergeBounds C hmsg)
    (ringProofFormat C hmsg) _ (show 0 < (ringTranscript G C).k from Nat.succ_pos 31)
    (ringHonest_errorBound G C) (ringIopSound G C)
    (falconBaseSigner_oracleFree G _) (falconBaseSigner_pubOfCoins G _ hG)
    (falconBaseSigner_refusalOfCoins G _) hcorr
    (Falcon512.Ring.ringVerifies_stmt_injective G _ _ _ program interp fun _ =>
      Function.injective_id)
    (Falcon512.Ring.not_mem_ringHonestRelOf_nil G _ program interp) T A Q

end GordieHowe.Falcon512.Ring.Carrier.ROMParams
