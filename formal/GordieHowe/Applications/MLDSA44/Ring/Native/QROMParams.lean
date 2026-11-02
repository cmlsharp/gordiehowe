-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.MLDSA44.Native.QROMParams.Interp
public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Completion
public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Interp
public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Facts.Model
public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Facts
public import GordieHowe.Applications.MLDSA44.Ring.Tableaux
public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Ready
public import GordieHowe.Applications.MLDSA44.Ring.Native.QROMParams.GadgetFacts
public import GordieHowe.ProofSystem.Program.HonestReady
public import GordieHowe.Applications.MLDSA44.Ring.Native.QROMParams.Relations
public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Figures
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap
public import GordieHowe.Applications.Configuration
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `MLDSA44.Ring.Native.QROMParams` under spBCS

The native ML-DSA-44 ring at the QROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`) at the converted base messages' length `34`
(`GordieHowe.MLDSA44.Ring.convertedMsg`: `0 ‖ 0 ‖ m` for a `32`-byte ring message): the record
`configuration` (the IOP with forked domains `ringIop 34`, its transcript `ringTranscript 34`,
`48`-byte Fiat–Shamir salts, the ring relation `GordieHowe.MLDSA44.Ring.ringRel64 34` with the
witness read at the statement's program statement (`ringWit`), the honest prover, the honest
strategy `honestStrategy 34`, and the figures), its facts `configurationFacts`, and the instances
of the templates of the families `Common`, `GordieHowe.Configuration.ZeroKnowledgeQROM` and
`GordieHowe.Configuration.AdaptiveCompleteness`. The extractor is `ringKeyExtractor`. The ring
signatures at every message length are in
`GordieHowe/Applications/MLDSA44/Ring/Native/QROMParams/RingScheme.lean`.

The figures: at most `2273` rounds, every round's load within `2^-990`, trees of at most `4069`
leaves, `273` queried leaves, `8099` verifier queries, round errors at most `13358901 / 2^260`,
`4549` digests per input, the query caps `2^100` (QROM) and `2^64` (ROM), `8005` positions and
`48`-byte digests.

* **The honest relation** (`ringHonestRel msgLen relH`): statements that pass the check and whose
  program statement is the strategy's; `mem_ringHonestRel`: an honest input's statement is an
  honest statement.

All statements hold under the compiler trust (`CircuitsEnforce`, and `CircuitsAccept` for the
honest prover).
-/

namespace GordieHowe.MLDSA44.Ring.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
  GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Configuration
open Generated.MLDSA44.Ring.Native.QROMParams.Program (program)
open Generated.MLDSA44.Ring.Native.QROMParams (interp ready ProofSystems figures figures_eq
  figuresOk numbers branchName branchName_le
  fieldBytes msgB_le samplerReaders chalLoadMax
  chalLoad_le grantMax sourceErrors fieldCard loadsOk)
open scoped NNReal ENNReal

/- Generated data: the figures' checks read the generated program. -/
set_option maxRecDepth 8192

/-! ## The honest strategy -/

section Honest

open Generated.MLDSA44.Ring.Native.QROMParams.Facts (interpModel sourceValid)
open RealizedProgram

/-- **The nodes of the program contain `1`.** -/
theorem oneNodes : OneNodes interp Generated.MLDSA44.Ring.Native.QROMParams.Honest.nodes := by
  intro p hp
  exact MLDSA44.Native.oneNodes (F0 := RealizedProgram.fq11) (FH := RealizedProgram.gf256) p
    (by simp only [Generated.MLDSA44.Ring.Native.QROMParams.Honest.nodes, List.mem_cons,
      List.not_mem_nil, or_false] at hp ⊢; tauto)

/-- **The ready data of the honest strategy of `MLDSA44.Ring.Native.QROMParams`**
(`RealizedProgram.CompletionReady.ofGenerated`): the honest nodes, which contain `1` (`oneNodes`),
and the generated facts: validity, the interpretation's model, the realizations, the source part,
and the checks of the completeness certificate and the honest roles
(`GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Completion.completionOk`, `GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Completion.rolesOk`). -/
def completionReady : program.CompletionReady interp
    (primeNodesOf Generated.MLDSA44.Ring.Native.QROMParams.Plan.plan program) Generated.MLDSA44.Ring.Native.QROMParams.Structure.records Generated.MLDSA44.Ring.Native.QROMParams.Cert.gens
    Generated.MLDSA44.Ring.Native.QROMParams.Cert.cderivs :=
  .ofGenerated oneNodes Generated.MLDSA44.Ring.Native.QROMParams.Valid.wellFormed interpModel Generated.MLDSA44.Ring.Native.QROMParams.Realize.derivable sourceValid
    Generated.MLDSA44.Ring.Native.QROMParams.Completion.completionOk Generated.MLDSA44.Ring.Native.QROMParams.Completion.rolesOk

variable (msgLen : ℕ)

/-- **The honest strategy of `MLDSA44.Ring.Native.QROMParams`**
(`RealizedProgram.HonestStrategy.ofCompletionReady` at the execution `Ring.Native.sourceExecution`
at the program's honest roles `completionReady.roles`): the honest values `Ring.Native.honestVal`
read off by `execOf`, the lookup digits and the static histograms the realization adds, no late
value, no completeness event. -/
noncomputable def honestStrategy :
    program.HonestStrategy interp (Native.relH (msgLen := msgLen) program RealizedProgram.fq11 RealizedProgram.gf256) :=
  RealizedProgram.HonestStrategy.ofCompletionReady completionReady
    (Native.sourceExecution program RealizedProgram.fq11 RealizedProgram.gf256 interpModel.registered interpModel.lawful
      completionReady.facts.committed completionReady.facts.boundNoCopy completionReady.roles
      completionReady.oneNodes interpModel.bitNodes Generated.MLDSA44.Ring.Native.QROMParams.Completion.noFieldForm)

/-- **The honest strategy's completeness errors are `0`.** -/
theorem honestStrategy_delta : ∑ k, (honestStrategy msgLen).δ k = 0 := by
  rw [honestStrategy, RealizedProgram.HonestStrategy.ofCompletionReady_δ, Native.sourceExecution_δ]
  simp

end Honest

/-! ## The honest relation -/

variable (msgLen : ℕ) in
/-- **The honest inputs at the ring statements of `msgLen`-byte message representatives**:
statements that pass the check (`ringOk`) and whose program statement (`Native.stmtOf`) is related
to the input by `relH`. -/
abbrev ringHonestRel {Inp : Type} (relH : Set (program.Valuation interp × Inp)) :
    Set (RStmt msgLen × Inp) :=
  {p | ringOk p.1 = true ∧ (Native.stmtOf (program := program) (I := interp) p.1, p.2) ∈ relH}

/-- **An honest input's statement is an honest statement**: it passes the check and its program
statement is the input's (`Native.relH`). -/
theorem mem_ringHonestRel {msgLen : ℕ} (y : RingIn msgLen) :
    (y.x, y) ∈ ringHonestRel msgLen
      (Native.relH (msgLen := msgLen) program RealizedProgram.fq11 RealizedProgram.gf256) :=
  ⟨y.ringOk_x, rfl⟩

/-- **A witness of the relation of the BCS transformation gives the ring relation at the read
witness** (`ringStmtRel_sound` at the checked statement). -/
theorem mem_ringRel64 {msgLen : ℕ} (x : RStmt msgLen) (f : program.Valuation interp → Native.RingW)
    (h : ringOk x = true ∧
      (Native.stmtOf (program := program) (I := interp) x, f) ∈
        RealizedProgram.ProofSystem.relOf
          (Native.rel (program := program) (F0 := RealizedProgram.fq11)
            (FH := RealizedProgram.gf256))) :
    (x, ringWit x f) ∈ ringRel64 msgLen :=
  ringStmtRel_sound x f h.1 h

/-! ## The multi-circuit IOP with forked domains -/

variable (msgLen : ℕ) (C : ProofSystems)

/-- The lowering of the soundness theorem on the generic per-field domain proofs
(`RealizedProgram.ProofSystem.lowering`). -/
abbrev ringLowering :=
  (C.withFieldProofs ready).lowering
    ⟨_, source_rbr_knowledge_soundness, sourceError_final sourceEps⟩

/-- **`MLDSA44.Ring.Native.QROMParams` as a multi-circuit IOP with forked domains at the ring
statements of `msgLen`-byte message representatives**: the generic per-field domain proofs
(`RealizedProgram.ProofSystem.fieldBranches`) with the proof system's application phase at the
frontend's round-by-round knowledge soundness (`source_rbr_knowledge_soundness`), the statement read
as its program statement and checked (`RealizedProgram.ProofSystem.IOP.comapWith Native.stmtOf
ringOk`). -/
abbrev ringIop : RealizedProgram.ProofSystem.IOP (RStmt msgLen)
    (program.Valuation interp → Native.RingW) (ringStmtRel msgLen) :=
  C.fieldIopWith ready (ringLowering C)
    (Native.stmtOf (program := program) (I := interp)) ringOk

/-- The soundness data of `ringIop` (`RealizedProgram.ProofSystem.FieldBranches.soundIOPSound`,
`RealizedProgram.ProofSystem.IOP.Sound.comapWith`). -/
noncomputable abbrev ringIopSound : (ringIop msgLen C).Sound :=
  ((C.fieldBranches ready).soundIOPSound
    (C.fieldBranchesSound ready) source_rbr_knowledge_soundness
    (sourceError_final sourceEps)).comapWith
      (Native.stmtOf (program := program) (I := interp) (len := msgLen)) ringOk

/-- **The C++ series–parallel transcript of `MLDSA44.Ring.Native.QROMParams`** at `msgLen`-byte
message representatives (`RealizedProgram.ProofSystem.fieldForkTranscriptWith`): the label
`labelNative`, `figures.k`-byte digests (SHA-384), the ring statement's writes (`stmtCodecN msgLen 64`),
every branch named by its domain's field (`branchName`), the phases' codecs
(`RealizedProgram.appWrites` at `fieldBytes`) and readers (`RealizedProgram.appReaders` at
`samplerReaders`), every domain's at `numbers`. The largest grant of a round is `grantMax`. -/
abbrev ringTranscript : ProofSystemTranscript (ringIop msgLen C) :=
  C.fieldForkTranscriptWith ready (ringLowering C)
    (Native.stmtOf (program := program) (I := interp)) numbers.cod (numbers.fits C.enforce)
    ringOk labelNative figures.k (stmtCodecN msgLen 64) (fun a => branchName a.1)
    (program.appWrites fieldBytes msgB_le)
    (program.appReaders samplerReaders (fun _ => chalLoadMax) chalLoad_le) grantMax

variable {msgLen} in
/-- **The facts the setting is built from** at message representatives of at most `2^19` bytes
(`hmsg`): the ring statement's writes within `2^20` bytes (`length_ser_stmtCodecN_le`), the
label, the digest length, the branch names and the figures of `numbers`
(`RealizedProgram.ProgramFigures.Check.transcriptWith_bounds`). -/
theorem ringTranscript_bounds (hmsg : msgLen ≤ 2 ^ 19) : (ringTranscript msgLen C).Bounds :=
  figuresOk.transcriptWith_bounds ringOk
    (fun x => (length_ser_stmtCodecN_le x).trans (by omega))
    (Nat.le_of_ble_eq_true rfl) (fun a => branchName_le a.1)

variable {msgLen} in
/-- **The setting's facts with `48`-byte salts** at message representatives of at most `2^19`
bytes. -/
theorem ringMergeBounds (hmsg : msgLen ≤ 2 ^ 19) : (ringTranscript msgLen C).MergeBounds 48 :=
  ⟨ringTranscript_bounds C hmsg, by norm_num⟩

/-- **The figures of `ringIop`** (`RealizedProgram.ProgramFigures.Check.figuresWith`, the generated figures): at
most `2273` rounds, trees of at most `4069` leaves, `273` queried leaves, `8099` verifier queries, `4549`
digests per input and `8005` positions. -/
theorem ringFigures : (ringIop msgLen C).Figures 2273 4069 273 8099 4549 8005 :=
  by simpa only [figures_eq] using figuresOk.figuresWith (B := C) (Lw := ringLowering C) ringOk

variable {msgLen} in
/-- **The proof format `max 4069 273`**: every tree has at most `4069` leaves and every query phase
opens at most `273` positions (`ringFigures`). -/
theorem ringProofFormat (hmsg : msgLen ≤ 2 ^ 19) :
    (ringTranscript msgLen C).ProofFormat 48 (ringMergeBounds C hmsg) (max 4069 273) :=
  ProofSystemTranscript.formatBounds (ringMergeBounds C hmsg)
    (fun d => ((ringFigures msgLen C).leaves_le d).trans (le_max_left _ _))
    fun ch => ((ringFigures msgLen C).queries_le ch).trans (le_max_right _ _)

/-- **The source challenges' errors are within their fractions** (`sourceErrors`). -/
theorem sourceEps_le (j : ℕ) (_ : program.IsSourceChal j) :
    sourceEps j ≤ ((sourceErrors j).1 : ℝ≥0) / (sourceErrors j).2 := by
  rcases j with _ | _ | _ | j
  · change ((5143 : ℕ) : ℝ≥0) / Fintype.card (interp 0).K ≤ _
    rw [show Fintype.card (interp 0).K = 8380417 ^ 11 from by convert mldsaNativeField11_card <;> rfl]
    simp only [sourceErrors, ↓reduceIte]
    norm_num [pGold]
  · change MLDSA44.sampleEpsOf 256 0 ≤ _
    norm_num [MLDSA44.sampleEpsOf, sourceErrors]
  · change MLDSA44.sampleEpsOf 256 1 ≤ _
    norm_num [MLDSA44.sampleEpsOf, sourceErrors]
  · change MLDSA44.sampleEpsOf 256 (j + 2) ≤ _
    simp [MLDSA44.sampleEpsOf]

/-- **The largest round error of the series–parallel composite** is at most
`figures.errorMax / 2^figures.errorExp` (`RealizedProgram.ProofSystem.fieldForkErrorWith_le`):
every domain's round charges and every phase's error
(`RealizedProgram.ProgramFigures.Check.fieldRoundsLe`,
`RealizedProgram.ProgramFigures.Check.phaseError_le`). -/
theorem maxRoundError_le :
    maxError (ringIopSound msgLen C).error ≤ (figures.errorMax : ℝ≥0) / 2 ^ figures.errorExp :=
  maxError_le_iff.2 (C.fieldForkErrorWith_le ready
    (Native.stmtOf (program := program) (I := interp)) source_rbr_knowledge_soundness
    (sourceError_final sourceEps) (figuresOk.fieldRoundsLe fieldCard)
    (fun _ => figuresOk.phaseError_le fieldCard sourceEps sourceEps_le _))

/-! ## The configuration -/

/-- The converted base messages' length `2 + 32` is within the setting's `2^19` bytes. -/
theorem msgLen_le : 2 + 32 ≤ 2 ^ 19 := by norm_num

/-- **`MLDSA44.Ring.Native.QROMParams` as a configuration under spBCS** at `34`-byte message
representatives (module docstring). The honest prover at a strategy `H`: the proof system's phased
honest prover and the forked domains' honest provers on the generic per-field domain proofs
(`RealizedProgram.ProofSystem.fieldIopWithHonest`), read through the program statement and
checked; its completeness error is the strategy's summed completeness errors (`err`). -/
noncomputable def configuration : Configuration where
  ProofSystem := ProofSystems
  Stmt := RStmt (2 + 32)
  Wit := program.Valuation interp → Native.RingW
  rel := ringStmtRel (2 + 32)
  iop := ringIop (2 + 32)
  sound := ringIopSound (2 + 32)
  T := ringTranscript (2 + 32)
  kS := 48
  Wit' := GordieHowe.Ring.RingWit (scheme (2 + 32))
  rel' := ringRel64 (2 + 32)
  g := ringWit
  Val := program.Valuation interp
  Strategy _ relH := program.HonestStrategy interp relH
  hrel relH := ringHonestRel (2 + 32) relH
  sim C := C.fieldIopWithSimData (ringLowering C)
    (Native.stmtOf (program := program) (I := interp) (len := 2 + 32)) ringOk
  honest C _ _ H :=
    C.fieldIopWithHonest (ringLowering C)
      (Native.stmtOf (program := program) (I := interp) (len := 2 + 32)) ringOk H.toHonestCore
  err H := ∑ k, H.δ k
  HonestIn := RingIn (2 + 32)
  relH := Native.relH (msgLen := 2 + 32) program RealizedProgram.fq11 RealizedProgram.gf256
  strategy := honestStrategy (2 + 32)
  keyStmtOf y := y.x
  inh := inferInstance
  rounds := figures.rounds
  chernoff := figures.chernoff
  N := figures.N
  nq := figures.nq
  kq := figures.kq
  errorMax := figures.errorMax
  errorExp := figures.errorExp
  D := figures.D
  qQ := 2 ^ 100
  qR := 2 ^ 64
  pos := figures.pos
  k := figures.k

/-- **The facts of `configuration`**: the figures' bounds, from the generated check
(`GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.figuresOk`: `RealizedProgram.ProgramFigures.Check.figuresWith`,
`RealizedProgram.ProgramFigures.Check.loadsWith`, `maxRoundError_le`), the setting's facts
(`ringMergeBounds`), the end-to-end theorem at the
configuration's IOP (`RealizedProgram.ProofSystem.FieldBranches.e2eWith_knowledge`,
`RealizedProgram.ProofSystem.FieldBranches.e2eWith`, at the witness map `mem_ringRel64` and the
domains' generic honest provers) and the honest strategy's (`honestStrategy_delta`,
`mem_ringHonestRel`). -/
theorem configurationFacts : configuration.Facts where
  hb C := ringMergeBounds C msgLen_le
  knowledge C _ hkq := (C.fieldBranches ready).e2eWith_knowledge
    (C.fieldBranchesSound ready) source_rbr_knowledge_soundness
    (sourceError_final sourceEps) (Native.stmtOf (program := program) (I := interp)) ringOk
    (ringTranscript (2 + 32) C) 48 (ringMergeBounds C msgLen_le) mem_ringRel64 hkq
  e2e C _ _ H _ hkq hf := (C.fieldBranches ready).e2eWith
    (C.fieldBranchesSound ready) source_rbr_knowledge_soundness
    (sourceError_final sourceEps) (Native.stmtOf (program := program) (I := interp)) ringOk
    (ringTranscript (2 + 32) C) 48 (ringMergeBounds C msgLen_le) mem_ringRel64 hkq hf
    (C.fieldHonestDomains ready)
    (C.fieldForkHonestDomains ready) H.toHonestCore H.complete
  rounds_le C := (figuresOk.figuresWith (B := C) (Lw := ringLowering C) ringOk).rounds_le
  loads C := figuresOk.loadsWith loadsOk (B := C) (Lw := ringLowering C) ringOk
  loadsGranted C := figuresOk.loadsGrantedWith (B := C) (Lw := ringLowering C) ringOk
  leaves_le C := (figuresOk.figuresWith (B := C) (Lw := ringLowering C) ringOk).leaves_le
  queries_le C := (figuresOk.figuresWith (B := C) (Lw := ringLowering C) ringOk).queries_le
  kq_ge C := (figuresOk.figuresWith (B := C) (Lw := ringLowering C) ringOk).kq_ge
  kq_le := figuresOk.kq_le
  error_le := maxRoundError_le (2 + 32)
  digests_le C := (figuresOk.figuresWith (B := C) (Lw := ringLowering C) ringOk).digests_le
  pos_eq C := (figuresOk.figuresWith (B := C) (Lw := ringLowering C) ringOk).pos_eq
  k_eq _ := rfl
  exact := honestStrategy_delta (2 + 32)
  keyStmtOf_mem := mem_ringHonestRel

instantiate_config GordieHowe.MLDSA44.Ring.Native.QROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeQROM,
    GordieHowe.Configuration.AdaptiveCompleteness]
  renaming keyExtractor → ringKeyExtractor
  configuration configurationFacts at proofSystem

end GordieHowe.MLDSA44.Ring.Native.QROMParams
