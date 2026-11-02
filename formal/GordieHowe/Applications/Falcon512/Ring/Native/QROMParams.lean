-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.GadgetFacts
public import GordieHowe.ProofSystem.Program.HonestReady
public import GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Completion
public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.Relations
public import GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Figures
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap
public import GordieHowe.Applications.Configuration
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `Falcon512.Ring.Native.QROMParams` under spBCS

The native Falcon ring at the QROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`), at every signer `G`: the record `mergeConfig G` (the IOP with
forked domains `forkIop G`, its transcript `forkTranscript G`, `48`-byte Fiat–Shamir salts, the ring
signature relation `FalconRing.ringRel64 G` with the witness read at the statement's program
statement and the signature encoded with the statement's salt, the honest prover, the honest strategy
`honestStrategy G`, and the figures), its facts `mergeFacts G` (with granted points: `GrantedFacts`), and the instances of the
templates of the families `Common`, `Query` and `GordieHowe.Configuration.AdaptiveCompleteness`, each abstracted over `G`. The extractor is
`ringKeyExtractor`.

The figures: at most `1038` rounds, every round's load within `2^-4260`, a tree of at most
`3258` leaves, `127` queried leaves, `3730` verifier queries
(`2 · 1038 + 3 + 127 · 13`), round errors at most `12734825 / 2^260`, `1042` digests per input
(`max 2 (1038 · 1) + 3 + 1`), the query caps `2^100` (QROM) and `2^64` (ROM), `3258` positions and
`48`-byte digests.

Domain `A`'s Ligero tableau (`RealizedProgram.Export.Plan.LigeroShapesValid`):
`(rate, t, block_enc) = (12, 127, 3799)` and `k = 271`, so `w = k − t = 144`; the `80 + 100 = 180`
subfield masks of its tree `F_q <4 F_q^4 <5 F_q^20` take two prefix rows (`⌈180 / w⌉`,
`tree_zk.h`'s `prefix_padded`).

The honest strategy (`honestStrategy`): `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` at the native Falcon rings'
execution of the source program (`GordieHowe.Falcon512.Ring.sourceExecution`: the honest values of a ring statement and
a witness of the ring relation), with no completeness event (`δ = 0`), on the pairs of the ring
relation (`GordieHowe.Falcon512.Ring.RingIn`), at their statements; the realization's facts come from the
checks (`completionReady`).

No statement has a compiler-trust hypothesis: the configuration's definitions are generic over the
program's proof systems (`ProofSystems`), and its statements are instantiated at `proofSystem`,
whose sources enforce the circuits' entries and accept the honest inputs by the certificates
(`GordieHowe/Applications/Falcon512/Ring/Native/QROMParams/Certified.lean`).
-/

namespace GordieHowe.Falcon512.Ring.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring GordieHowe.Configuration
open Generated.Falcon512.Ring.Native.QROMParams.Program (program)
open Generated.Falcon512.Ring.Native.QROMParams (interp ready ProofSystems figures figuresOk
  numbers branchName branchName_le fieldBytes
  msgB_le samplerReaders chalLoadMax chalLoad_le
  grantMax sourceErrors fieldCard)
open Generated.Falcon512.Ring.Native.QROMParams.Facts (interpModel sourceValid)
open Native (Signer CoreWit scheme)
open Ring (RingIn relH)
open scoped NNReal ENNReal

variable {G : Signer 32}

/-! ## The honest strategy -/

/-- **The ready data of the honest strategy of `Falcon512.Ring.Native.QROMParams`**
(`RealizedProgram.CompletionReady.ofGenerated`): the honest nodes, which contain `1`
(`Ring.oneNodes`), and the generated facts: validity, the interpretation's model, the
realizations, the source part, and the checks of the completeness certificate and the honest roles
(`GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Completion.completionOk`, `GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Completion.rolesOk`). -/
def completionReady : program.CompletionReady interp
    (RealizedProgram.primeNodesOf Generated.Falcon512.Ring.Native.QROMParams.Plan.plan program)
    Generated.Falcon512.Ring.Native.QROMParams.Structure.records
    Generated.Falcon512.Ring.Native.QROMParams.Cert.gens Generated.Falcon512.Ring.Native.QROMParams.Cert.cderivs :=
  .ofGenerated Ring.oneNodes Generated.Falcon512.Ring.Native.QROMParams.Valid.wellFormed interpModel Generated.Falcon512.Ring.Native.QROMParams.Realize.derivable sourceValid
    Generated.Falcon512.Ring.Native.QROMParams.Completion.completionOk Generated.Falcon512.Ring.Native.QROMParams.Completion.rolesOk

variable (G) in
/-- **The honest strategy of `Falcon512.Ring.Native.QROMParams`** (`RealizedProgram.HonestStrategy.ofCompletionReady` at the
execution `Ring.sourceExecution` at the program's honest roles `completionReady.roles`): the honest values `Ring.honestVal` at the source values,
the lookup digits and the static histograms the realization adds, no late value, no completeness
event. -/
noncomputable def honestStrategy : program.HonestStrategy interp (relH G program interp) :=
  RealizedProgram.HonestStrategy.ofCompletionReady completionReady
    (Ring.sourceExecution program interp _ interpModel.registered interpModel.lawful
      completionReady.facts.committed completionReady.facts.boundNoCopy completionReady.roles
      completionReady.oneNodes interpModel.bitNodes Generated.Falcon512.Ring.Native.QROMParams.Completion.noFieldForm)

/-- The honest strategy's completeness errors are `0`. -/
theorem honestStrategy_delta : ∑ k, (honestStrategy G).δ k ≤ honestBound := by
  rw [honestStrategy, RealizedProgram.HonestStrategy.ofCompletionReady_δ, Ring.sourceExecution_δ (I := interp)]
  simp [honestBound]

/-- **An honest input's statement is an honest statement**: it passes the check and its program
statement is the input's. -/
theorem mem_ringHonestRel (y : RingIn G) : (y.x, y) ∈ ringHonestRel (relH G program interp) :=
  ⟨y.ringOk_x, rfl⟩

/-! ## The multi-circuit IOP with forked domains -/

variable {G : Signer 32} (C : ProofSystems)

/-- The lowering of the soundness theorem on the generic per-field domain proofs
(`RealizedProgram.ProofSystem.lowering`). -/
abbrev forkLowering :=
  (C.withFieldProofs ready).lowering ⟨_, source_rbr_knowledge_soundness, sourceError_final⟩

variable (G) in
/-- **`Falcon512.Ring.Native.QROMParams` as a multi-circuit IOP with forked domains at the ring
statement**: the generic per-field domain proofs (`RealizedProgram.ProofSystem.fieldBranches`) with the proof system's
application phase at the frontend's round-by-round knowledge soundness (`source_rbr_knowledge_soundness`), the statement
read as its program statement and checked (`RealizedProgram.ProofSystem.IOP.comapWith stmtOf ringOk`). -/
abbrev forkIop : RealizedProgram.ProofSystem.IOP (Ring.RStmt G)
    (program.Valuation interp → CoreWit) ringStmtRel :=
  C.fieldIopWith ready (forkLowering C) Ring.stmtOf Ring.ringOk

variable (G) in
/-- The soundness data of `forkIop` (`RealizedProgram.ProofSystem.FieldBranches.soundIOPSound`, `RealizedProgram.ProofSystem.IOP.Sound.comapWith`). -/
noncomputable abbrev forkIopSound : (forkIop G C).Sound :=
  ((C.fieldBranches ready).soundIOPSound (C.fieldBranchesSound ready) source_rbr_knowledge_soundness sourceError_final).comapWith Ring.stmtOf Ring.ringOk

variable (G) in
/-- **The C++ series–parallel transcript of `Falcon512.Ring.Native.QROMParams`**
(`RealizedProgram.ProofSystem.fieldForkTranscriptWith`): the label, `figures.k`-byte digests (SHA-384), the ring statement's
writes, the branch name, the phase's codecs (`RealizedProgram.appWrites` at `fieldBytes`) and readers
(`RealizedProgram.appReaders` at `samplerReaders`), the domain's at `numbers`. The largest grant of a round is `grantMax`. -/
abbrev forkTranscript : ProofSystemTranscript (forkIop G C) :=
  C.fieldForkTranscriptWith ready (forkLowering C) Ring.stmtOf numbers.cod
    (numbers.fits C.enforce)
    Ring.ringOk Native.label figures.k (Native.stmtCodecN G 64)
    (fun a => branchName a.1) (program.appWrites fieldBytes msgB_le)
    (program.appReaders samplerReaders (fun _ => chalLoadMax) chalLoad_le) grantMax

variable (G) in
/-- **The facts the setting with merges is built from**: the transcript's
(`RealizedProgram.ProgramFigures.Check.transcriptWith_bounds`: the ring statement's writes, the
label and the branch name) and `48`-byte salts. -/
theorem transcriptMergeBounds : (forkTranscript G C).MergeBounds 48 :=
  ⟨figuresOk.transcriptWith_bounds Ring.ringOk (fun x => (Native.length_ser_stmtCodecN_le x).trans (by norm_num))
    (Nat.le_of_ble_eq_true rfl) (fun a => branchName_le a.1), by norm_num⟩

/-- **The source challenge's error is within its fraction** (`sourceErrors`). -/
theorem ringEps_le (j : ℕ) (_ : program.IsSourceChal j) :
    Ring.ringEps interp j ≤ ((sourceErrors j).1 : ℝ≥0) / (sourceErrors j).2 := by
  unfold Ring.ringEps
  simp only [sourceErrors]
  split_ifs
  · rw [show Fintype.card _ = 12289 ^ 20 from by convert falconNativeField20_card <;> rfl]
    norm_num
  · exact zero_le'

variable (G) in
/-- **The largest round error of the series–parallel composite** is at most
`figures.errorMax / 2^figures.errorExp` (`RealizedProgram.ProofSystem.fieldForkErrorWith_le`): the
domain's round charges and the phase's error (`RealizedProgram.ProgramFigures.Check.fieldRoundsLe`,
`RealizedProgram.ProgramFigures.Check.phaseError_le`). -/
theorem maxRoundError_le :
    maxError (forkIopSound G C).error ≤ (figures.errorMax : ℝ≥0) / 2 ^ figures.errorExp :=
  maxError_le_iff.2 (C.fieldForkErrorWith_le ready Ring.stmtOf source_rbr_knowledge_soundness
    sourceError_final (figuresOk.fieldRoundsLe fieldCard)
    (fun _ => figuresOk.phaseError_le fieldCard (Ring.ringEps interp) ringEps_le _))

/-! ## The configuration -/

variable (G) in
/-- **`Falcon512.Ring.Native.QROMParams` as a configuration under spBCS** at the signer `G`
(module docstring). The honest prover at a strategy `H`: the proof system's phased honest prover and the
forked domain's honest prover on the generic per-field domain proofs (`RealizedProgram.ProofSystem.FieldBranches.honestAt`,
`RealizedProgram.ProofSystem.fieldHonestDomains`, `RealizedProgram.ProofSystem.fieldForkHonestDomains`) read through the program statement
and checked (`RealizedProgram.ProofSystem.IOP.Honest.comapWith`); its completeness error is the strategy's summed
completeness errors (`err`). -/
noncomputable def configuration : Configuration where
  ProofSystem := ProofSystems
  Stmt := Ring.RStmt G
  Wit := program.Valuation interp → CoreWit
  rel := ringStmtRel
  iop := forkIop G
  sound := forkIopSound G
  T := forkTranscript G
  kS := 48
  Wit' := RingWit (scheme G)
  rel' := Ring.ringRel64 G
  g x w := (w (Ring.stmtOf x)).withSalt (G := G) x.pub
  Val := program.Valuation interp
  Strategy _ relH := program.HonestStrategy interp relH
  hrel relH := ringHonestRel (G := G) relH
  sim C := C.fieldIopWithSimData (forkLowering C) Ring.stmtOf Ring.ringOk
  honest C _ _ H :=
    C.fieldIopWithHonest (forkLowering C) Ring.stmtOf Ring.ringOk H.toHonestCore
  err H := ∑ k, H.δ k
  HonestIn := RingIn G
  relH := relH G program interp
  strategy := honestStrategy G
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

variable (G) in
/-- **The facts of `mergeConfig G`**: the figures' bounds, from the generated check
(`figuresOk`: `RealizedProgram.ProgramFigures.Check.figuresWith`,
`RealizedProgram.ProgramFigures.Check.loadsGrantedWith`, every round at its own stream length,
`maxRoundError_le`), the setting's facts (`transcriptMergeBounds`), the end-to-end theorem at
the configuration's IOP (`RealizedProgram.ProofSystem.FieldBranches.e2eWith_knowledge`, `RealizedProgram.ProofSystem.FieldBranches.e2eWith`, at
the witness map `mem_ringRel64` and the domains' generic honest provers) and the honest strategy's
(`honestStrategy_delta`, `mem_ringHonestRel`). -/
theorem configurationFacts : (configuration G).GrantedFacts where
  hb := transcriptMergeBounds G
  knowledge C _ hkq := (C.fieldBranches ready).e2eWith_knowledge (C.fieldBranchesSound ready) source_rbr_knowledge_soundness
    sourceError_final Ring.stmtOf Ring.ringOk (forkTranscript G C) 48
    (transcriptMergeBounds G C) (fun _ _ h => mem_ringRel64 h) hkq
  e2e C _ _ H _ hkq hf := (C.fieldBranches ready).e2eWith (C.fieldBranchesSound ready) source_rbr_knowledge_soundness
    sourceError_final Ring.stmtOf Ring.ringOk (forkTranscript G C) 48
    (transcriptMergeBounds G C) (fun _ _ h => mem_ringRel64 h) hkq hf
    (C.fieldHonestDomains ready)
    (C.fieldForkHonestDomains ready) H.toHonestCore
    H.complete
  rounds_le C := (figuresOk.figuresWith (B := C) (Lw := forkLowering C) (f := Ring.stmtOf) Ring.ringOk).rounds_le
  loadsGranted C := figuresOk.loadsGrantedWith (B := C) (Lw := forkLowering C) (f := Ring.stmtOf)
    Ring.ringOk
  leaves_le C := (figuresOk.figuresWith (B := C) (Lw := forkLowering C) (f := Ring.stmtOf) Ring.ringOk).leaves_le
  queries_le C := (figuresOk.figuresWith (B := C) (Lw := forkLowering C) (f := Ring.stmtOf) Ring.ringOk).queries_le
  kq_ge C := (figuresOk.figuresWith (B := C) (Lw := forkLowering C) (f := Ring.stmtOf) Ring.ringOk).kq_ge
  kq_le := figuresOk.kq_le
  error_le := maxRoundError_le G
  digests_le C := (figuresOk.figuresWith (B := C) (Lw := forkLowering C) (f := Ring.stmtOf) Ring.ringOk).digests_le
  pos_eq C := (figuresOk.figuresWith (B := C) (Lw := forkLowering C) (f := Ring.stmtOf) Ring.ringOk).pos_eq
  k_eq _ := rfl
  exact := nonpos_iff_eq_zero.1 honestStrategy_delta
  keyStmtOf_mem := mem_ringHonestRel

instantiate_config GordieHowe.Falcon512.Ring.Native.QROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeQROM,
    GordieHowe.Configuration.AdaptiveCompleteness]
  renaming keyExtractor → ringKeyExtractor
  {G : Signer 32} => (configuration G) (configurationFacts G) at proofSystem

end GordieHowe.Falcon512.Ring.Native.QROMParams
