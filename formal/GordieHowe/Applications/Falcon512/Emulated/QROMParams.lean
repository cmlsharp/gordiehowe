-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Emulated.QROMParams.HonestStrategy
public import GordieHowe.Applications.Falcon512.Emulated.QROMParams.Relations
public import GordieHowe.Generated.Falcon512.Emulated.QROMParams.Figures
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap
public import GordieHowe.Applications.Configuration
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `Falcon512.Emulated.QROMParams` under spBCS

The emulated Falcon-512 proof of possession at the QROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`): the record `configuration` (the IOP with forked domains
`forkIop`, its transcript `forkTranscript`, `48`-byte Fiat–Shamir salts, the Falcon-512
proof-of-possession relation at the key `keyWitRel` with the witness read at the key's statement
values, the honest prover, the honest strategy `honestStrategy`, and the figures), its facts
`configurationFacts`, and the instances of the templates of the families `Common`,
`GordieHowe.Configuration.ZeroKnowledgeQROM`, `GordieHowe.Configuration.AdaptiveCompleteness` and
`GordieHowe.Configuration.PaperRelation`.

The figures: at most `2092` rounds, every round's load within `2^-2650`, trees of at most `4069`
leaves, `329` queried leaves, `8466` verifier queries (`2 · 2092 + 5 + 329 · 13`), round errors at
most `16484193 / 2^260`, `4188` digests per input (`2 · 2092 + 3 + 1`), the query caps `2^100`
(QROM) and `2^64` (ROM), `7141` positions (`4069 + 3072`) and `48`-byte digests.

The honest strategy (`honestStrategy`, `GordieHowe/Applications/Falcon512/Emulated/QROMParams/HonestStrategy.lean`):
`GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` at the execution of the source
program (`sourceExecution`), with no completeness event (`δ = 0`), on the honest inputs
`Native.HonestIn` (a valid Falcon-512 honest input with a message of at most `32` bytes, at its
key).

No statement has a compiler-trust hypothesis: the configuration's definitions are generic over the
program's proof systems (`ProofSystems`), and its statements are instantiated at `proofSystem`,
whose sources enforce the circuits' entries and accept the honest inputs by the certificates
(`GordieHowe/Applications/Falcon512/Emulated/QROMParams/Certified.lean`).
-/

namespace GordieHowe.Falcon512.Emulated.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Configuration
open Generated.Falcon512.Emulated.QROMParams.Program (program)
open Generated.Falcon512.Emulated.QROMParams (interp ready ProofSystems figures figuresOk
  numbers branchName branchName_le fieldBytes
  msgB_le samplerReaders chalLoadMax chalLoad_le
  grantMax sourceErrors fieldCard loadsOk)
open scoped NNReal ENNReal

/-! ## The multi-circuit IOP with forked domains -/

variable (C : ProofSystems)

/-- The lowering of the soundness theorem on the generic per-field domain proofs
(`RealizedProgram.ProofSystem.lowering`). -/
abbrev forkLowering :=
  (C.withFieldProofs ready).lowering ⟨_, source_rbr_knowledge_soundness, sourceError_final⟩

/-- **`Falcon512.Emulated.QROMParams` as a multi-circuit IOP with forked domains at the key**: the generic
per-field domain proofs (`RealizedProgram.ProofSystem.fieldIop`) with the proof system's application phase at the
frontend's round-by-round knowledge soundness (`source_rbr_knowledge_soundness`), the statement read as the key's
statement values (`stmtOf`). -/
abbrev forkIop : RealizedProgram.ProofSystem.IOP PublicKey (program.Valuation interp → VarWitness)
    keyRel :=
  C.fieldIop ready (forkLowering C) stmtOf

/-- The soundness data of `forkIop` (`RealizedProgram.ProofSystem.FieldBranches.soundIOPSound`, `RealizedProgram.ProofSystem.IOP.Sound.comap`). -/
noncomputable abbrev forkIopSound : (forkIop C).Sound :=
  ((C.fieldBranches ready).soundIOPSound (C.fieldBranchesSound ready) source_rbr_knowledge_soundness
    sourceError_final).comap stmtOf

/-- **The C++ series–parallel transcript of `Falcon512.Emulated.QROMParams`** (`RealizedProgram.ProofSystem.fieldForkTranscript`): the
label `label`, `figures.k`-byte digests (SHA-384), the key writes (`falconKeyCodec`), every branch named by its
domain's field (`branchName`), the phases' codecs (`RealizedProgram.appWrites` at `fieldBytes`) and readers
(`RealizedProgram.appReaders` at `samplerReaders`), every domain's at `numbers`. The largest grant of a round is `grantMax`. -/
abbrev forkTranscript : ProofSystemTranscript (forkIop C) :=
  C.fieldForkTranscript ready (forkLowering C) stmtOf numbers.cod
    (numbers.fits C.enforce) label figures.k
    falconKeyCodec (fun a => branchName a.1) (program.appWrites fieldBytes msgB_le)
    (program.appReaders samplerReaders (fun _ => chalLoadMax) chalLoad_le) grantMax

/-- **The facts the setting with merges is built from**: the transcript's
(`RealizedProgram.ProgramFigures.Check.transcript_bounds`: the statement's writes, the label and the
branch names) and `48`-byte salts. -/
theorem transcriptMergeBounds : (forkTranscript C).MergeBounds 48 :=
  ⟨figuresOk.transcript_bounds
    (fun pk => by
      change (falconKeyWrites pk).length ≤ _
      rw [falconKeyWrites_length]
      norm_num)
    (Nat.le_of_ble_eq_true rfl) (fun a => branchName_le a.1), by norm_num⟩

/-- **The source challenges' errors are within their fractions** (`sourceErrors`). -/
theorem sampleEps_le (j : ℕ) (_ : program.IsSourceChal j) :
    (selectEps (FH := RealizedProgram.gf256)) j ≤ ((sourceErrors j).1 : ℝ≥0) / (sourceErrors j).2 := by
  unfold selectEps
  simp only [sourceErrors]
  split_ifs
  · show (717 : ℝ≥0) / 2 ^ 256 ≤ _
    norm_num
  · exact zero_le'

/-- **The largest round error of the series–parallel composite** is at most
`figures.errorMax / 2^figures.errorExp` (`RealizedProgram.ProofSystem.fieldForkError_le`): every
domain's round charges and every phase's error (`RealizedProgram.ProgramFigures.Check.fieldRoundsLe`,
`RealizedProgram.ProgramFigures.Check.phaseError_le`). -/
theorem maxRoundError_le :
    maxError (forkIopSound C).error ≤ (figures.errorMax : ℝ≥0) / 2 ^ figures.errorExp :=
  maxError_le_iff.2 (C.fieldForkError_le ready stmtOf source_rbr_knowledge_soundness
    sourceError_final (figuresOk.fieldRoundsLe fieldCard)
    (fun _ => figuresOk.phaseError_le fieldCard (selectEps (FH := RealizedProgram.gf256)) sampleEps_le _))

/-! ## The configuration -/

/-- **`Falcon512.Emulated.QROMParams` as a configuration under spBCS** (module docstring).
The honest prover at a strategy `H`: the proof system's phased honest prover and every forked domain's honest
prover on the generic per-field domain proofs (`RealizedProgram.ProofSystem.FieldBranches.honestAt`, `RealizedProgram.ProofSystem.fieldHonestDomains`,
`RealizedProgram.ProofSystem.fieldForkHonestDomains`) read through the key's statement values
(`RealizedProgram.ProofSystem.IOP.Honest.comap`); its completeness error is the strategy's summed completeness errors
(`err`). -/
noncomputable def configuration : Configuration where
  ProofSystem := ProofSystems
  Stmt := PublicKey
  Wit := program.Valuation interp → VarWitness
  rel := keyRel
  iop := forkIop
  sound := forkIopSound
  T := forkTranscript
  kS := 48
  Wit' := VarWitness
  rel' := keyWitRel
  g s w := w (stmtOf s)
  Val := program.Valuation interp
  Strategy _ relH := program.HonestStrategy interp relH
  hrel := keyHonestRel
  sim C := C.fieldIopSimData (forkLowering C) stmtOf
  honest C _ _ H := C.fieldIopHonest (forkLowering C) stmtOf H.toHonestCore
  err H := ∑ k, H.δ k
  HonestIn := Native.HonestIn
  relH := relH program RealizedProgram.gf256 RealizedProgram.gold4
  strategy := honestStrategy
  keyStmtOf y := y.y.pk
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
(`GordieHowe.Generated.Falcon512.Emulated.QROMParams.figuresOk`: `RealizedProgram.ProgramFigures.Check.figures`,
`RealizedProgram.ProgramFigures.Check.loads`, `maxRoundError_le`), the setting's facts
(`transcriptMergeBounds`), the end-to-end theorem at the configuration's IOP
(`RealizedProgram.ProofSystem.FieldBranches.e2e_knowledge`, `RealizedProgram.ProofSystem.FieldBranches.e2e`, at the witness
map `mem_keyWitRel` and the domains' generic honest provers) and the honest strategy's
(`honestStrategy_delta`). -/
theorem configurationFacts : configuration.Facts where
  hb := transcriptMergeBounds
  knowledge C _ hkq := (C.fieldBranches ready).e2e_knowledge (C.fieldBranchesSound ready) source_rbr_knowledge_soundness
    sourceError_final stmtOf (forkTranscript C) 48 (transcriptMergeBounds C)
    (fun _ _ h => mem_keyWitRel h) hkq
  e2e C _ _ H _ hkq hf := (C.fieldBranches ready).e2e (C.fieldBranchesSound ready) source_rbr_knowledge_soundness
    sourceError_final stmtOf (forkTranscript C) 48 (transcriptMergeBounds C)
    (fun _ _ h => mem_keyWitRel h) hkq hf (C.fieldHonestDomains ready)
    (C.fieldForkHonestDomains ready) H.toHonestCore
    H.complete
  rounds_le C := (figuresOk.figures (B := C) (Lw := forkLowering C) (f := stmtOf)).rounds_le
  loads C := figuresOk.loads loadsOk (B := C) (Lw := forkLowering C) (f := stmtOf)
  loadsGranted C := figuresOk.loadsGranted (B := C) (Lw := forkLowering C) (f := stmtOf)
  leaves_le C := (figuresOk.figures (B := C) (Lw := forkLowering C) (f := stmtOf)).leaves_le
  queries_le C := (figuresOk.figures (B := C) (Lw := forkLowering C) (f := stmtOf)).queries_le
  kq_ge C := (figuresOk.figures (B := C) (Lw := forkLowering C) (f := stmtOf)).kq_ge
  kq_le := figuresOk.kq_le
  error_le := maxRoundError_le
  digests_le C := (figuresOk.figures (B := C) (Lw := forkLowering C) (f := stmtOf)).digests_le
  pos_eq C := (figuresOk.figures (B := C) (Lw := forkLowering C) (f := stmtOf)).pos_eq
  k_eq _ := rfl
  exact := honestStrategy_delta
  keyStmtOf_mem _ := rfl

/-- **The honest inputs of the supported pairs of the paper's relation**
(`Configuration.HonestOf` at `Falcon512.Native.keySupportedRel`: the pairs of `keyWitRel` whose
`HashToPoint` succeeds within the H circuit's `717` samples, `Falcon512.PoP.relSupported`): every
such pair has the honest input `Native.HonestIn.ofRel` at its key. -/
def honestOfRel : configuration.HonestOf where
  rel := Native.keySupportedRel
  rel_subset _ h := h.1
  honestOf p hp := Native.HonestIn.ofRel p.1 p.2 hp
  keyStmtOf_honestOf _ _ := rfl

instantiate_config GordieHowe.Falcon512.Emulated.QROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeQROM,
    GordieHowe.Configuration.AdaptiveCompleteness,
    GordieHowe.Configuration.PaperRelation] configuration
    configurationFacts honestOfRel at proofSystem

end GordieHowe.Falcon512.Emulated.QROMParams
