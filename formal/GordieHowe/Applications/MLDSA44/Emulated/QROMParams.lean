-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams.GadgetFacts
public import GordieHowe.ProofSystem.Program.HonestReady
public import GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Completion
public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams.Relations
public import GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Figures
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap
public import GordieHowe.Applications.Configuration
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `MLDSA44.Emulated.QROMParams` under spBCS

The emulated ML-DSA-44 proof of possession at the QROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`): the record `configuration` (the IOP with forked domains
`forkIop`, its transcript `forkTranscript`, `48`-byte Fiat–Shamir salts, the ML-DSA-44
proof-of-possession relation at the key `keyWitRel` with the witness read at the key's statement
values, the honest prover, the honest strategy `honestStrategy`, and the figures), its facts
`configurationFacts`, and the instances of the templates of the families `Common`, `Query` and `GordieHowe.Configuration.AdaptiveCompleteness`.

The figures: at most `2333` rounds, every round's load within `2^-940`, trees of at most `4069`
leaves, `303` queried leaves, `8609` verifier queries (`2 · 2333 + 4 + 303 · 13`), round errors at
most `13358901 / 2^260`, `4669` digests per input (`2 · 2333 + 2 + 1`), the query caps `2^100`
(QROM) and `2^64` (ROM), `7141` positions (`3072 + 4069`) and `48`-byte digests.

The realization step's derivations (`RealizedProgram.Derivable`) are checked at the declared
statement bounds (`RealizedProgram.declaredRanges`): `key.a`, value `56`, below `q = 8380417`, and
`key.t1`, value `57`, below `2^10`, which every key's statement satisfies (`stmtBounded_stmtOf`).

The honest strategy (`honestStrategy`): `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` at the execution of the
source program (`GordieHowe.MLDSA44.Emulated.sourceExecution`), with no completeness event (`δ = 0`), on the honest
inputs `GordieHowe.MLDSA44.HonestInput` (a valid ML-DSA-44 honest input with a message of at most `32`
bytes, at its key); the realization's facts and the honest roles come from the generated
checks (`completionReady`).

No statement has a compiler-trust hypothesis: the configuration's definitions are generic over the
program's proof systems (`ProofSystems`), and its statements are instantiated at `proofSystem`,
whose sources enforce the circuits' entries and accept the honest inputs by the certificates
(`GordieHowe/Applications/MLDSA44/Emulated/QROMParams/Certified.lean`).
-/

namespace GordieHowe.MLDSA44.Emulated.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Configuration
open Generated.MLDSA44.Emulated.QROMParams.Program (program)
open Generated.MLDSA44.Emulated.QROMParams (interp ready ProofSystems figures figuresOk numbers
  branchName branchName_le fieldBytes msgB_le
  samplerReaders chalLoadMax chalLoad_le grantMax
  sourceErrors fieldCard loadsOk)
open Generated.MLDSA44.Emulated.QROMParams.Facts (interpModel sourceValid)
open MLDSA44 (HonestInput)
open scoped NNReal ENNReal

/-! ## The honest strategy -/

/-- **The honest relation of `MLDSA44.Emulated.QROMParams`**: the statement is the input's key's. -/
abbrev relH : Set (program.Valuation interp × HonestInput) :=
  Emulated.relH program RealizedProgram.gold4 RealizedProgram.gf256

/-- **The ready data of the honest strategy of `MLDSA44.Emulated.QROMParams`**
(`RealizedProgram.CompletionReady.ofGenerated`): the honest nodes, which contain `1`
(`Emulated.oneNodes`), and the generated facts: validity, the interpretation's model, the
realizations, the source part, and the checks of the completeness certificate and the honest roles
(`GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Completion.completionOk`, `GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Completion.rolesOk`). -/
def completionReady : program.CompletionReady interp (Emulated.MldsaEmulatedHonest.PN (program := program))
    Generated.MLDSA44.Emulated.QROMParams.Structure.records
    Generated.MLDSA44.Emulated.QROMParams.Cert.gens Generated.MLDSA44.Emulated.QROMParams.Cert.cderivs :=
  .ofGenerated Emulated.oneNodes Generated.MLDSA44.Emulated.QROMParams.Valid.wellFormed interpModel
    Generated.MLDSA44.Emulated.QROMParams.Realize.derivable sourceValid Generated.MLDSA44.Emulated.QROMParams.Completion.completionOk
    Generated.MLDSA44.Emulated.QROMParams.Completion.rolesOk

/-- **The honest strategy of `MLDSA44.Emulated.QROMParams`** (`RealizedProgram.HonestStrategy.ofCompletionReady` at the execution
`Emulated.sourceExecution` at the program's honest roles `completionReady.roles`): the honest
valuation `Emulated.honestVal` read off by `execOf`, the generated late values, no completeness
event. -/
noncomputable def honestStrategy : program.HonestStrategy interp relH :=
  RealizedProgram.HonestStrategy.ofCompletionReady completionReady
    (Emulated.sourceExecution program RealizedProgram.gold4 RealizedProgram.gf256 completionReady.facts.committed
      completionReady.facts.boundNoCopy completionReady.roles completionReady.oneNodes
      interpModel.bitNodes Generated.MLDSA44.Emulated.QROMParams.Completion.noFieldForm)

/-- The honest strategy's completeness errors are `0`. -/
theorem honestStrategy_delta : ∑ k, honestStrategy.δ k ≤ honestBound := by
  rw [honestStrategy, RealizedProgram.HonestStrategy.ofCompletionReady_δ, Emulated.sourceExecution_δ]
  simp [honestBound]

/-! ## The multi-circuit IOP with forked domains -/

variable (C : ProofSystems)

/-- The lowering of the soundness theorem on the generic per-field domain proofs
(`RealizedProgram.ProofSystem.lowering`). -/
abbrev forkLowering :=
  (C.withFieldProofs ready).lowering ⟨_, source_rbr_knowledge_soundness, (sourceError_final sampleEps)⟩

/-- **`MLDSA44.Emulated.QROMParams` as a multi-circuit IOP with forked domains at the key**: the generic
per-field domain proofs (`RealizedProgram.ProofSystem.fieldIop`) with the proof system's application phase at the
frontend's round-by-round knowledge soundness (`source_rbr_knowledge_soundness`), the statement read as the key's
statement values (`stmtOf`). -/
abbrev forkIop : RealizedProgram.ProofSystem.IOP KeyStmt
    (program.Valuation interp → MLDSA44.VarWitness) keyRel :=
  C.fieldIop ready (forkLowering C) stmtOf

/-- The soundness data of `forkIop` (`RealizedProgram.ProofSystem.FieldBranches.soundIOPSound`, `RealizedProgram.ProofSystem.IOP.Sound.comap`). -/
noncomputable abbrev forkIopSound : (forkIop C).Sound :=
  ((C.fieldBranches ready).soundIOPSound (C.fieldBranchesSound ready) source_rbr_knowledge_soundness
    (sourceError_final sampleEps)).comap stmtOf

/-- **The C++ series–parallel transcript of `MLDSA44.Emulated.QROMParams`** (`RealizedProgram.ProofSystem.fieldForkTranscript`): the
label `label`, `figures.k`-byte digests (SHA-384), the key-and-context writes (`keyStmtCodec`), every
branch named by its domain's field (`branchName`), the phases' codecs (`RealizedProgram.appWrites` at
`fieldBytes`) and readers (`RealizedProgram.appReaders` at `samplerReaders`), every domain's at `numbers`. The largest grant of a round is `grantMax`. -/
abbrev forkTranscript : ProofSystemTranscript (forkIop C) :=
  C.fieldForkTranscript ready (forkLowering C) stmtOf numbers.cod
    (numbers.fits C.enforce) label figures.k
    keyStmtCodec (fun a => branchName a.1) (program.appWrites fieldBytes msgB_le)
    (program.appReaders samplerReaders (fun _ => chalLoadMax) chalLoad_le) grantMax

/-- **The facts the setting with merges is built from**: the transcript's
(`RealizedProgram.ProgramFigures.Check.transcript_bounds`: the statement's writes, the label and the
branch names) and `48`-byte salts. -/
theorem transcriptMergeBounds : (forkTranscript C).MergeBounds 48 :=
  ⟨figuresOk.transcript_bounds
    (fun x => by
      change ((MLDSA44.PoP.StatementWrites.keyContext 0).pre x.1).length ≤ _
      rw [MLDSA44.PoP.StatementWrites.keyContext_pre_length]
      norm_num)
    (Nat.le_of_ble_eq_true rfl) (fun a => branchName_le a.1), by norm_num⟩

/-- **The source challenges' errors are within their fractions** (`sourceErrors`). -/
theorem sampleEps_le (j : ℕ) (_ : program.IsSourceChal j) :
    sampleEps j ≤ ((sourceErrors j).1 : ℝ≥0) / (sourceErrors j).2 := by
  unfold sampleEps MLDSA44.sampleEpsOf
  simp only [sourceErrors]
  split_ifs <;> norm_num

/-- **The largest round error of the series–parallel composite** is at most
`figures.errorMax / 2^figures.errorExp` (`RealizedProgram.ProofSystem.fieldForkError_le`): every
domain's round charges and every phase's error (`RealizedProgram.ProgramFigures.Check.fieldRoundsLe`,
`RealizedProgram.ProgramFigures.Check.phaseError_le`). -/
theorem maxRoundError_le :
    maxError (forkIopSound C).error ≤ (figures.errorMax : ℝ≥0) / 2 ^ figures.errorExp :=
  maxError_le_iff.2 (C.fieldForkError_le ready stmtOf source_rbr_knowledge_soundness
    (sourceError_final sampleEps) (figuresOk.fieldRoundsLe fieldCard)
    (fun _ => figuresOk.phaseError_le fieldCard sampleEps sampleEps_le _))

/-! ## The configuration -/

/-- **`MLDSA44.Emulated.QROMParams` as a configuration under spBCS** (module docstring). The
honest prover at a strategy `H`: the proof system's phased honest prover and every forked domain's honest
prover on the generic per-field domain proofs (`RealizedProgram.ProofSystem.FieldBranches.honestAt`, `RealizedProgram.ProofSystem.fieldHonestDomains`,
`RealizedProgram.ProofSystem.fieldForkHonestDomains`) read through the key's statement values
(`RealizedProgram.ProofSystem.IOP.Honest.comap`); its completeness error is the strategy's summed completeness errors
(`err`). -/
noncomputable def configuration : Configuration where
  ProofSystem := ProofSystems
  Stmt := KeyStmt
  Wit := program.Valuation interp → MLDSA44.VarWitness
  rel := keyRel
  iop := forkIop
  sound := forkIopSound
  T := forkTranscript
  kS := 48
  Wit' := MLDSA44.VarWitness
  rel' := keyWitRel
  g s w := w (stmtOf s)
  Val := program.Valuation interp
  Strategy _ relH := program.HonestStrategy interp relH
  hrel := keyHonestRel
  sim C := C.fieldIopSimData (forkLowering C) stmtOf
  honest C _ _ H := C.fieldIopHonest (forkLowering C) stmtOf H.toHonestCore
  err H := ∑ k, H.δ k
  HonestIn := HonestInput
  relH := relH
  strategy := honestStrategy
  keyStmtOf := keyStmtOf
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
(`GordieHowe.Generated.MLDSA44.Emulated.QROMParams.figuresOk`: `RealizedProgram.ProgramFigures.Check.figures`,
`RealizedProgram.ProgramFigures.Check.loads`, `maxRoundError_le`), the setting's facts
(`transcriptMergeBounds`), the end-to-end theorem at the configuration's IOP
(`RealizedProgram.ProofSystem.FieldBranches.e2e_knowledge`, `RealizedProgram.ProofSystem.FieldBranches.e2e`, at the witness
map `mem_keyWitRel` and the domains' generic honest provers) and the honest strategy's
(`honestStrategy_delta`). -/
theorem configurationFacts : configuration.Facts where
  hb := transcriptMergeBounds
  knowledge C _ hkq := (C.fieldBranches ready).e2e_knowledge (C.fieldBranchesSound ready) source_rbr_knowledge_soundness
    (sourceError_final sampleEps) stmtOf (forkTranscript C) 48 (transcriptMergeBounds C)
    (fun _ _ h => mem_keyWitRel h) hkq
  e2e C _ _ H _ hkq hf := (C.fieldBranches ready).e2e (C.fieldBranchesSound ready) source_rbr_knowledge_soundness
    (sourceError_final sampleEps) stmtOf (forkTranscript C) 48 (transcriptMergeBounds C)
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
  exact := nonpos_iff_eq_zero.1 honestStrategy_delta
  keyStmtOf_mem y := stmtOf_eq (keyStmtOf y)

/-- **The honest inputs of the paper's relation** (`Configuration.HonestOf` at `keyWitRel`, the
paper's relation `MLDSA44.PoP.relUpTo 32` at the key): every pair has the honest input
`MLDSA44.HonestInput.ofRel` at its statement; no pair of the relation is excluded. -/
def honestOfRel : configuration.HonestOf where
  rel := keyWitRel
  rel_subset _ h := h
  honestOf p hp := MLDSA44.HonestInput.ofRel p.1.1 p.2 hp
  keyStmtOf_honestOf _ _ := rfl

instantiate_config GordieHowe.MLDSA44.Emulated.QROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeQROM,
    GordieHowe.Configuration.AdaptiveCompleteness,
    GordieHowe.Configuration.PaperRelation] configuration configurationFacts
    honestOfRel at proofSystem

end GordieHowe.MLDSA44.Emulated.QROMParams
