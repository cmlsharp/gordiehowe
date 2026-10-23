-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Native.ROMParams.HonestFacts
public import GordieHowe.Generated.Falcon512.Ring.Native.ROMParams.Completion
public import GordieHowe.Applications.Falcon512.Ring.Native.ROMParams.Transcript
public import GordieHowe.Applications.Configuration
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `Falcon512.Ring.Native.ROMParams` under spBCS

The native Falcon ring at the ROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`), at every signer `G`: the record `mergeConfig G` (the IOP with
forked domains `forkIop G`, its transcript `forkTranscript G`, `32`-byte Fiat–Shamir salts, the ring
signature relation `FalconRing.ringRel64 G` with the witness read at the statement's program
statement and the signature encoded with the statement's salt, the honest prover, the honest strategy
`honestStrategy G`, and the figures), its facts `mergeFacts G`, and the instances of the
templates of the families `Common`, `GordieHowe.Configuration.ZeroKnowledgeROM` and `GordieHowe.Configuration.AdaptiveCompleteness`, each abstracted over `G`. The extractor is
`ringKeyExtractor`.

The figures: at most `1080` rounds, every round's load within `2^-3600`, a tree of at most `1506`
leaves, `89` queried leaves, `3233` verifier queries (`2 · 1080 + 5 + 89 · 12`), round errors at
most `errorMax / 2^140`, `2166` digests per input (`2 · 1080 + 5 + 1`), the query caps `2^40` (QROM)
and `2^64` (ROM), `1506` positions and `32`-byte digests.

The honest strategy (`honestStrategy`): `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` at the native Falcon rings'
execution of the source program (`GordieHowe.Falcon512.Ring.sourceExecution`: the honest values of a ring statement and
a witness of the ring relation), with no completeness event (`δ = 0`), on the pairs of the ring
relation (`GordieHowe.Falcon512.Ring.RingIn`), at their statements; the realization's facts come from the
checks (`completionReady`).

All statements hold under the compiler trust (`CircuitsEnforce`, and `CircuitsAccept` for the
honest prover).
-/

namespace GordieHowe.Falcon512.Ring.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring GordieHowe.Configuration
open Generated.Falcon512.Ring.Native.ROMParams.Program (program)
open Native (Signer CoreWit scheme)
open Ring (RingIn relH)
open scoped NNReal ENNReal

variable {G : Signer 32}

/-! ## The honest strategy -/

/-- **The ready data of the honest strategy of `Falcon512.Ring.Native.ROMParams`** (`RealizedProgram.CompletionReady`): the nodes
containing `1` (`Ring.oneNodes`), the program's validity, the interpretation's registry, integer
readings and MAC model, and the checks (`GordieHowe.Generated.Falcon512.Ring.Native.ROMParams.Completion.completionOk`). -/
def completionReady : program.CompletionReady interpROM (RealizedProgram.primeNodesOf Generated.Falcon512.Ring.Native.ROMParams.Plan.plan program)
    Generated.Falcon512.Ring.Native.ROMParams.Cert.gens Generated.Falcon512.Ring.Native.ROMParams.Cert.cderivs where
  nodes := Generated.Falcon512.Ring.Native.ROMParams.Honest.nodes
  oneNodes := Ring.oneNodes
  wf := Generated.Falcon512.Ring.Native.ROMParams.Valid.wellFormed
  registered := interpModel.registered
  lawful := interpModel.lawful
  macModel := RealizedProgram.Interp.macModel_of_noTail (by decide +kernel)
  tables := Generated.Falcon512.Ring.Native.ROMParams.Realize.derivable.tables
  macsRealizable := Generated.Falcon512.Ring.Native.ROMParams.Realize.derivable.eventsOk
  sourceValid := sourceValid
  ok := Generated.Falcon512.Ring.Native.ROMParams.Completion.completionOk

set_option maxRecDepth 8192 in
/-- **The `kpriv` source values whose type no node states have checked types** (decided). -/
theorem kprivTyped : program.KprivTyped := by
  decide +kernel

/-- The bound values' subfield types contain `1`. -/
theorem boundOneMem : program.BoundOneMem interpROM :=
  RealizedProgram.boundOneMem_of_natTypedIn Ring.oneNodes (by decide +kernel)

variable (G) in
/-- **The honest strategy of `Falcon512.Ring.Native.ROMParams`** (`RealizedProgram.HonestStrategy.ofCompletionReady` at the
execution `Ring.sourceExecution`): the honest values `Ring.honestVal` at the source values,
the lookup digits and the static histograms the realization adds, no late value, no completeness
event. -/
noncomputable def honestStrategy : program.HonestStrategy interpROM (relH G program interpROM) :=
  RealizedProgram.HonestStrategy.ofCompletionReady completionReady
    (Ring.sourceExecution program interpROM _ interpModel.registered interpModel.lawful completionReady.facts.committed completionReady.facts.boundNoCopy kprivTyped
      boundOneMem (by decide +kernel) (by decide +kernel))

/-- The honest strategy's completeness errors are `0`. -/
theorem honestStrategy_delta : ∑ k, (honestStrategy G).δ k ≤ honestBound := by
  simp [honestStrategy, RealizedProgram.HonestStrategy.ofCompletionReady_δ, Ring.sourceExecution, Ring.sourceExecutionOf,
    honestBound]

/-- **An honest input's statement is an honest statement**: it passes the check and its program
statement is the input's. -/
theorem mem_ringHonestRel (y : RingIn G) : (y.x, y) ∈ ringHonestRel (relH G program interpROM) :=
  ⟨y.ringOk_x, rfl⟩

/-! ## The facts of the figures -/

/- Generated data: the figures' checks read the generated program. -/
set_option maxRecDepth 8192

variable (C : Compiled)

variable (G) in
/-- **The facts the setting with merges is built from**: the transcript's (`forkTranscript_bounds`)
and `32`-byte salts. -/
theorem transcriptMergeBounds : (forkTranscript G C).MergeBounds 32 :=
  ⟨forkTranscript_bounds G C, by norm_num⟩

set_option maxRecDepth 8192 in
variable (G) in
/-- **The figures of `forkIop`** (`RealizedProgram.ProofSystem.fieldIopWith_figures`, decided): at most `1080` rounds,
trees of at most `1506` leaves, `89` queried leaves, `3233` verifier queries, `2166` digests
per input and `1506` positions. -/
theorem forkFigures : (forkIop G C).Figures 1080 1506 89 3233 2166 1506 :=
  (proofSystem C.src).fieldIopWith_figures (forkLowering C) Ring.stmtOf C.enforce
    Ring.ringOk (by decide +kernel)

/-! ## The configuration -/

variable (G) in
/-- **`Falcon512.Ring.Native.ROMParams` as a configuration under spBCS** at the signer `G`
(module docstring). The honest prover at a strategy `H`: the proof system's phased honest prover and the
forked domain's honest prover on the generic per-field domain proofs (`RealizedProgram.ProofSystem.FieldBranches.honestAt`,
`RealizedProgram.ProofSystem.fieldHonestDomains`, `RealizedProgram.ProofSystem.fieldForkHonestDomains`) read through the program statement
and checked (`RealizedProgram.ProofSystem.IOP.Honest.comapWith`); its completeness error is the strategy's summed
completeness errors (`err`). -/
noncomputable def configuration : Configuration where
  Compiled := Compiled
  Stmt := Ring.RStmt G
  Wit := program.Valuation interpROM → CoreWit
  rel := ringStmtRel
  iop := forkIop G
  sound := forkIopSound G
  T := forkTranscript G
  kS := 32
  Wit' := RingWit (scheme G)
  rel' := Ring.ringRel64 G
  g x w := (w (Ring.stmtOf x)).withSalt (G := G) x.pub
  TA C := (proofSystem C.src).CircuitsAccept
  Val := program.Valuation interpROM
  Strategy _ relH := program.HonestStrategy interpROM relH
  hrel relH := ringHonestRel (G := G) relH
  sim C := (proofSystem C.src).fieldIopWithSimData (forkLowering C) Ring.stmtOf Ring.ringOk
  honest C TA _ _ H :=
    (proofSystem C.src).fieldIopWithHonest (forkLowering C) Ring.stmtOf Ring.ringOk TA H.toHonestCore
  err H := ∑ k, H.δ k
  HonestIn := RingIn G
  relH := relH G program interpROM
  strategy := honestStrategy G
  keyStmtOf y := y.x
  inh := inferInstance
  rounds := 1080
  chernoff := 3600
  N := 1506
  nq := 89
  kq := 3233
  errorMax := errorMax
  errorExp := 140
  D := 2166
  qQ := 2 ^ 40
  qR := 2 ^ 64
  pos := 1506
  k := 32

variable (G) in
/-- **The facts of `mergeConfig G`**: the figures' bounds (`transcriptMergeBounds`, `forkFigures`,
`forkLoads` at `good_A_at` and `good_phase_at`, `maxRoundError_le`, `forkFigures`), the end-to-end
theorem at the configuration's IOP (`RealizedProgram.ProofSystem.FieldBranches.e2eWith_knowledge`,
`RealizedProgram.ProofSystem.FieldBranches.e2eWith`, at the witness map `mem_ringRel64` and the domains' generic honest
sides) and the honest strategy's (`honestStrategy_delta`, `mem_ringHonestRel`). -/
theorem configurationFacts : (configuration G).Facts where
  hb := transcriptMergeBounds G
  knowledge C _ hkq := ((proofSystem C.src).fieldBranches ready).e2eWith_knowledge
    ((proofSystem C.src).fieldBranchesSound ready) C.enforce
    source_rbr_knowledge_soundness sourceError_final Ring.stmtOf Ring.ringOk (forkTranscript G C)
    32 (transcriptMergeBounds G C) (fun _ _ h => mem_ringRel64 h) hkq
  e2e C TA _ _ H _ hkq hf := ((proofSystem C.src).fieldBranches ready).e2eWith ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness
    sourceError_final Ring.stmtOf Ring.ringOk (forkTranscript G C) 32
    (transcriptMergeBounds G C) (fun _ _ h => mem_ringRel64 h) hkq hf TA
    ((proofSystem C.src).fieldHonestDomains ready)
    ((proofSystem C.src).fieldForkHonestDomains ready TA) H.toHonestCore
    H.complete
  rounds_le C := (forkFigures G C).rounds_le
  loads C := forkLoads G C (fun _ h => good_A_at h) fun _ h => good_phase_at h
  leaves_le C := (forkFigures G C).leaves_le
  queries_le C := (forkFigures G C).queries_le
  kq_ge C := (forkFigures G C).kq_ge
  kq_le := show 3233 ≤ 2 ^ 16 by norm_num
  error_le := maxRoundError_le G
  digests_le C := (forkFigures G C).digests_le
  pos_eq C := (forkFigures G C).pos_eq
  k_eq _ := rfl
  exact := nonpos_iff_eq_zero.1 honestStrategy_delta
  keyStmtOf_mem := mem_ringHonestRel

instantiate_config GordieHowe.Falcon512.Ring.Native.ROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeROM,
    GordieHowe.Configuration.AdaptiveCompleteness]
  renaming keyExtractor → ringKeyExtractor
  {G : Signer 32} => (configuration G) (configurationFacts G)

end GordieHowe.Falcon512.Ring.Native.ROMParams
