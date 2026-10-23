-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.HonestFacts
public import GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Completion
public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.Transcript
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
(`2 · 1038 + 3 + 127 · 13`), round errors at most `errorMax / 2^260`, `2080` digests per input
(`2 · 1038 + 3 + 1`), the query caps `2^100` (QROM) and `2^64` (ROM), `3258` positions and
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

All statements hold under the compiler trust (`CircuitsEnforce`, and `CircuitsAccept` for the
honest prover).
-/

namespace GordieHowe.Falcon512.Ring.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring GordieHowe.Configuration
open Generated.Falcon512.Ring.Native.QROMParams.Program (program)
open Native (Signer CoreWit scheme)
open Ring (RingIn relH)
open scoped NNReal ENNReal

variable {G : Signer 32}

/-! ## The honest strategy -/

/-- **The ready data of the honest strategy of `Falcon512.Ring.Native.QROMParams`** (`RealizedProgram.CompletionReady`): the nodes
containing `1` (`Ring.oneNodes`), the program's validity, the interpretation's registry, integer
readings and MAC model, and the checks (`GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Completion.completionOk`). -/
def completionReady : program.CompletionReady interpQROM (RealizedProgram.primeNodesOf Generated.Falcon512.Ring.Native.QROMParams.Plan.plan program)
    Generated.Falcon512.Ring.Native.QROMParams.Cert.gens Generated.Falcon512.Ring.Native.QROMParams.Cert.cderivs where
  nodes := Generated.Falcon512.Ring.Native.QROMParams.Honest.nodes
  oneNodes := Ring.oneNodes
  wf := Generated.Falcon512.Ring.Native.QROMParams.Valid.wellFormed
  registered := interpModel.registered
  lawful := interpModel.lawful
  macModel := RealizedProgram.Interp.macModel_of_noTail (by decide +kernel)
  tables := Generated.Falcon512.Ring.Native.QROMParams.Realize.derivable.tables
  macsRealizable := Generated.Falcon512.Ring.Native.QROMParams.Realize.derivable.eventsOk
  sourceValid := sourceValid
  ok := Generated.Falcon512.Ring.Native.QROMParams.Completion.completionOk

set_option maxRecDepth 8192 in
/-- **The `kpriv` source values whose type no node states have checked types** (decided). -/
theorem kprivTyped : program.KprivTyped := by
  decide +kernel

/-- The bound values' subfield types contain `1`. -/
theorem boundOneMem : program.BoundOneMem interpQROM :=
  RealizedProgram.boundOneMem_of_natTypedIn Ring.oneNodes (by decide +kernel)

variable (G) in
/-- **The honest strategy of `Falcon512.Ring.Native.QROMParams`** (`RealizedProgram.HonestStrategy.ofCompletionReady` at the
execution `Ring.sourceExecution`): the honest values `Ring.honestVal` at the source values,
the lookup digits and the static histograms the realization adds, no late value, no completeness
event. -/
noncomputable def honestStrategy : program.HonestStrategy interpQROM (relH G program interpQROM) :=
  RealizedProgram.HonestStrategy.ofCompletionReady completionReady
    (Ring.sourceExecution program interpQROM _ interpModel.registered interpModel.lawful completionReady.facts.committed completionReady.facts.boundNoCopy kprivTyped
      boundOneMem (by decide +kernel) (by decide +kernel))

/-- The honest strategy's completeness errors are `0`. -/
theorem honestStrategy_delta : ∑ k, (honestStrategy G).δ k ≤ honestBound := by
  simp [honestStrategy, RealizedProgram.HonestStrategy.ofCompletionReady_δ, Ring.sourceExecution, Ring.sourceExecutionOf,
    honestBound]

/-- **An honest input's statement is an honest statement**: it passes the check and its program
statement is the input's. -/
theorem mem_ringHonestRel (y : RingIn G) : (y.x, y) ∈ ringHonestRel (relH G program interpQROM) :=
  ⟨y.ringOk_x, rfl⟩

/-! ## The facts of the figures -/

/- Generated data: the figures' checks read the generated program. -/
set_option maxRecDepth 8192

variable (C : Compiled)

variable (G) in
/-- **The facts the setting with merges is built from**: the transcript's (`forkTranscript_bounds`)
and `48`-byte salts. -/
theorem transcriptMergeBounds : (forkTranscript G C).MergeBounds 48 :=
  ⟨forkTranscript_bounds G C, by norm_num⟩

set_option maxRecDepth 8192 in
variable (G) in
/-- **The figures of `forkIop`** (`RealizedProgram.ProofSystem.fieldIopWith_figures`, decided): at most `1038` rounds,
trees of at most `3258` leaves, `127` queried leaves, `3730` verifier queries, `2080` digests
per input and `3258` positions. -/
theorem forkFigures : (forkIop G C).Figures 1038 3258 127 3730 2080 3258 :=
  (proofSystem C.src).fieldIopWith_figures (forkLowering C) Ring.stmtOf C.enforce
    Ring.ringOk (by decide +kernel)

/-! ## The configuration -/

variable (G) in
/-- **`Falcon512.Ring.Native.QROMParams` as a configuration under spBCS** at the signer `G`
(module docstring). The honest prover at a strategy `H`: the proof system's phased honest prover and the
forked domain's honest prover on the generic per-field domain proofs (`RealizedProgram.ProofSystem.FieldBranches.honestAt`,
`RealizedProgram.ProofSystem.fieldHonestDomains`, `RealizedProgram.ProofSystem.fieldForkHonestDomains`) read through the program statement
and checked (`RealizedProgram.ProofSystem.IOP.Honest.comapWith`); its completeness error is the strategy's summed
completeness errors (`err`). -/
noncomputable def configuration : Configuration where
  Compiled := Compiled
  Stmt := Ring.RStmt G
  Wit := program.Valuation interpQROM → CoreWit
  rel := ringStmtRel
  iop := forkIop G
  sound := forkIopSound G
  T := forkTranscript G
  kS := 48
  Wit' := RingWit (scheme G)
  rel' := Ring.ringRel64 G
  g x w := (w (Ring.stmtOf x)).withSalt (G := G) x.pub
  TA C := (proofSystem C.src).CircuitsAccept
  Val := program.Valuation interpQROM
  Strategy _ relH := program.HonestStrategy interpQROM relH
  hrel relH := ringHonestRel (G := G) relH
  sim C := (proofSystem C.src).fieldIopWithSimData (forkLowering C) Ring.stmtOf Ring.ringOk
  honest C TA _ _ H :=
    (proofSystem C.src).fieldIopWithHonest (forkLowering C) Ring.stmtOf Ring.ringOk TA H.toHonestCore
  err H := ∑ k, H.δ k
  HonestIn := RingIn G
  relH := relH G program interpQROM
  strategy := honestStrategy G
  keyStmtOf y := y.x
  inh := inferInstance
  rounds := 1038
  chernoff := 4260
  N := 3258
  nq := 127
  kq := 3730
  errorMax := errorMax
  errorExp := 260
  D := 2080
  qQ := 2 ^ 100
  qR := 2 ^ 64
  pos := 3258
  k := 48

variable (G) in
/-- **The facts of `mergeConfig G`**: the figures' bounds (`transcriptMergeBounds`, `forkLoadsGranted`,
every round at its own stream length, `maxRoundError_le`, `forkFigures`), the end-to-end theorem at
the configuration's IOP (`RealizedProgram.ProofSystem.FieldBranches.e2eWith_knowledge`, `RealizedProgram.ProofSystem.FieldBranches.e2eWith`, at
the witness map `mem_ringRel64` and the domains' generic honest provers) and the honest strategy's
(`honestStrategy_delta`, `mem_ringHonestRel`). -/
theorem configurationFacts : (configuration G).GrantedFacts where
  hb := transcriptMergeBounds G
  knowledge C _ hkq := ((proofSystem C.src).fieldBranches ready).e2eWith_knowledge ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness
    sourceError_final Ring.stmtOf Ring.ringOk (forkTranscript G C) 48
    (transcriptMergeBounds G C) (fun _ _ h => mem_ringRel64 h) hkq
  e2e C TA _ _ H _ hkq hf := ((proofSystem C.src).fieldBranches ready).e2eWith ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness
    sourceError_final Ring.stmtOf Ring.ringOk (forkTranscript G C) 48
    (transcriptMergeBounds G C) (fun _ _ h => mem_ringRel64 h) hkq hf TA
    ((proofSystem C.src).fieldHonestDomains ready)
    ((proofSystem C.src).fieldForkHonestDomains ready TA) H.toHonestCore
    H.complete
  rounds_le C := (forkFigures G C).rounds_le
  loadsGranted C := forkLoadsGranted G C
  leaves_le C := (forkFigures G C).leaves_le
  queries_le C := (forkFigures G C).queries_le
  kq_ge C := (forkFigures G C).kq_ge
  kq_le := show 3730 ≤ 2 ^ 16 by norm_num
  error_le := maxRoundError_le G
  digests_le C := (forkFigures G C).digests_le
  pos_eq C := (forkFigures G C).pos_eq
  k_eq _ := rfl
  exact := nonpos_iff_eq_zero.1 honestStrategy_delta
  keyStmtOf_mem := mem_ringHonestRel

instantiate_config GordieHowe.Falcon512.Ring.Native.QROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeQROM,
    GordieHowe.Configuration.AdaptiveCompleteness]
  renaming keyExtractor → ringKeyExtractor
  {G : Signer 32} => (configuration G) (configurationFacts G)

end GordieHowe.Falcon512.Ring.Native.QROMParams
