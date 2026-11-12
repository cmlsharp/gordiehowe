-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Anonymity
public import GordieHowe.Applications.Ring.Completeness
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# The hypotheses of the plan-level theorem

- `ProgramHypotheses`: the hypotheses of the plan-level theorem in the series–parallel order (the
  paper's Theorem 5.2) at a proof system with forked domain proofs, and the objects they give
  (`ProgramHypotheses.iop`, `iopSound`, `roundError`, `simData`, `honestIOP`, `errorBound`).
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM Quantum RealizedProgram RealizedProgram.ProofSystem
open scoped NNReal ENNReal

variable {Pl : Export.Plan} {ir : RealizedProgram} {I : RealizedProgram.Interp}
  {B : ir.ProofSystem Pl I}

/-- **The hypotheses of the plan-level theorem in the series–parallel order** (the paper's
Theorem 5.2, `thm:backend`; `FieldBranches.causal_rbr_knowledge_soundness`,
`FieldBranches.completeness`, `FieldBranches.hvzk`, and the end-to-end theorem
`FieldBranches.e2eWith`) at the proof system `B` with forked domain proofs `F`, for the relation
`rel` with the projection `proj`, and the honest inputs `relH` at completeness error `errc`: the
source protocol `Π_P₀` is round-by-round knowledge sound with errors that vanish at `γ_end`, the
honest prover is complete with error `errc` (`HonestCore.Complete`, `def:o-guarantees` (1)), the
forked domain proofs are sound, with the domains' honest provers and simulators, under the trust
base (`CircuitsEnforce`, `CircuitsAccept`). -/
structure ProgramHypotheses (F : B.FieldBranches) {W : Type} (rel : Set (ir.Valuation I × W))
    (proj : ir.Valuation I → ir.Assignment I → W) {Inp : Type}
    (relH : Set (ir.Valuation I × Inp)) (errc : ℝ≥0) where
  /-- The forked domain proofs are sound. -/
  forkSound : F.Sound
  /-- The state function of the source protocol. -/
  stateFn : KnowledgeStateFunction (ir.sourceVerifier I)
  /-- The round errors of the source protocol. -/
  sourceError : (ir.sourceSpec I).ChallengeIdx → ℝ≥0
  /-- The source protocol is round-by-round knowledge sound for `rel`. -/
  source_rbr : RBRKnowledgeSound rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) stateFn
    sourceError
  /-- Its errors vanish at `γ_end`. -/
  sourceError_final : ∀ i, ir.rounds.get i.1 = .final → sourceError i = 0
  /-- The domains' simulators. -/
  domainSims : B.DomainSims
  /-- The domains' honest provers. -/
  honestDomains : B.HonestDomains domainSims
  /-- The forked domains' simulators. -/
  forkSims : F.ForkSims
  /-- The forked domains' honest provers. -/
  forkHonest : ∀ d, F.ForkDomainHonest d (honestDomains d).In (honestDomains d).dom (forkSims d)
  /-- The honest prover. -/
  honest : ir.HonestCore I relH
  /-- The honest prover is complete with error `errc`. -/
  complete : honest.Complete fun _ => errc

namespace ProgramHypotheses

variable {F : B.FieldBranches} {W : Type} {rel : Set (ir.Valuation I × W)}
  {proj : ir.Valuation I → ir.Assignment I → W} {Inp : Type} {relH : Set (ir.Valuation I × Inp)}
  {errc : ℝ≥0} (G : ProgramHypotheses F rel proj relH errc)

/-- The lowering of the soundness theorem (`ProofSystem.lowering`). -/
abbrev lowering :=
  B.lowering ⟨_, G.source_rbr, G.sourceError_final⟩

/-- **The multi-circuit IOP with forked domains of the soundness theorem**
(`FieldBranches.soundIOP`). -/
abbrev iop : RealizedProgram.ProofSystem.IOP (ir.Valuation I) (ir.Valuation I → W) (relOf rel) :=
  F.soundIOP G.source_rbr G.sourceError_final

/-- Its soundness (`FieldBranches.soundIOPSound`). -/
noncomputable abbrev iopSound : G.iop.Sound :=
  F.soundIOPSound G.forkSound G.source_rbr G.sourceError_final

/-- **The round errors of the program in the series–parallel order** (`IOP.Sound.error`): the
errors of Theorem 5.2's causal round-by-round knowledge soundness
(`FieldBranches.causal_rbr_knowledge_soundness`), every challenge with its own error. -/
noncomputable abbrev roundError := G.iopSound.error

/-- The simulator data of the soundness IOP (`FieldBranches.simDataAt`). -/
abbrev simData : G.iop.SimData := F.simDataAt G.lowering G.forkSims

/-- The honest prover of the soundness IOP (`FieldBranches.honestAt`). -/
abbrev honestIOP : G.iop.Honest G.simData Inp relH :=
  F.honestAt G.lowering G.honestDomains G.forkHonest G.honest

/-- The completeness events of the honest prover have together probability at most `errc`. -/
theorem errorBound : G.honestIOP.app.ErrorBound fun _ => errc :=
  F.errorBound_honestAt G.lowering G.honestDomains G.forkHonest G.honest G.complete

end ProgramHypotheses

end GordieHowe.Ring
