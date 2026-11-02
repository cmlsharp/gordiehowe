-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Certified
public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.Applications.Falcon512.Ring.Carrier.ROMParams.Facts

@[expose] public section

/-!
# GordieHowe: the theorem at the realized program for `Falcon512.Ring.Carrier.ROMParams`

The frontend's round-by-round knowledge soundness of `Π_P₀` at the Falcon ring relation
(`GordieHowe.Falcon512.Ring.rbr_carrier`: the relation `GordieHowe.Falcon512.Ring.rel` at the statement's ring and challenge, the
extractor `GordieHowe.Falcon512.Ring.proj`, the error `511/p^2` at `member.ring.gamma`), composed with the
proof system (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains of `proofSystem`),
and the proof system's completeness and honest-verifier zero knowledge
(`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.completeness`,
`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.hvzk`), each at the proof system `proofSystem` (`GordieHowe/Applications/Falcon512/Ring/Carrier/ROMParams/Certified.lean`).
-/

namespace GordieHowe.Falcon512.Ring.Carrier.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP
open Generated.Falcon512.Ring.Carrier.ROMParams.Program (program)
open Generated.Falcon512.Ring.Carrier.ROMParams (interp ready ProofSystems)
open scoped NNReal

/-- **The selections' error** (`RealizedProgram.SelSound`): the one selection the product form's
kernel reads is the membership's, whose event implies the membership's event
(`Ring.selSound_carrier`; the selections, the reads and the selection error decided). -/
theorem selSound : program.SelSound interp :=
  Ring.selSound_carrier (by decide +kernel) Generated.Falcon512.Ring.Carrier.ROMParams.Valid.wellFormed
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The proof system of `Falcon512.Ring.Carrier.ROMParams`**
(`GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.proofSystemOf`): the generic per-field proof
system at the certificates' sources, whose circuits enforce their entries and accept the honest
inputs by the certificates, at the selections' soundness `selSound`. -/
abbrev proofSystem : ProofSystems :=
  Generated.Falcon512.Ring.Carrier.ROMParams.proofSystemOf selSound

/-- **Round-by-round knowledge soundness of `Π_P₀` for `Falcon512.Ring.Carrier.ROMParams`** at the ring
relation `Ring.rel`, the extractor `Ring.extractor` and the errors `511/p^2` at
`member.ring.gamma`, `0` elsewhere. -/
theorem source_rbr_knowledge_soundness :
    rbrKnowledgeSoundness Ring.rel (program.sourceVerifier interp) Ring.extractor
      (program.eventState interp Ring.rel Ring.proj Ring.ringEvent
        Ring.ringEvent_use Ring.sound_carrier)
      (program.roundError interp (Ring.ringEps interp)) :=
  Ring.rbr_carrier

/-- **`Π_P₀`'s round errors vanish at `γ_end`.** -/
theorem sourceError_final :
    ∀ i, program.rounds.get i.1 = .final →
      program.roundError interp (Ring.ringEps interp) i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

/-- **Soundness of `Falcon512.Ring.Carrier.ROMParams` at the realized program, in the series–parallel order of
`prot:backend`** (`RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains
`RealizedProgram.ProofSystem.fieldBranches` of `proofSystem`): the series–parallel composite is round-by-round knowledge sound
for `Ring.rel` at the proof system's extractor (`RealizedProgram.ProofSystem.FieldBranches.extractor`, reading the frontend's
witness map at the realized assignment of the committed cells), with every challenge's own error
(`RealizedProgram.ProofSystem.IOP.Sound.error`): at a phase's challenge round the sum over the phase's challenges of
`Π_P₀`'s errors and the realization step's (`RealizedProgram.phaseError`), at every other challenge the
error of that challenge in its domain's commit rounds, branches or join part. -/
@[headline]
theorem iop_rbr_knowledge_soundness :
    CausalRBRKnowledgeSound Ring.rel ((proofSystem.fieldBranches ready).soundIOP source_rbr_knowledge_soundness sourceError_final).verifier
      ((proofSystem.fieldBranches ready).extractor source_rbr_knowledge_soundness sourceError_final)
      ((proofSystem.fieldBranches ready).soundIOPSound (proofSystem.fieldBranchesSound ready) source_rbr_knowledge_soundness sourceError_final).stateFn
      ((proofSystem.fieldBranches ready).soundIOPSound (proofSystem.fieldBranchesSound ready) source_rbr_knowledge_soundness sourceError_final).error :=
  (proofSystem.fieldBranches ready).causal_rbr_knowledge_soundness (proofSystem.fieldBranchesSound ready) source_rbr_knowledge_soundness sourceError_final

variable {Inp : Type} {relH : Set (program.Valuation interp × Inp)}

/-- **Completeness of `Falcon512.Ring.Carrier.ROMParams` at the realized program** (`RealizedProgram.ProofSystem.FieldBranches.completeness` at
the forked domains `RealizedProgram.ProofSystem.fieldBranches` of `proofSystem`, the domains' honest provers `RealizedProgram.ProofSystem.fieldHonestDomains`): in the
series–parallel order of `prot:backend`, if the honest prover `H` has completeness error `errc` (a function of the statement)
(`hc`), then at every value of the coins, on every honest input, the honest prover is rejected with
probability at most `errc`. -/
@[headline]
theorem iop_completeness (H : program.HonestCore interp relH)
    {errc : program.Valuation interp → ℝ≥0} (hc : H.Complete errc) (c : (proofSystem.fieldForkHonest ready H).Coins) :
    CausalCompleteStmt relH (proofSystem.fieldBranches ready).protocol.verifier
      (fun y => RealizedProgram.ProofSystem.IOP.honest (proofSystem.fieldForkHonest ready H) y c) errc :=
  (proofSystem.fieldBranches ready).completeness (proofSystem.fieldHonestDomains ready) _ H hc c

/-- **Honest-verifier zero knowledge of `Falcon512.Ring.Carrier.ROMParams` at the realized program**
(`RealizedProgram.ProofSystem.FieldBranches.hvzk` at the forked domains of `proofSystem`): in the series–parallel order of
`prot:backend`, if the honest prover `H` has completeness error `errc` (a function of the statement) (`hc`), the simulator of the
series–parallel composite is honest-verifier zero knowledge for the honest prover with error `errc`. -/
@[headline]
theorem iop_hvzk (H : program.HonestCore interp relH) {errc : program.Valuation interp → ℝ≥0}
    (hc : H.Complete errc) :
    CausalHVZKStmt (proofSystem.fieldBranches ready).protocol.toCausalIOP.views relH
      (RealizedProgram.ProofSystem.IOP.honest (proofSystem.fieldForkHonest ready H))
      id
      (RealizedProgram.ProofSystem.IOP.simulator
        ((proofSystem.fieldBranches ready).simData (proofSystem.fieldForkSims ready))) errc :=
  (proofSystem.fieldBranches ready).hvzk (proofSystem.fieldHonestDomains ready) _ H hc

end GordieHowe.Falcon512.Ring.Carrier.ROMParams
