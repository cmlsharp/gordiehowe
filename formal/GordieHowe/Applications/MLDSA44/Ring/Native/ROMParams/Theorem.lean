-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Certified
public import GordieHowe.Applications.MLDSA44.Ring.Native.ROMParams.Frontend.Front
public import GordieHowe.ProofSystem.Program.Headlines

@[expose] public section

/-!
# GordieHowe: the theorem at the realized program for `MLDSA44.Ring.Native.ROMParams`

The frontend's round-by-round knowledge soundness of `Π_P₀` at the native ML-DSA-44 ring relation
(`GordieHowe.MLDSA44.Ring.Native.ROMParams.source_rbr_knowledge_soundness`: the relation
`GordieHowe.MLDSA44.Ring.Native.rel` at every checked ring statement whose rows the statement
holds, the extractor `GordieHowe.MLDSA44.Ring.Native.extractor`, the errors `sourceEps`:
`5143/|F_q^6|` at `member.table.gamma`, SampleInBall's `264/2^128` and `295/2^128` at the ring's
challenges `1` and `2`), composed with the proof system
(`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked
domains of `proofSystem`) in the headline `iop_rbr_knowledge_soundness`, whose only hypothesis is
the compiler trust `CircuitsEnforce`.
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP
open Generated.MLDSA44.Ring.Native.ROMParams.Program (program)
open Generated.MLDSA44.Ring.Native.ROMParams (interp ready ProofSystems)
open scoped NNReal

/-- **The proof system of `MLDSA44.Ring.Native.ROMParams`**
(`GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.proofSystem`): the generic per-field proof
system at the certificates' sources, whose circuits enforce their entries and accept the honest
inputs by the certificates. -/
abbrev proofSystem : ProofSystems :=
  Generated.MLDSA44.Ring.Native.ROMParams.proofSystem

/-- **The round errors of `Π_P₀`'s challenges** (`Native.ringEps` at SampleInBall's view
`MLDSA44.sampleView`): `5143/|F_q^6|` at `member.table.gamma` (challenge `0`),
`264/2^128` and `295/2^128` at the ring's challenges `1` and `2`. -/
noncomputable abbrev sourceEps : ℕ → ℝ≥0 :=
  Native.ringEps (program := program) (F0 := RealizedProgram.fq6) (FH := RealizedProgram.gf128)
    MLDSA44.sampleView

/-- **`Π_P₀`'s round errors vanish at `γ_end`**: they are the view's errors at a challenge round,
`0` at every other round. -/
theorem sourceError_final (ε : ℕ → ℝ≥0) :
    ∀ i, program.rounds.get i.1 = .final → program.roundError interp ε i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

/-- **Soundness of `MLDSA44.Ring.Native.ROMParams` at the realized program, in the series–parallel order of
`prot:backend`** (`RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains
`RealizedProgram.ProofSystem.fieldBranches` of `proofSystem`): the series–parallel composite is round-by-round
knowledge sound for the relation at the proof system's extractor, with every challenge's own error
(`RealizedProgram.ProofSystem.IOP.Sound.error`). -/
@[headline]
theorem iop_rbr_knowledge_soundness :
    CausalRBRKnowledgeSound (Native.rel (program := program) (F0 := RealizedProgram.fq6)
        (FH := RealizedProgram.gf128))
      ((proofSystem.fieldBranches ready).soundIOP source_rbr_knowledge_soundness (sourceError_final sourceEps)).verifier
      ((proofSystem.fieldBranches ready).extractor source_rbr_knowledge_soundness (sourceError_final sourceEps))
      ((proofSystem.fieldBranches ready).soundIOPSound (proofSystem.fieldBranchesSound ready)
        source_rbr_knowledge_soundness (sourceError_final sourceEps)).stateFn
      ((proofSystem.fieldBranches ready).soundIOPSound (proofSystem.fieldBranchesSound ready)
        source_rbr_knowledge_soundness (sourceError_final sourceEps)).error :=
  (proofSystem.fieldBranches ready).causal_rbr_knowledge_soundness (proofSystem.fieldBranchesSound ready)
    source_rbr_knowledge_soundness (sourceError_final sourceEps)

variable {Inp : Type} {relH : Set (program.Valuation interp × Inp)}

/-- **Completeness of `MLDSA44.Ring.Native.ROMParams` at the realized program** (`RealizedProgram.ProofSystem.FieldBranches.completeness` at
the forked domains `RealizedProgram.ProofSystem.fieldBranches` of `proofSystem`, the domains' honest provers
`RealizedProgram.ProofSystem.fieldHonestDomains`): in the series–parallel order of `prot:backend`, if the honest
prover `H` has completeness error `errc` (a function of the statement) (`hc`), then at every value
of the coins, on every honest input, the honest prover is rejected with probability at most
`errc`. -/
@[headline]
theorem iop_completeness (H : program.HonestCore interp relH)
    {errc : program.Valuation interp → ℝ≥0} (hc : H.Complete errc)
    (c : (proofSystem.fieldForkHonest ready H).Coins) :
    CausalCompleteStmt relH (proofSystem.fieldBranches ready).protocol.verifier
      (fun y => RealizedProgram.ProofSystem.IOP.honest (proofSystem.fieldForkHonest ready H) y c) errc :=
  (proofSystem.fieldBranches ready).completeness (proofSystem.fieldHonestDomains ready) _ H hc c

/-- **Honest-verifier zero knowledge of `MLDSA44.Ring.Native.ROMParams` at the realized program**
(`RealizedProgram.ProofSystem.FieldBranches.hvzk` at the forked domains of `proofSystem`): in the series–parallel order of
`prot:backend`, if the honest prover `H` has completeness error `errc` (a function of the statement) (`hc`), the simulator of the
series–parallel composite is honest-verifier zero knowledge for the honest prover with error `errc`. -/
@[headline]
theorem iop_hvzk (H : program.HonestCore interp relH) {errc : program.Valuation interp → ℝ≥0}
    (hc : H.Complete errc) :
    CausalHVZKStmt (proofSystem.fieldBranches ready).protocol.toCausalIOP.views relH
      (RealizedProgram.ProofSystem.IOP.honest (proofSystem.fieldForkHonest ready H)) id
      (RealizedProgram.ProofSystem.IOP.simulator
        ((proofSystem.fieldBranches ready).simData (proofSystem.fieldForkSims ready))) errc :=
  (proofSystem.fieldBranches ready).hvzk (proofSystem.fieldHonestDomains ready) _ H hc

end GordieHowe.MLDSA44.Ring.Native.ROMParams
