-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Certified
public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.Frontend.Algebra
public import GordieHowe.ProofSystem.Program.Headlines

@[expose] public section

/-!
# GordieHowe: the theorem at the realized program of `MLDSA44.Emulated.ROMParams`

The frontend's round-by-round knowledge soundness of `Π_P₀` at the ML-DSA-44 proof-of-possession
relation (`GordieHowe.MLDSA44.Emulated.ROMParams.rbr_of_views`: the relation `rel` at every key whose preprocessing
the statement holds, the extractor `proj`) at its obligations, all proved: the hash view and
SampleInBall's view are those of `MLDSA44.Native.ROMParams`, read through the renaming of domain `H`
(`GordieHowe/Applications/MLDSA44/Emulated/ROMParams/Frontend/Embed.lean`; SampleInBall's errors `264/2^128` at `h2c.sample.select.delta` and
`295/2^128` at `h2c.sample.mem.delta`), the crossing (`crossSound`, `mac.equal`) and domain `A`'s
algebra (`algebraSound`, over Goldilocks² with the signature relation a source `mod_q`); composed
with the proof system (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains of `proofSystem`) in the headline
`iop_rbr_knowledge_soundness`, at the proof system `proofSystem` of the certificates (no
compiler-trust hypothesis). The
program declares the statement bounds `key.a < q`, `key.t1 < 2^10`, which the verifier checks before
the proof.
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP
open Generated.MLDSA44.Emulated.ROMParams.Program (program)
open Generated.MLDSA44.Emulated.ROMParams (interp ready ProofSystems)
open scoped NNReal

/-- **The proof system of `MLDSA44.Emulated.ROMParams`**
(`GordieHowe.Generated.MLDSA44.Emulated.ROMParams.proofSystem`): the generic per-field proof system
at the certificates' sources, whose circuits enforce their entries and accept the honest inputs by
the certificates. -/
abbrev proofSystem : ProofSystems :=
  Generated.MLDSA44.Emulated.ROMParams.proofSystem

/-- **`Π_P₀`'s round errors vanish at `γ_end`**: they are the view's errors at a challenge round,
`0` at every other round. -/
theorem sourceError_final (ε : ℕ → ℝ≥0) :
    ∀ i, program.rounds.get i.1 = .final → program.roundError interp ε i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

/-- **Round-by-round knowledge soundness of `Π_P₀` for `MLDSA44.Emulated.ROMParams`** at the relation
`rel`, the extractor `extractor` and SampleInBall's errors (`rbr_of_views` at `crossSound` and
`algebraSound`). -/
theorem source_rbr_knowledge_soundness :
    rbrKnowledgeSoundness rel (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj sampleEvent sampleEvent_use
        (sound_of_views crossSound algebraSound))
      (program.roundError interp MLDSA44.sampleEps) :=
  rbr_of_views crossSound algebraSound

/-- **Soundness of `MLDSA44.Emulated.ROMParams` at the realized program, in the series–parallel order of
`prot:backend`** (`RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains
`RealizedProgram.ProofSystem.fieldBranches` of `proofSystem`): the series–parallel composite is round-by-round knowledge sound
for `rel` at the proof system's extractor (`RealizedProgram.ProofSystem.FieldBranches.extractor`, reading the frontend's
witness map at the realized assignment of the committed cells), with every challenge's own error
(`RealizedProgram.ProofSystem.IOP.Sound.error`): at a phase's challenge round the sum over the phase's challenges of
`Π_P₀`'s errors and the realization step's (`RealizedProgram.phaseError`), at every other challenge the
error of that challenge in its domain's commit rounds, branches or join part. -/
@[headline]
theorem iop_rbr_knowledge_soundness :
    CausalRBRKnowledgeSound rel ((proofSystem.fieldBranches ready).soundIOP source_rbr_knowledge_soundness (sourceError_final MLDSA44.sampleEps)).verifier
      ((proofSystem.fieldBranches ready).extractor source_rbr_knowledge_soundness (sourceError_final MLDSA44.sampleEps))
      ((proofSystem.fieldBranches ready).soundIOPSound (proofSystem.fieldBranchesSound ready) source_rbr_knowledge_soundness (sourceError_final MLDSA44.sampleEps)).stateFn
      ((proofSystem.fieldBranches ready).soundIOPSound (proofSystem.fieldBranchesSound ready) source_rbr_knowledge_soundness (sourceError_final MLDSA44.sampleEps)).error :=
  (proofSystem.fieldBranches ready).causal_rbr_knowledge_soundness (proofSystem.fieldBranchesSound ready) source_rbr_knowledge_soundness (sourceError_final MLDSA44.sampleEps)

variable {Inp : Type} {relH : Set (program.Valuation interp × Inp)}

/-- **Completeness of `MLDSA44.Emulated.ROMParams` at the realized program** (`RealizedProgram.ProofSystem.FieldBranches.completeness` at
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

/-- **Honest-verifier zero knowledge of `MLDSA44.Emulated.ROMParams` at the realized program**
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

end GordieHowe.MLDSA44.Emulated.ROMParams
