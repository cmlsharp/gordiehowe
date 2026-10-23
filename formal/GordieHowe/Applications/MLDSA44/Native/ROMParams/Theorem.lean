-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.ProofSystem
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Algebra
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Sample
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Hash

@[expose] public section

/-!
# GordieHowe: the theorem at the realized program for `MLDSA44.Native.ROMParams`

The frontend's round-by-round knowledge soundness of `Π_P₀` at the ML-DSA-44 proof-of-possession
relation (`GordieHowe.MLDSA44.Native.ROMParams.rbr_of_views`: the relation `rel` at every key whose preprocessing the
statement holds, the extractor `proj`) at its four obligations, all proved: the hash view
(`hashView`, the Keccak trace's three SHAKE256 calls), SampleInBall's view (`sampleView`: its events
and errors `264/2^128` at `h2c.sample.select.delta` and `295/2^128` at `h2c.sample.mem.delta`, and
its soundness), the crossing (`crossSound`, `mac.equal`) and domain `A`'s algebra (`algebraSound`);
composed with the proof system (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains of `ROMParams.proofSystem`) in the headline
`rbr_knowledge_soundness`, whose only hypothesis is the compiler trust `CircuitsEnforce`.
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP
open Generated.MLDSA44.Native.ROMParams.Program (program)
open HashField (interp)
open scoped NNReal

/-- **`Π_P₀`'s round errors vanish at `γ_end`**: they are the view's errors at a challenge round,
`0` at every other round. -/
theorem sourceError_final (ε : ℕ → ℝ≥0) :
    ∀ i, program.rounds.get i.1 = .final → program.roundError interp ε i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

variable (src : ∀ c : Fin program.circuits.length, program.CircuitSource interp c)

/-- **Round-by-round knowledge soundness of `Π_P₀` for `MLDSA44.Native.ROMParams`** at the relation
`rel`, the extractor `extractor` and SampleInBall's errors (`rbr_of_views` at `hashView`,
`sampleView`, `crossSound` and `algebraSound`). -/
theorem source_rbr_knowledge_soundness :
    rbrKnowledgeSoundness rel (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj sampleEvent sampleEvent_use
        (sound_of_views hashView sampleView crossSound algebraSound))
      (program.roundError interp sampleEps) :=
  rbr_of_views hashView sampleView crossSound algebraSound

/-- **Soundness of `MLDSA44.Native.ROMParams` at the realized program, in the series–parallel order of
`prot:backend`** (`RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains
`RealizedProgram.ProofSystem.fieldBranches` of `proofSystem`): the series–parallel composite is round-by-round knowledge sound
for `rel` at the proof system's extractor (`RealizedProgram.ProofSystem.FieldBranches.extractor`, reading the frontend's
witness map at the realized assignment of the committed cells), with every challenge's own error
(`RealizedProgram.ProofSystem.IOP.Sound.error`): at a phase's challenge round the sum over the phase's challenges of
`Π_P₀`'s errors and the realization step's (`RealizedProgram.phaseError`), at every other challenge the
error of that challenge in its domain's commit rounds, branches or join part. `T`: the program's
GKR circuits enforce their entries (trust base). -/
@[headline]
theorem iop_rbr_knowledge_soundness (T : (proofSystem src).CircuitsEnforce) :
    CausalRBRKnowledgeSound rel (((proofSystem src).fieldBranches ready).soundIOP T source_rbr_knowledge_soundness (sourceError_final sampleEps)).verifier
      (((proofSystem src).fieldBranches ready).extractor T source_rbr_knowledge_soundness (sourceError_final sampleEps))
      (((proofSystem src).fieldBranches ready).soundIOPSound ((proofSystem src).fieldBranchesSound ready) T source_rbr_knowledge_soundness (sourceError_final sampleEps)).stateFn
      (((proofSystem src).fieldBranches ready).soundIOPSound ((proofSystem src).fieldBranchesSound ready) T source_rbr_knowledge_soundness (sourceError_final sampleEps)).error :=
  ((proofSystem src).fieldBranches ready).causal_rbr_knowledge_soundness ((proofSystem src).fieldBranchesSound ready) T source_rbr_knowledge_soundness (sourceError_final sampleEps)

end GordieHowe.MLDSA44.Native.ROMParams
