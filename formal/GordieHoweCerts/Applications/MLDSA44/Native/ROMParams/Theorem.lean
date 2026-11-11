-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.MLDSA44.Native.ROMParams.Certified
public import GordieHoweCerts.Applications.MLDSA44.Native.Frontend.Algebra
public import GordieHoweCerts.Applications.MLDSA44.Frontend.Sample
public import GordieHoweCerts.Applications.MLDSA44.Frontend.Hash
public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.Applications.Configuration.Certified
public import GordieHoweCerts.Applications.MLDSA44.Native.HonestFull

@[expose] public section

/-!
# GordieHowe: the theorem at the realized program for `MLDSA44.Native.ROMParams`

The frontend's round-by-round knowledge soundness of `Π_P₀` at the ML-DSA-44 proof-of-possession
relation (`GordieHowe.MLDSA44.rbr_of_views`: the relation `rel` at every key whose preprocessing the
statement holds, the extractor `proj`) at its four obligations, all proved: the hash view
(`hashView`, the Keccak trace's three SHAKE256 calls), SampleInBall's view (`sampleView`: its events
and errors `264/2^128` at `h2c.sample.select.delta` and `295/2^128` at `h2c.sample.mem.delta`, and
its soundness), the crossing (`crossSound`, `mac.equal`) and domain `A`'s algebra (`algebraSound`);
composed with the proof system (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains of `ROMParams.proofSystem`) in
`iop_rbr_knowledge_soundness`, at the proof system `proofSystem` of the certificates (no
compiler-trust hypothesis).
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP
open Generated.MLDSA44.Native.ROMParams.Program (program)
open Generated.MLDSA44.Native.ROMParams (interp ProofSystems certified sourceErrors)
open scoped NNReal

/-- **The proof system of `MLDSA44.Native.ROMParams`**
(`GordieHowe.Generated.MLDSA44.Native.ROMParams.proofSystem`): the generic per-field proof system at
the certificates' sources, whose circuits enforce their entries and accept the honest inputs by the
certificates. -/
abbrev proofSystem : ProofSystems :=
  Generated.MLDSA44.Native.ROMParams.proofSystem

/-- **`Π_P₀`'s round errors vanish at `γ_end`**: they are the view's errors at a challenge round,
`0` at every other round. -/
theorem sourceError_final (ε : ℕ → ℝ≥0) :
    ∀ i, program.rounds.get i.1 = .final → program.roundError interp ε i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

/-- **The state function of `Π_P₀`'s round-by-round knowledge soundness** (`RealizedProgram.eventState`)
at the relation, the extractor's projection and the source challenges' event, the frontend's soundness
proofs as its argument. -/
abbrev sourceState :=
  program.eventState interp rel proj sampleEvent sampleEvent_use (sound_of_views hashView sampleView crossSound algebraSound)

/-- **Round-by-round knowledge soundness of `Π_P₀` for `MLDSA44.Native.ROMParams`** at the relation
`rel`, the extractor `extractor` and SampleInBall's errors (`rbr_of_views` at `hashView`,
`sampleView`, `crossSound` and `algebraSound`). -/
theorem source_rbr_knowledge_soundness :
    RBRKnowledgeSound rel (program.sourceVerifier interp) extractor
      sourceState
      (program.roundError interp sampleEps) :=
  rbr_of_views hashView sampleView crossSound algebraSound

/-- **The source challenges' errors are within their fractions** (`sourceErrors`): `264/2^128` and
`295/2^128` at SampleInBall's challenges. -/
theorem sampleEps_le (j : ℕ) (_ : program.IsSourceChal j) :
    sampleEps j ≤ ((sourceErrors j).1 : ℝ≥0) / (sourceErrors j).2 := by
  unfold sampleEps MLDSA44.sampleEpsOf
  simp only [sourceErrors]
  split_ifs <;> norm_num

/-- **The source program's soundness of `MLDSA44.Native.ROMParams`** (`Configuration.SourceFront`):
the frontend's round-by-round knowledge soundness (`source_rbr_knowledge_soundness`) at
SampleInBall's errors (`sampleEps`, within `sampleEps_le`), and the honest nodes' `1`
(`MLDSA44.Native.oneNodes`). -/
noncomputable def source : Configuration.SourceFront certified VarWitness
    sourceState where
  rel := rel
  proj := proj
  eps := sampleEps
  sound := source_rbr_knowledge_soundness
  final := sourceError_final sampleEps
  eps_le := sampleEps_le
  oneNodes := Native.oneNodes

instantiate_config GordieHowe.MLDSA44.Native.ROMParams
  from [GordieHowe.Configuration.CertifiedSource] certified source at proofSystem

end GordieHowe.MLDSA44.Native.ROMParams
