-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.Falcon512.Emulated.ROMParams.Certified
public import GordieHoweCerts.Applications.Falcon512.Frontend.Hash
public import GordieHoweCerts.Applications.Falcon512.Emulated.ROMParams.Frontend.HashFacts
public import GordieHoweCerts.Applications.Falcon512.Emulated.ROMParams.Frontend.AlgebraFacts
public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.Applications.Configuration.Certified
public import GordieHoweCerts.Applications.Falcon512.Emulated.HonestFull

@[expose] public section

/-!
# GordieHowe: the theorem at the realized program for `Falcon512.Emulated.ROMParams`

The Falcon frontend's round-by-round knowledge soundness of `Π_P₀` at the Falcon-512
proof-of-possession relation (`GordieHowe.Falcon512.rbr_of_views`: the relation `rel` at the decoded
key, the extractor `proj`, the error `717/2^128` at `h2p.select.delta`) composed with the proof
system (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the
forked domains of `proofSystem`): the proof system's protocol is round-by-round knowledge sound for
`rel` at the proof system's extractor reading `proj`, with the phase errors
(`GordieHowe.RealizedProgram.phaseError`) and the domain proofs' errors. The frontend's two
obligations are proved: the hash view (`falconHashView`, the Keccak trace's SHAKE256 call over the
nonce and the message at the length the in-message flags encode) and domain A's algebra
(`algebraSound`, `GordieHowe.Falcon512.Emulated.algebraSound`: Falcon's arithmetic modulo `q`
emulated in Goldilocks, read off the source program at the key `statement.hhat` decodes to).

**Round-by-round knowledge soundness of `Π_P₀`** (`source_rbr_knowledge_soundness`): `rbr_of_views
falconHashView algebraSound`, with state function `sourceState` and errors `Program.roundError
selectEps`.
-/

namespace GordieHowe.Falcon512.Emulated.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP
open Generated.Falcon512.Emulated.ROMParams.Program (program)
open Generated.Falcon512.Emulated.ROMParams (interp ready ProofSystems certified sourceErrors)
open scoped NNReal

/-- **The proof system of `Falcon512.Emulated.ROMParams`**
(`GordieHowe.Generated.Falcon512.Emulated.ROMParams.proofSystem`): the generic per-field proof
system at the certificates' sources, whose circuits enforce their entries and accept the honest
inputs by the certificates. -/
abbrev proofSystem : ProofSystems :=
  Generated.Falcon512.Emulated.ROMParams.proofSystem

/-- **`Π_P₀`'s round errors vanish at `γ_end`**: they are `selectEps` at a challenge round, `0` at
every other round. -/
theorem sourceError_final :
    ∀ i, program.rounds.get i.1 = .final → program.roundError interp (selectEps (FH := RealizedProgram.gf128)) i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

/-- **Round-by-round knowledge soundness of `Π_P₀` for `Falcon512.Emulated.ROMParams`** at the relation
`rel`, the extractor `extractor` and the errors `717/2^128` at `h2p.select.delta`, `0` elsewhere
(`rbr_of_views` at the hash view `falconHashView` and domain A's `algebraSound`). -/
theorem source_rbr_knowledge_soundness :
    rbrKnowledgeSoundness rel (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj selectEvent selectEvent_use
        (sound_of_views falconHashView algebraSound))
      (program.roundError interp (selectEps (FH := RealizedProgram.gf128))) :=
  rbr_of_views falconHashView algebraSound

/-- **The source challenges' errors are within their fractions** (`sourceErrors`). -/
theorem sampleEps_le (j : ℕ) (_ : program.IsSourceChal j) :
    (selectEps (FH := RealizedProgram.gf128)) j ≤ ((sourceErrors j).1 : ℝ≥0) / (sourceErrors j).2 := by
  unfold selectEps
  simp only [sourceErrors]
  split_ifs
  · show (717 : ℝ≥0) / 2 ^ 128 ≤ _
    norm_num
  · exact zero_le'

/-- **The source program's soundness of `Falcon512.Emulated.ROMParams`** (`Configuration.SourceFront`): the frontend's
round-by-round knowledge soundness (`source_rbr_knowledge_soundness`) at the source challenges'
errors, within their generated fractions (`sampleEps_le`), and the honest nodes' `1`. -/
noncomputable def source : Configuration.SourceFront certified VarWitness
    (program.eventState interp rel proj selectEvent selectEvent_use (sound_of_views falconHashView
      algebraSound)) where
  rel := rel
  proj := proj
  eps := (selectEps (FH := RealizedProgram.gf128))
  sound := source_rbr_knowledge_soundness
  final := sourceError_final
  eps_le := sampleEps_le
  oneNodes := oneNodes (FH := RealizedProgram.gf128) (FA := RealizedProgram.gold2)

instantiate_config GordieHowe.Falcon512.Emulated.ROMParams
  from [GordieHowe.Configuration.CertifiedSource] certified source at proofSystem

end GordieHowe.Falcon512.Emulated.ROMParams
