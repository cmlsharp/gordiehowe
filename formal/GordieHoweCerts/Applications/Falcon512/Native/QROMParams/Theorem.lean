-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.Falcon512.Native.QROMParams.Certified
public import GordieHoweCerts.Applications.Falcon512.Native.Frontend.Algebra
public import GordieHoweCerts.Applications.Falcon512.Frontend.Hash
public import GordieHoweCerts.Applications.Falcon512.Native.QROMParams.Frontend.HashFacts
public import GordieHoweCerts.Applications.Falcon512.Native.QROMParams.Frontend.AlgebraFacts
public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.Applications.Configuration.Certified
public import GordieHoweCerts.Applications.Falcon512.Native.HonestFull

@[expose] public section

/-!
# GordieHowe: the theorem at the realized program for `Falcon512.Native.QROMParams`

The native Falcon frontend's round-by-round knowledge soundness of `Π_P₀` at the Falcon-512
proof-of-possession relation (`GordieHowe.Falcon512.rbr_of_views`, generic in the program and its
fields, at the program facts of `GordieHoweCerts/Applications/Falcon512/Native/QROMParams/Frontend/Facts.lean`,
`GordieHoweCerts/Applications/Falcon512/Native/QROMParams/Frontend/HashFacts.lean` and
`GordieHoweCerts/Applications/Falcon512/Native/QROMParams/Frontend/AlgebraFacts.lean`: the relation `rel` at the decoded key, the extractor `proj`, the
error `717/2^256` at `h2p.select.delta`) composed with the proof system
(`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains of `proofSystem`): the proof system's protocol is
round-by-round knowledge sound for `rel` at the proof system's extractor reading `proj`, with the
phase errors (`GordieHowe.RealizedProgram.phaseError`) `717/2^256 + 32/2^256` and `18175/(q^20 − 189)` and the
domain proofs' errors. The frontend's two obligations are the generic frontend's: the hash view
(`falconHashView`) and domain A's algebra (`algebraSound`).

**Round-by-round knowledge soundness of `Π_P₀`** (`source_rbr_knowledge_soundness`): `rbr_of_views falconHashView
algebraSound`, with state function `sourceState` and errors `Program.roundError selectEps`.
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP
open Generated.Falcon512.Native.QROMParams.Program (program)
open Generated.Falcon512.Native.QROMParams (interp ready ProofSystems certified sourceErrors)
open scoped NNReal

/-- **The proof system of `Falcon512.Native.QROMParams`**
(`GordieHowe.Generated.Falcon512.Native.QROMParams.proofSystem`): the generic per-field proof system
at the certificates' sources, whose circuits enforce their entries and accept the honest inputs by
the certificates. -/
abbrev proofSystem : ProofSystems :=
  Generated.Falcon512.Native.QROMParams.proofSystem

/-- **`Π_P₀`'s round errors vanish at `γ_end`**: they are `selectEps` at a challenge round, `0` at
every other round. -/
theorem sourceError_final :
    ∀ i, program.rounds.get i.1 = .final → program.roundError interp (selectEps (FH := RealizedProgram.gf256)) i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

/-- **The state function of `Π_P₀`'s round-by-round knowledge soundness** (`RealizedProgram.eventState`)
at the relation, the extractor's projection and the source challenges' event, the frontend's soundness
proofs as its argument. -/
abbrev sourceState :=
  program.eventState interp rel proj selectEvent selectEvent_use (sound_of_views falconHashView (algebraSound normSound))

/-- **Round-by-round knowledge soundness of `Π_P₀` for `Falcon512.Native.QROMParams`** at the relation
`rel`, the extractor `extractor` and the errors `717/2^256` at `h2p.select.delta`, `0` elsewhere
(`rbr_of_views` at the hash view `falconHashView` and domain A's `algebraSound`). -/
theorem source_rbr_knowledge_soundness :
    RBRKnowledgeSound rel (program.sourceVerifier interp) extractor
      sourceState
      (program.roundError interp (selectEps (FH := RealizedProgram.gf256))) :=
  rbr_of_views falconHashView (algebraSound normSound)

/-- **The source challenges' errors are within their fractions** (`sourceErrors`). -/
theorem sampleEps_le (j : ℕ) (_ : program.IsSourceChal j) :
    (selectEps (FH := RealizedProgram.gf256)) j ≤ ((sourceErrors j).1 : ℝ≥0) / (sourceErrors j).2 := by
  unfold selectEps
  simp only [sourceErrors]
  split_ifs
  · show (717 : ℝ≥0) / 2 ^ 256 ≤ _
    norm_num
  · exact zero_le'

/-- **The source program's soundness of `Falcon512.Native.QROMParams`** (`Configuration.SourceFront`): the frontend's
round-by-round knowledge soundness (`source_rbr_knowledge_soundness`) at the source challenges'
errors, within their generated fractions (`sampleEps_le`), and the honest nodes' `1`. -/
noncomputable def source : Configuration.SourceFront certified VarWitness
    sourceState where
  rel := rel
  proj := proj
  eps := (selectEps (FH := RealizedProgram.gf256))
  sound := source_rbr_knowledge_soundness
  final := sourceError_final
  eps_le := sampleEps_le
  oneNodes := oneNodes (FH := RealizedProgram.gf256) (FA := RealizedProgram.fq20)

instantiate_config GordieHowe.Falcon512.Native.QROMParams
  from [GordieHowe.Configuration.CertifiedSource] certified source at proofSystem

end GordieHowe.Falcon512.Native.QROMParams
