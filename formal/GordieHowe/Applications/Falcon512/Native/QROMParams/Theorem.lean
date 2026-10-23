-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.QROMParams.ProofSystem
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.Algebra
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.Hash
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Frontend.HashFacts
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Frontend.AlgebraFacts

@[expose] public section

/-!
# GordieHowe: the theorem at the realized program for `Falcon512.Native.QROMParams`

The native Falcon frontend's round-by-round knowledge soundness of `Π_P₀` at the Falcon-512
proof-of-possession relation (`GordieHowe.Falcon512.Native.ROMParams.rbr_of_views`, generic in the program and its
fields, at the program facts of `GordieHowe/Applications/Falcon512/Native/QROMParams/Frontend/Facts.lean`,
`GordieHowe/Applications/Falcon512/Native/QROMParams/Frontend/HashFacts.lean` and
`GordieHowe/Applications/Falcon512/Native/QROMParams/Frontend/AlgebraFacts.lean`: the relation `rel` at the decoded key, the extractor `proj`, the
error `639/2^256` at `h2p.select.delta`) composed with the proof system
(`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains of `proofSystem`): the proof system's protocol is
round-by-round knowledge sound for `rel` at the proof system's extractor reading `proj`, with the
phase errors (`GordieHowe.RealizedProgram.phaseError`) `639/2^256 + 32/2^256` and `18175/(q^20 − 189)` and the
domain proofs' errors. The frontend's two obligations are the generic frontend's: the hash view
(`falconHashView`) and domain A's algebra (`algebraSound`).

**Round-by-round knowledge soundness of `Π_P₀`** (`source_rbr_knowledge_soundness`): `rbr_of_views falconHashView
algebraSound`, with state function `sourceState` and errors `Program.roundError selectEps`.
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP
open Generated.Falcon512.Native.QROMParams.Program (program)
open ROMParams
open scoped NNReal

/-- **`Π_P₀`'s round errors vanish at `γ_end`**: they are `selectEps` at a challenge round, `0` at
every other round. -/
theorem sourceError_final :
    ∀ i, program.rounds.get i.1 = .final → program.roundError interp (selectEps (FH := RealizedProgram.gf256)) i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

/-- **Round-by-round knowledge soundness of `Π_P₀` for `Falcon512.Native.QROMParams`** at the relation
`rel`, the extractor `extractor` and the errors `639/2^256` at `h2p.select.delta`, `0` elsewhere
(`rbr_of_views` at the hash view `falconHashView` and domain A's `algebraSound`). -/
theorem source_rbr_knowledge_soundness :
    rbrKnowledgeSoundness rel (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj selectEvent selectEvent_use
        (sound_of_views falconHashView (algebraSound normSound)))
      (program.roundError interp (selectEps (FH := RealizedProgram.gf256))) :=
  rbr_of_views falconHashView (algebraSound normSound)

variable (src : ∀ c : Fin program.circuits.length, program.CircuitSource interp c)

/-- **Soundness of `Falcon512.Native.QROMParams` at the realized program, in the series–parallel order of
`prot:backend`** (`RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains
`RealizedProgram.ProofSystem.fieldBranches` of `QROMParams.proofSystem`): the series–parallel composite is round-by-round knowledge sound in the series–parallel order
for `rel` at the proof system's extractor (`RealizedProgram.ProofSystem.FieldBranches.extractor`, reading the frontend's
witness map at the realized assignment of the committed cells), with every challenge's own error
(`RealizedProgram.ProofSystem.IOP.Sound.error`): at a phase's challenge round the sum over the phase's challenges of
`Π_P₀`'s errors and the realization step's (`RealizedProgram.phaseError`), at every other challenge the
error of that challenge in its domain's commit rounds, branches or join part. `T`: the program's
GKR circuits enforce their entries (trust base). -/
@[headline]
theorem iop_rbr_knowledge_soundness (T : (proofSystem src).CircuitsEnforce) :
    CausalRBRKnowledgeSound rel (((proofSystem src).fieldBranches ready).soundIOP T source_rbr_knowledge_soundness sourceError_final).verifier
      (((proofSystem src).fieldBranches ready).extractor T source_rbr_knowledge_soundness sourceError_final)
      (((proofSystem src).fieldBranches ready).soundIOPSound ((proofSystem src).fieldBranchesSound ready) T source_rbr_knowledge_soundness sourceError_final).stateFn
      (((proofSystem src).fieldBranches ready).soundIOPSound ((proofSystem src).fieldBranchesSound ready) T source_rbr_knowledge_soundness sourceError_final).error :=
  ((proofSystem src).fieldBranches ready).causal_rbr_knowledge_soundness ((proofSystem src).fieldBranchesSound ready) T source_rbr_knowledge_soundness sourceError_final

end GordieHowe.Falcon512.Native.QROMParams
