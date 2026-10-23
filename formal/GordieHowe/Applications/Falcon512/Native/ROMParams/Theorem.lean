-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.ROMParams.ProofSystem
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.Algebra
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.Hash
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.HashFacts
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.AlgebraFacts

@[expose] public section

/-!
# GordieHowe: the theorem at the realized program for `Falcon512.Native.ROMParams`

The frontend's round-by-round knowledge soundness of `Π_P₀` at the Falcon-512 proof-of-possession
relation (`GordieHowe.Falcon512.Native.ROMParams.rbr_of_views`: the relation `rel` at the decoded key, the extractor
`proj`, the error `639/2^128` at `h2p.select.delta`) composed with the proof system
(`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains of `proofSystem`): the proof system's protocol is round-by-round
knowledge sound for `rel` at the proof system's extractor reading `proj`, with the phase errors
(`GordieHowe.RealizedProgram.phaseError`) `639/2^128 + 64/2^128` and `16448/(q^9 − 189)` and the domain proofs' errors.
The frontend's two obligations are proved: the hash view (`falconHashView`,
`GordieHowe/Applications/Falcon512/Native/ROMParams/Frontend/Hash.lean`: the Keccak trace's SHAKE256 call over the nonce and the message at
the length the in-message flags encode) and domain A's algebra (`algebraSound`,
`GordieHowe/Applications/Falcon512/Native/ROMParams/Frontend/Algebra.lean`).

**Round-by-round knowledge soundness of `Π_P₀`** (`source_rbr_knowledge_soundness`): `rbr_of_views falconHashView
algebraSound`, with state function `sourceState` and errors `Program.roundError selectEps`.
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP
open Generated.Falcon512.Native.ROMParams.Program (program)
open scoped NNReal

/-- **`Π_P₀`'s round errors vanish at `γ_end`**: they are `selectEps` at a challenge round, `0` at
every other round. -/
theorem sourceError_final :
    ∀ i, program.rounds.get i.1 = .final → program.roundError interp (selectEps (FH := RealizedProgram.gf128)) i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

/-- **Round-by-round knowledge soundness of `Π_P₀` for `Falcon512.Native.ROMParams`** at the relation
`rel`, the extractor `extractor` and the errors `639/2^128` at `h2p.select.delta`, `0` elsewhere
(`rbr_of_views` at the hash view `falconHashView` and domain A's `algebraSound`). -/
theorem source_rbr_knowledge_soundness :
    rbrKnowledgeSoundness rel (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj selectEvent selectEvent_use
        (sound_of_views falconHashView (algebraSound normSound)))
      (program.roundError interp (selectEps (FH := RealizedProgram.gf128))) :=
  rbr_of_views falconHashView (algebraSound normSound)

variable (src : ∀ c : Fin program.circuits.length, program.CircuitSource interp c)

/-- **Soundness of `Falcon512.Native.ROMParams` at the realized program, in the series–parallel order of
`prot:backend`** (`RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains
`RealizedProgram.ProofSystem.fieldBranches` of `proofSystem`): the series–parallel composite is round-by-round knowledge sound in the series–parallel order
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

end GordieHowe.Falcon512.Native.ROMParams
