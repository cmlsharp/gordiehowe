-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.Falcon512.Emulated.ROMParams.Certified
public import GordieHowe.Applications.Falcon512.Frontend.Hash
public import GordieHowe.Applications.Falcon512.Emulated.ROMParams.Frontend.HashFacts
public import GordieHowe.Applications.Falcon512.Emulated.ROMParams.Frontend.AlgebraFacts
public import GordieHowe.ProofSystem.Program.Headlines

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
open Generated.Falcon512.Emulated.ROMParams (interp ready ProofSystems)
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

/-- **Soundness of `Falcon512.Emulated.ROMParams` at the realized program, in the series–parallel order of
`prot:backend`** (`RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains
`RealizedProgram.ProofSystem.fieldBranches` of `proofSystem`): the series–parallel composite is round-by-round knowledge sound in the series–parallel order
for `rel` at the proof system's extractor (`RealizedProgram.ProofSystem.FieldBranches.extractor`, reading the frontend's
witness map at the realized assignment of the committed cells), with every challenge's own error
(`RealizedProgram.ProofSystem.IOP.Sound.error`): at a phase's challenge round the sum over the phase's challenges of
`Π_P₀`'s errors and the realization step's (`RealizedProgram.phaseError`), at every other challenge the
error of that challenge in its domain's commit rounds, branches or join part. -/
@[headline]
theorem iop_rbr_knowledge_soundness :
    CausalRBRKnowledgeSound rel
      ((proofSystem.fieldBranches ready).soundIOP source_rbr_knowledge_soundness sourceError_final).verifier
      ((proofSystem.fieldBranches ready).extractor source_rbr_knowledge_soundness sourceError_final)
      ((proofSystem.fieldBranches ready).soundIOPSound (proofSystem.fieldBranchesSound ready)
        source_rbr_knowledge_soundness sourceError_final).stateFn
      ((proofSystem.fieldBranches ready).soundIOPSound (proofSystem.fieldBranchesSound ready)
        source_rbr_knowledge_soundness sourceError_final).error :=
  (proofSystem.fieldBranches ready).causal_rbr_knowledge_soundness (proofSystem.fieldBranchesSound ready)
    source_rbr_knowledge_soundness sourceError_final

variable {Inp : Type} {relH : Set (program.Valuation interp × Inp)}

/-- **Completeness of `Falcon512.Emulated.ROMParams` at the realized program** (`RealizedProgram.ProofSystem.FieldBranches.completeness` at
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

/-- **Honest-verifier zero knowledge of `Falcon512.Emulated.ROMParams` at the realized program**
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

end GordieHowe.Falcon512.Emulated.ROMParams
