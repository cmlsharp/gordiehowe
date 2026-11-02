-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.Facts
public import GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Certified

@[expose] public section

/-!
# GordieHowe: the theorem at the realized program for `Falcon512.Ring.Native.QROMParams`

The frontend's round-by-round knowledge soundness of `Π_P₀` at the native Falcon ring relation
(`GordieHowe.Falcon512.Ring.rbr_of_norm`: the relation `GordieHowe.Falcon512.Ring.rel` at the statement's ring and challenge,
the extractor `GordieHowe.Falcon512.Ring.proj`, the error `511/q^20` at `member.ring.gamma`), its norm's
obligation discharged by the generic norm (`normSound`, `FalconNorm`), composed with the proof system
(`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains of `proofSystem`).
-/

namespace GordieHowe.Falcon512.Ring.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP
open Generated.Falcon512.Ring.Native.QROMParams.Program (program)
open Generated.Falcon512.Ring.Native.QROMParams (interp ready ProofSystems)
open scoped NNReal

/-- **The proof system of `Falcon512.Ring.Native.QROMParams`**
(`GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.proofSystem`): the generic per-field proof
system at the certificates' sources, whose circuits enforce their entries and accept the honest
inputs by the certificates. -/
abbrev proofSystem : ProofSystems :=
  Generated.Falcon512.Ring.Native.QROMParams.proofSystem

/-- **The norm's obligation** (`Ring.NormSound`): the generic norm's advice
(`Norm.algOf` at the slack's high digit) wherever the source program holds. -/
theorem normSound : Ring.NormSound (program := program) (I := interp) := fun e hs => by
  obtain ⟨k, hk, hkv⟩ := Norm.slack_below (program := program) (I := interp) hs
  exact ⟨Norm.algOf e ((k / 64 : ℕ) : _), fun _ => rfl, Norm.normHolds hs _,
    Norm.encodingBits hs _, ⟨Norm.digitsBelow hs, Norm.encodingRequests hs hk hkv⟩⟩

/-- **Round-by-round knowledge soundness of `Π_P₀` for `Falcon512.Ring.Native.QROMParams`** at the ring
relation `Ring.rel`, the extractor `Ring.extractor` and the errors `511/q^20` at
`member.ring.gamma`, `0` elsewhere. -/
theorem source_rbr_knowledge_soundness :
    rbrKnowledgeSoundness Ring.rel (program.sourceVerifier interp) Ring.extractor
      (program.eventState interp Ring.rel Ring.proj Ring.ringEvent
        Ring.ringEvent_use (Ring.sound_of_norm normSound))
      (program.roundError interp (Ring.ringEps interp)) :=
  Ring.rbr_of_norm normSound

/-- **`Π_P₀`'s round errors vanish at `γ_end`.** -/
theorem sourceError_final :
    ∀ i, program.rounds.get i.1 = .final → program.roundError interp (Ring.ringEps interp) i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

/-- **Soundness of `Falcon512.Ring.Native.QROMParams` at the realized program, in the series–parallel order of
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

/-- **Completeness of `Falcon512.Ring.Native.QROMParams` at the realized program** (`RealizedProgram.ProofSystem.FieldBranches.completeness` at
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

/-- **Honest-verifier zero knowledge of `Falcon512.Ring.Native.QROMParams` at the realized program**
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

end GordieHowe.Falcon512.Ring.Native.QROMParams
