-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Native.ROMParams.Facts

@[expose] public section

/-!
# GordieHowe: the theorem at the realized program for `Falcon512.Ring.Native.ROMParams`

The frontend's round-by-round knowledge soundness of `Π_P₀` at the native Falcon ring relation
(`GordieHowe.Falcon512.Ring.rbr_of_norm`: the relation `GordieHowe.Falcon512.Ring.rel` at the statement's ring and challenge,
the extractor `GordieHowe.Falcon512.Ring.proj`, the error `511/q^9` at `member.ring.gamma`), its norm's
obligation discharged by the generic norm (`normSound`, `FalconNorm`), composed with the proof system
(`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains of `proofSystem`).
-/

namespace GordieHowe.Falcon512.Ring.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP
open Generated.Falcon512.Ring.Native.ROMParams.Program (program)
open scoped NNReal

/-- **The norm's obligation** (`Ring.NormSound`): the generic norm's advice
(`Norm.algOf` at the slack's high digit) wherever the source program holds. -/
theorem normSound : Ring.NormSound (program := program) (I := interpROM) := fun e hs => by
  obtain ⟨k, hk, hkv⟩ := Norm.slack_below (program := program) (I := interpROM) hs
  exact ⟨Norm.algOf e ((k / 64 : ℕ) : _), fun _ => rfl, Norm.normHolds hs _,
    Norm.encodingBits hs _, ⟨Norm.digitsBelow hs, Norm.encodingRequests hs hk hkv⟩⟩

/-- **Round-by-round knowledge soundness of `Π_P₀` for `Falcon512.Ring.Native.ROMParams`** at the ring
relation `Ring.rel`, the extractor `Ring.extractor` and the errors `511/q^9` at
`member.ring.gamma`, `0` elsewhere. -/
theorem source_rbr_knowledge_soundness :
    rbrKnowledgeSoundness Ring.rel (program.sourceVerifier interpROM) Ring.extractor
      (program.eventState interpROM Ring.rel Ring.proj Ring.ringEvent
        Ring.ringEvent_use (Ring.sound_of_norm normSound))
      (program.roundError interpROM (Ring.ringEps interpROM)) :=
  Ring.rbr_of_norm normSound

/-- **`Π_P₀`'s round errors vanish at `γ_end`.** -/
theorem sourceError_final :
    ∀ i, program.rounds.get i.1 = .final → program.roundError interpROM (Ring.ringEps interpROM) i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

variable (src : ∀ c : Fin program.circuits.length, program.CircuitSource interpROM c)

/-- **Soundness of `Falcon512.Ring.Native.ROMParams` at the realized program, in the series–parallel order of
`prot:backend`** (`RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains
`RealizedProgram.ProofSystem.fieldBranches` of `proofSystem`): the series–parallel composite is round-by-round knowledge sound
for `Ring.rel` at the proof system's extractor (`RealizedProgram.ProofSystem.FieldBranches.extractor`, reading the frontend's
witness map at the realized assignment of the committed cells), with every challenge's own error
(`RealizedProgram.ProofSystem.IOP.Sound.error`): at a phase's challenge round the sum over the phase's challenges of
`Π_P₀`'s errors and the realization step's (`RealizedProgram.phaseError`), at every other challenge the
error of that challenge in its domain's commit rounds, branches or join part. `T`: the program's
GKR circuits enforce their entries (trust base). -/
@[headline]
theorem iop_rbr_knowledge_soundness (T : (proofSystem src).CircuitsEnforce) :
    CausalRBRKnowledgeSound Ring.rel (((proofSystem src).fieldBranches ready).soundIOP T source_rbr_knowledge_soundness sourceError_final).verifier
      (((proofSystem src).fieldBranches ready).extractor T source_rbr_knowledge_soundness sourceError_final)
      (((proofSystem src).fieldBranches ready).soundIOPSound ((proofSystem src).fieldBranchesSound ready) T source_rbr_knowledge_soundness sourceError_final).stateFn
      (((proofSystem src).fieldBranches ready).soundIOPSound ((proofSystem src).fieldBranchesSound ready) T source_rbr_knowledge_soundness sourceError_final).error :=
  ((proofSystem src).fieldBranches ready).causal_rbr_knowledge_soundness ((proofSystem src).fieldBranchesSound ready) T source_rbr_knowledge_soundness sourceError_final

end GordieHowe.Falcon512.Ring.Native.ROMParams
