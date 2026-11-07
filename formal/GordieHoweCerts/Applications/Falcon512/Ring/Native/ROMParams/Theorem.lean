-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.Falcon512.Ring.Native.ROMParams.Facts
public import GordieHoweCerts.Generated.Falcon512.Ring.Native.ROMParams.Certified
public import GordieHowe.Applications.Configuration.Certified
public import GordieHowe.Applications.Falcon512.Ring.Honest

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
open Generated.Falcon512.Ring.Native.ROMParams (interp ready ProofSystems certified sourceErrors)
open scoped NNReal

/-- **The proof system of `Falcon512.Ring.Native.ROMParams`**
(`GordieHowe.Generated.Falcon512.Ring.Native.ROMParams.proofSystem`): the generic per-field proof
system at the certificates' sources, whose circuits enforce their entries and accept the honest
inputs by the certificates. -/
abbrev proofSystem : ProofSystems :=
  Generated.Falcon512.Ring.Native.ROMParams.proofSystem

/-- **The norm's obligation** (`Ring.NormSound`): the generic norm's advice
(`Norm.algOf` at the slack's high digit) wherever the source program holds. -/
theorem normSound : Ring.NormSound (program := program) (I := interp) := fun e hs => by
  obtain ⟨k, hk, hkv⟩ := Norm.slack_below (program := program) (I := interp) hs
  exact ⟨Norm.algOf e ((k / 64 : ℕ) : _), fun _ => rfl, Norm.normHolds hs _,
    Norm.encodingBits hs _, ⟨Norm.digitsBelow hs, Norm.encodingRequests hs hk hkv⟩⟩

/-- **Round-by-round knowledge soundness of `Π_P₀` for `Falcon512.Ring.Native.ROMParams`** at the ring
relation `Ring.rel`, the extractor `Ring.extractor` and the errors `511/q^9` at
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

/-- **The source challenge's error is within its fraction** (`sourceErrors`). -/
theorem ringEps_le (j : ℕ) (_ : program.IsSourceChal j) :
    Ring.ringEps interp j ≤ ((sourceErrors j).1 : ℝ≥0) / (sourceErrors j).2 := by
  unfold Ring.ringEps
  simp only [sourceErrors]
  split_ifs
  · rw [show Fintype.card _ = 12289 ^ 9 from by convert falconNativeField_card <;> rfl]
    norm_num
  · exact zero_le'

/-- **The source program's soundness of `Falcon512.Ring.Native.ROMParams`** (`Configuration.SourceFront`): the frontend's
round-by-round knowledge soundness (`source_rbr_knowledge_soundness`) at the ring's errors
(`Ring.ringEps`, within `ringEps_le`), and the honest nodes' `1` (`Ring.oneNodes`). -/
noncomputable def source :=
  ({ rel := Ring.rel,
     proj := Ring.proj,
     eps := Ring.ringEps interp,
     sound := source_rbr_knowledge_soundness,
     final := sourceError_final,
     eps_le := ringEps_le,
     oneNodes := Ring.oneNodes } :
    Configuration.SourceFront certified Native.CoreWit _)

instantiate_config GordieHowe.Falcon512.Ring.Native.ROMParams
  from [GordieHowe.Configuration.CertifiedSource] certified source at proofSystem

end GordieHowe.Falcon512.Ring.Native.ROMParams
