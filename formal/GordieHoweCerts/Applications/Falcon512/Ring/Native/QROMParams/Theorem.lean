-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.Falcon512.Ring.Native.QROMParams.Facts
public import GordieHoweCerts.Generated.Falcon512.Ring.Native.QROMParams.Certified
public import GordieHowe.Applications.Configuration.Certified
public import GordieHowe.Applications.Falcon512.Ring.Honest

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
open Generated.Falcon512.Ring.Native.QROMParams (interp ready ProofSystems certified sourceErrors)
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

/-- **The state function of `Π_P₀`'s round-by-round knowledge soundness** (`RealizedProgram.eventState`)
at the relation, the extractor's projection and the source challenges' event, the frontend's soundness
proofs as its argument. -/
abbrev sourceState :=
  program.eventState interp Ring.rel Ring.proj Ring.nativeEvent Ring.nativeEvent_use (Ring.sound_of_norm normSound)

/-- **Round-by-round knowledge soundness of `Π_P₀` for `Falcon512.Ring.Native.QROMParams`** at the ring
relation `Ring.rel`, the extractor `Ring.extractor` and the errors `511/q^20` at
`member.ring.gamma`, `1022/q^20` at `signature.r`, `0` elsewhere. -/
theorem source_rbr_knowledge_soundness :
    RBRKnowledgeSound Ring.rel (program.sourceVerifier interp) Ring.extractor
      sourceState
      (program.roundError interp (Ring.nativeEps (program := program) interp)) :=
  Ring.rbr_of_norm normSound

/-- **`Π_P₀`'s round errors vanish at `γ_end`.** -/
theorem sourceError_final :
    ∀ i, program.rounds.get i.1 = .final → program.roundError interp (Ring.nativeEps (program := program) interp) i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

/-- **The source challenge's error is within its fraction** (`sourceErrors`). -/
theorem nativeEps_le (j : ℕ) (hj : program.IsSourceChal j) :
    Ring.nativeEps (program := program) interp j ≤ ((sourceErrors j).1 : ℝ≥0) / (sourceErrors j).2 := by
  have hc : Fintype.card (interp 0).K = 12289 ^ 20 := by convert falconNativeField20_card <;> rfl
  rcases (FalconRandomPoint.isSourceChal_iff (program := program) j).1 hj with rfl | rfl
  · simp only [Ring.nativeEps, if_pos rfl, sourceErrors, hc]
    norm_num
  · have h1 : FalconRandomPoint.rChal program = 1 := rfl
    simp only [Ring.nativeEps, h1, sourceErrors, hc]
    norm_num

/-- **The source program's soundness of `Falcon512.Ring.Native.QROMParams`** (`Configuration.SourceFront`): the frontend's
round-by-round knowledge soundness (`source_rbr_knowledge_soundness`) at the ring's errors
(`Ring.nativeEps`, within `nativeEps_le`), and the honest nodes' `1` (`Ring.oneNodes`). -/
noncomputable def source :=
  ({ rel := Ring.rel,
     proj := Ring.proj,
     eps := Ring.nativeEps (program := program) interp,
     sound := source_rbr_knowledge_soundness,
     final := sourceError_final,
     eps_le := nativeEps_le,
     oneNodes := Ring.oneNodes } :
    Configuration.SourceFront certified Native.CoreWit _)

instantiate_config GordieHowe.Falcon512.Ring.Native.QROMParams
  from [GordieHowe.Configuration.CertifiedSource] certified source at proofSystem

end GordieHowe.Falcon512.Ring.Native.QROMParams
