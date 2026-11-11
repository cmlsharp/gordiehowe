-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.Falcon512.Ring.Carrier.QROMParams.Certified
public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.Applications.Configuration.Certified
public import GordieHowe.Applications.Falcon512.Ring.Honest
public import GordieHoweCerts.Applications.Falcon512.Ring.Carrier.QROMParams.Facts

@[expose] public section

/-!
# GordieHowe: the theorem at the realized program for `Falcon512.Ring.Carrier.QROMParams`

The frontend's round-by-round knowledge soundness of `Π_P₀` at the Falcon ring relation
(`GordieHowe.Falcon512.Ring.rbr_carrier`: the relation `GordieHowe.Falcon512.Ring.rel` at the statement's ring and challenge, the
extractor `GordieHowe.Falcon512.Ring.proj`, the errors `511/p^4` at `member.ring.gamma` and `1022/p^4` at
`signature.r`), composed with the
proof system (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked domains of `proofSystem`).
-/

namespace GordieHowe.Falcon512.Ring.Carrier.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP
open Generated.Falcon512.Ring.Carrier.QROMParams.Program (program)
open Generated.Falcon512.Ring.Carrier.QROMParams (interp ready ProofSystems certified sourceErrors)
open scoped NNReal

/-- **The proof system of `Falcon512.Ring.Carrier.QROMParams`**
(`GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.proofSystem`): the generic per-field
proof system at the certificates' sources, whose circuits enforce their entries and accept the
honest inputs by the certificates, at the selections' soundness from the program check. -/
abbrev proofSystem : ProofSystems :=
  Generated.Falcon512.Ring.Carrier.QROMParams.proofSystem

/-- **The state function of `Π_P₀`'s round-by-round knowledge soundness** (`RealizedProgram.eventState`)
at the relation, the extractor's projection and the source challenges' event, the frontend's soundness
proofs as its argument. -/
abbrev sourceState :=
  program.eventState interp Ring.rel Ring.proj Ring.carrierEvent Ring.carrierEvent_use Ring.sound_carrier

/-- **Round-by-round knowledge soundness of `Π_P₀` for `Falcon512.Ring.Carrier.QROMParams`** at the ring
relation `Ring.rel`, the extractor `Ring.extractor` and the errors `511/p^4` at
`member.ring.gamma`, `1022/p^4` at `signature.r`, `0` elsewhere. -/
theorem source_rbr_knowledge_soundness :
    RBRKnowledgeSound Ring.rel (program.sourceVerifier interp) Ring.extractor
      sourceState
      (program.roundError interp (Ring.carrierEps interp)) :=
  Ring.rbr_carrier

/-- **`Π_P₀`'s round errors vanish at `γ_end`.** -/
theorem sourceError_final :
    ∀ i, program.rounds.get i.1 = .final →
      program.roundError interp (Ring.carrierEps interp) i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

/-- **The source challenge's error is within its fraction** (`sourceErrors`). -/
theorem carrierEps_le (j : ℕ) (hj : program.IsSourceChal j) :
    Ring.carrierEps interp j ≤ ((sourceErrors j).1 : ℝ≥0) / (sourceErrors j).2 := by
  have hc : Fintype.card (interp 0).K = pGold ^ 4 := by convert goldilocksExt4_card <;> rfl
  rcases (Ring.isSourceChal_iff_carrier (program := program) j).1 hj with rfl | rfl
  · simp only [Ring.carrierEps, if_pos rfl, sourceErrors, hc]
    norm_num [pGold]
  · simp only [Ring.carrierEps, one_ne_zero, if_false, if_pos rfl, sourceErrors, hc]
    norm_num [pGold]

/-- Domain `A`'s node `GF(p^1)` is the prime subfield `F_p`. -/
instance : Ring.PrimeNode (interp 0) :=
  ⟨⟨RelativePacking.fixedField _ pGold 1, fun x => by
    change x ∈ RealizedProgram.gold4Node "GF(p^1)" ↔ _
    rw [RealizedProgram.gold4Node, if_pos rfl]
    rfl⟩⟩

/-- **The source program's soundness of `Falcon512.Ring.Carrier.QROMParams`** (`Configuration.SourceFront`): the frontend's
round-by-round knowledge soundness (`source_rbr_knowledge_soundness`) at the carrier's errors
(`Ring.carrierEps`, within `carrierEps_le`), and the honest nodes' `1` (`Ring.oneNodes`). -/
noncomputable def source :=
  ({ rel := Ring.rel,
     proj := Ring.proj,
     eps := Ring.carrierEps interp,
     sound := source_rbr_knowledge_soundness,
     final := sourceError_final,
     eps_le := carrierEps_le,
     oneNodes := Ring.oneNodes } :
    Configuration.SourceFront certified Native.CoreWit _)

instantiate_config GordieHowe.Falcon512.Ring.Carrier.QROMParams
  from [GordieHowe.Configuration.CertifiedSource] certified source at proofSystem

end GordieHowe.Falcon512.Ring.Carrier.QROMParams
