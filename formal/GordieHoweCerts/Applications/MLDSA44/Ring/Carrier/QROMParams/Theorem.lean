-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.Certified
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.QROMParams.Frontend.Front
public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.Applications.Configuration.Certified
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.HonestFull
public import GordieHoweCerts.Applications.MLDSA44.Honest.SampleInBall

@[expose] public section

/-!
# GordieHowe: the theorem at the realized program for `MLDSA44.Ring.Carrier.QROMParams`

The frontend's round-by-round knowledge soundness of `Π_P₀` at the ML-DSA-44 ring carrier relation
(`GordieHowe.MLDSA44.Ring.Carrier.QROMParams.source_rbr_knowledge_soundness`: the relation
`GordieHowe.MLDSA44.Ring.Carrier.rel` at every checked ring statement whose rows the statement
holds, the extractor `GordieHowe.MLDSA44.Ring.Carrier.extractor`, the errors `sourceEps`:
`5143/|Goldilocks^4|` at `member.table.gamma`, `2040/|Goldilocks^4|` at `signature.r`, SampleInBall's `264/2^256` and `295/2^256` at
the ring's challenges `2` and `3`), composed with the proof system
(`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness` at the forked
domains of `proofSystem`) in `iop_rbr_knowledge_soundness`. Circuit enforcement
follows from the generated certificates.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.QROMParams

open RealizedProgram RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP
open Generated.MLDSA44.Ring.Carrier.QROMParams.Program (program)
open Generated.MLDSA44.Ring.Carrier.QROMParams (interp ready ProofSystems certified sourceErrors)
open scoped NNReal

/-- **The proof system of `MLDSA44.Ring.Carrier.QROMParams`**
(`GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.proofSystem`): the generic per-field proof
system at the certificates' sources, whose circuits enforce their entries and accept the honest
inputs by the certificates, at the selections' soundness from the program check. -/
abbrev proofSystem : ProofSystems :=
  Generated.MLDSA44.Ring.Carrier.QROMParams.proofSystem

/-- **The round errors of `Π_P₀`'s challenges** (`Carrier.ringEps` at SampleInBall's view
`MLDSA44.sampleView`): `5143/|Goldilocks^4|` at `member.table.gamma` (challenge `0`),
`2040/|Goldilocks^4|` at `signature.r` (challenge `1`), `264/2^256` and `295/2^256` at the ring's
challenges `2` and `3`. -/
noncomputable abbrev sourceEps : ℕ → ℝ≥0 :=
  Carrier.ringEps (program := program) (F0 := RealizedProgram.gold4) (FH := RealizedProgram.gf256)
    MLDSA44.sampleView

/-- **`Π_P₀`'s round errors vanish at `γ_end`**: they are the view's errors at a challenge round,
`0` at every other round. -/
theorem sourceError_final (ε : ℕ → ℝ≥0) :
    ∀ i, program.rounds.get i.1 = .final → program.roundError interp ε i = 0 := by
  intro i hi
  simp only [RealizedProgram.roundError, hi]

/-- **The source challenges' errors are within their fractions** (`sourceErrors`). -/
theorem sourceEps_le (j : ℕ) (_ : program.IsSourceChal j) :
    sourceEps j ≤ ((sourceErrors j).1 : ℝ≥0) / (sourceErrors j).2 := by
  have hc : Fintype.card (interp 0).K = pGold ^ 4 := by convert goldilocksExt4_card <;> rfl
  rcases j with _ | _ | _ | _ | j
  · change ((5143 : ℕ) : ℝ≥0) / Fintype.card (interp 0).K ≤ _
    rw [hc]
    simp only [sourceErrors, ↓reduceIte]
    norm_num [pGold]
  · change ((2040 : ℕ) : ℝ≥0) / Fintype.card (interp 0).K ≤ _
    rw [hc]
    simp only [sourceErrors, ↓reduceIte]
    norm_num [pGold]
  · change MLDSA44.sampleEpsOf 256 0 ≤ _
    norm_num [MLDSA44.sampleEpsOf, sourceErrors]
  · change MLDSA44.sampleEpsOf 256 1 ≤ _
    norm_num [MLDSA44.sampleEpsOf, sourceErrors]
  · change MLDSA44.sampleEpsOf 256 (j + 2) ≤ _
    simp [MLDSA44.sampleEpsOf]

/-- **The source program's soundness of `MLDSA44.Ring.Carrier.QROMParams`** (`Configuration.SourceFront`): the frontend's
round-by-round knowledge soundness (`source_rbr_knowledge_soundness`) at the source challenges'
errors (`sourceEps`, within `sourceEps_le`), and the honest nodes' `1`. -/
noncomputable def source :=
  ({ rel := Carrier.rel (program := program) (F0 := RealizedProgram.gold4) (FH := RealizedProgram.gf256),
     proj := proj,
     eps := sourceEps,
     sound := source_rbr_knowledge_soundness,
     final := sourceError_final sourceEps,
     eps_le := sourceEps_le,
     oneNodes := Carrier.oneNodes } :
    Configuration.SourceFront certified Native.RingW _)

instantiate_config GordieHowe.MLDSA44.Ring.Carrier.QROMParams
  from [GordieHowe.Configuration.CertifiedSource] renaming forkLowering → ringLowering
  certified source at proofSystem

end GordieHowe.MLDSA44.Ring.Carrier.QROMParams
