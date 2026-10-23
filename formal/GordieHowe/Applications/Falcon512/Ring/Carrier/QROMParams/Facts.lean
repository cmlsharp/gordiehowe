-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Carrier.QROMParams.ProofSystem
public import GordieHowe.Applications.Falcon512.Ring.Carrier.Frontend

@[expose] public section

/-!
# GordieHowe: the frontend's program facts of `Falcon512.Ring.Carrier.QROMParams`

The program facts the Falcon ring frontend reads (`GordieHowe.Falcon512.Ring.FalconRingPowers`,
`GordieHowe.Falcon512.Ring.FalconRingSelect`, `GordieHowe.Falcon512.Ring.FalconRingMember`, `GordieHowe.Falcon512.Ring.FalconCarrierBase`),
decided on the tables of `GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.Program.program` (export
`b65a4929`), and domain `A`'s field Goldilocks⁴ (`GordieHowe.Falcon512.EField`).
-/

namespace GordieHowe.Falcon512.Ring.Carrier.QROMParams

open Generated.Falcon512.Ring.Carrier.QROMParams.Program
open Ring

/-- Domain `A`'s field is Goldilocks⁴. -/
instance : EField (interpQROM 0) := inferInstanceAs (EField RealizedProgram.gold4)

set_option maxRecDepth 4096 in
/-- The challenge powers: the constant `1` (value `0`) and `γ` (value `9`). -/
instance : FalconRingPowers program where
  one := 0
  gamma := 9
  refsOrdered := (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)
  exprs_length := by decide +kernel
  expr0 := rfl
  expr1 := rfl
  exprEven m hm := by
    simp only [List.mem_range'_1] at hm
    obtain ⟨h1, h2⟩ := hm
    interval_cases m <;> rfl
  exprOdd m hm := by
    simp only [List.mem_range'_1] at hm
    obtain ⟨h1, h2⟩ := hm
    interval_cases m <;> rfl
  expr15 := rfl
  size0 := by decide +kernel

set_option maxRecDepth 4096 in
/-- The selection: the index bits `8` and the digests `19`. -/
instance : FalconRingSelect program where
  idx := 8
  dig := 19
  refsOrdered := (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)
  exprs_length := by decide +kernel
  expr16 := rfl
  exprSel t ht := by
    simp only [List.mem_range'_1] at ht
    obtain ⟨h1, h2⟩ := ht
    interval_cases t <;> rfl

set_option maxRecDepth 4096 in
theorem carrier_member : ∃ t, (program.predicate 0).body =
    .equal 0 (memberLhs 7 18 8 mOneG) (.leaf 1) t := ⟨_, rfl⟩

set_option maxRecDepth 4096 in
theorem carrier_idxBool :
    ∃ t, (program.predicate 9).body = .equal 0 (.mul (.leaf 8) (.leaf 8)) (.leaf 8) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- The membership's facts: the ring `5`, the challenge `6`, the spectrum `7`, `s2` `10`, the powers
`18`, the zero constant `1`, `ψ = psiG`, `−1 = p − 1`, the index bits' check `9`. -/
instance : FalconRingMember program where
  ring := 5
  spec := 7
  pow := 18
  zero := 1
  psi := psiG
  mOne := mOneG
  idxPred := 9
  chal := 6
  s2 := 10
  domainField0 := by decide +kernel
  member := carrier_member
  idxBool := carrier_idxBool
  inSource := by decide +kernel
  powersKind := rfl
  digestsKind := rfl
  consts := by decide +kernel
  gammaKind := rfl
  ringKind := rfl
  chalKind := rfl
  chal_ne_ring := by decide
  fields := by decide +kernel
  sizes := by decide +kernel
  chal0 := by decide +kernel
  isSourceChal_iff := fun j => by
    constructor
    · intro h
      have hj : j < 2 := h.1
      have key : ∀ j < 2, program.IsSourceChal j → j = 0 := by decide +kernel
      exact key j hj h
    · rintro rfl
      decide +kernel
  values_length := by decide +kernel
  privKinds := ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
theorem carrier_sig : ∃ t, (program.predicate 1).body = .equal 0 carrierSigLhs (.leaf 3) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- The carrier's facts outside the membership. -/
instance : FalconCarrierBase program where
  ids := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  sig := carrier_sig
  magS1 := ⟨_, rfl⟩
  magS2 := ⟨_, rfl⟩
  normSum := ⟨_, rfl⟩
  rQuot := ⟨_, rfl⟩
  rMag1 := ⟨_, rfl⟩
  rMag2 := ⟨_, rfl⟩
  rLow2 := ⟨_, rfl⟩
  rBudget := ⟨_, rfl⟩
  rNorm := ⟨_, rfl⟩
  high2 := ⟨_, rfl⟩
  inSource := by decide +kernel
  consts := by decide +kernel
  fields := by decide +kernel
  sizes := by decide +kernel
  privKinds := ⟨rfl, rfl⟩
  ringCheck := by decide +kernel
  chalCheck := by decide +kernel

end GordieHowe.Falcon512.Ring.Carrier.QROMParams
