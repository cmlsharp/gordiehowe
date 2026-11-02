-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Carrier.Frontend
public import GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Structure
public import GordieHowe.Language.RealizedProgram.MemberValues
public import GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Interp

@[expose] public section

/-!
# GordieHowe: the frontend's program facts of `Falcon512.Ring.Carrier.ROMParams`

The program facts the Falcon ring frontend reads (the table's selection `GordieHowe.Falcon512.Ring.FalconRingPowers`,
`GordieHowe.Falcon512.Ring.FalconRingSelect`, `GordieHowe.Falcon512.Ring.FalconRingMember`, `GordieHowe.Falcon512.Ring.FalconCarrierBase`),
decided on the tables of `GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Program.program` (export
`5d775ae1`), and domain `A`'s field Goldilocks² (`GordieHowe.Falcon512.EField`).
-/

namespace GordieHowe.Falcon512.Ring.Carrier.ROMParams

open Generated.Falcon512.Ring.Carrier.ROMParams.Program
open Generated.Falcon512.Ring.Carrier.ROMParams (interp)
open Ring

/-- Every field of the program has characteristic `p`. -/
instance (n : ℕ) : ExpChar (interp.field n).K pGold :=
  inferInstanceAs (ExpChar GoldilocksExt2 pGold)

/-- Domain `A`'s field is Goldilocks². -/
instance : EField (interp 0) := inferInstanceAs (EField RealizedProgram.gold2)

/-- **The table's selection** (`member.signer`): the record `key.spectrum` (value `6`), the rows
`statement.ring` (value `4`), the natural-order transform of length `512` at `ψ = psiG`. -/
def tableShape : RealizedProgram.TableShape where
  dom := 0
  one := 0
  zero := 1
  mOne := mOneG
  gamma := 8
  chal := 0
  pow := 17
  dig := 18
  idx := 7
  pred := 0
  idxPred := 9
  record := .leaf 6
  map := [⟨true, true, 512, 0, psiG⟩]
  parts := [(4, 512)]
  rows := 64
  bits := 6

set_option maxRecDepth 100000 in
/-- **The table's selection**, decided on the program's tables. -/
instance : FalconRingPowers program where
  shape := tableShape
  refsOrdered := (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)
  exprs_pos := by decide +kernel
  values_pos := by decide +kernel
  mapWf := by decide +kernel
  width := by decide +kernel
  powOk := by decide +kernel
  digOk := by decide +kernel
  bodyOk := by decide +kernel
  powKind := rfl
  digKind := rfl
  idxBool := ⟨_, rfl⟩
  inSource := by decide +kernel
  consts := by decide +kernel
  gammaKind := rfl
  chalOk := by decide +kernel
  fields := by decide +kernel
  sizes := by decide +kernel
  idxPriv := rfl
  recordReads := by decide +kernel
  rowReads := by decide +kernel

/-- The selection's identifiers. -/
instance : FalconRingSelect program := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩⟩

set_option maxRecDepth 4096 in
theorem carrier_member : ∃ t, (program.predicate 0).body =
    .equal 0 (memberLhs 6 17 7 mOneG) (.leaf 1) t := ⟨_, rfl⟩

set_option maxRecDepth 4096 in
theorem carrier_idxBool :
    ∃ t, (program.predicate 9).body = .equal 0 (.mul (.leaf 7) (.leaf 7)) (.leaf 7) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- The membership's facts: the ring `4`, the challenge `5`, the spectrum `6`, `s2` `9`, the powers
`17`, the zero constant `1`, `ψ = psiG`, `−1 = p − 1`, the index bits' check `9`. -/
instance : FalconRingMember program where
  ring := 4
  spec := 6
  pow := 17
  zero := 1
  psi := psiG
  mOne := mOneG
  idxPred := 9
  chal := 5
  s2 := 9
  domainField0 := by decide +kernel
  member := carrier_member
  idxBool := carrier_idxBool
  inSource := by decide +kernel
  consts := by decide +kernel
  table := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
/-- **`signature.equation`**: the spectral product form of `c − s1 ≡ h · s2 (mod q)`. -/
theorem carrier_sig : ∃ real, (program.predicate 4).body = .mod 0 12289 carrierSigP carrierSigN real ∧
    real.form = .spectralProduct ∧ real.quotient = some (.leaf 11) ∧
    real.quotientLo = -6291457 ∧ real.qmax = 12570625 :=
  ⟨_, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- The carrier's facts outside the membership. -/
instance : FalconCarrierBase program where
  ids := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  sig := carrier_sig
  magS1 := ⟨_, rfl⟩
  magS2 := ⟨_, rfl⟩
  normSum := ⟨_, rfl⟩
  rMag1 := ⟨_, rfl⟩
  rMag2 := ⟨_, rfl⟩
  rLow2 := ⟨_, rfl⟩
  rBudget := ⟨_, rfl⟩
  rNorm := ⟨_, rfl⟩
  rQuot := ⟨_, rfl⟩
  high2 := ⟨_, rfl, rfl⟩
  inSource := by decide +kernel
  consts := by decide +kernel
  fields := by decide +kernel
  sizes := by decide +kernel
  privKinds := ⟨rfl, rfl, rfl⟩
  ringCheck := by
    obtain ⟨m, hm, v, hv, hp⟩ := RealizedProgram.exists_check_of_ptr (ir := program)
      (S := Generated.Falcon512.Ring.Carrier.ROMParams.Structure.records) (k := 0)
      (p := fun m v => v == 4 && m.entryBound? == some 12289)
        (by decide +kernel) (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨m, hm, hp.1 ▸ hv, hp.2⟩
  chalCheck := by
    obtain ⟨m, hm, v, hv, hp⟩ := RealizedProgram.exists_check_of_ptr (ir := program)
      (S := Generated.Falcon512.Ring.Carrier.ROMParams.Structure.records) (k := 1)
      (p := fun m v => v == 5 && m.entryBound? == some 12289)
        (by decide +kernel) (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨m, hm, hp.1 ▸ hv, hp.2⟩

end GordieHowe.Falcon512.Ring.Carrier.ROMParams
