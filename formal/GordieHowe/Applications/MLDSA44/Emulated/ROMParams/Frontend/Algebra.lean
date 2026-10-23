-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.Frontend.Cross
public import GordieHowe.Applications.MLDSA44.Emulated.Frontend.Algebra

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Emulated.ROMParams`, domain `A`

Domain `A` of the emulated frontend (`GordieHowe.MLDSA44.Emulated.algebraSound`,
`GordieHowe/Applications/MLDSA44/Emulated/Frontend/Algebra.lean`) at the emulated program at the ROM parameters: its digit
layout (`layout`) and its program facts (`GordieHowe.MLDSA44.Emulated.MldsaEAlgebra`, decided here).
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open Generated.MLDSA44.Emulated.ROMParams.Program
open HashField (interp)

/-- **The digit layout of `MLDSA44.Emulated.ROMParams`**: `w'` in three base-`256` digits
(`578`–`580`), `z + 130993`, the offset and the slack in two base-`645` digits each (`581`, `582`;
`586`, `587`; `588`, `589`); the offset's and the slack's bound `645^2`. -/
def layout : Emulated.MldsaELayout where
  w := ⟨256, [578, 579, 580]⟩
  z := ⟨645, [581, 582]⟩
  offset := ⟨645, [586, 587]⟩
  slack := ⟨645, [588, 589]⟩
  offsetBound := 416025

set_option maxRecDepth 4096 in
/-- The emulated program at the ROM parameters has domain `A`'s facts. -/
instance : Emulated.MldsaEAlgebra program where
  layout := layout
  offsetBound_lt := by decide
  lenWeight := by decide +kernel
  lenSigL := by decide +kernel
  pred0 := rfl
  pred1 := rfl
  pred2 := rfl
  pred11 := ⟨_, rfl⟩
  pred12 := ⟨_, rfl⟩
  pred13 := ⟨_, rfl⟩
  pred14 := ⟨_, rfl⟩
  pred15 := ⟨_, rfl⟩
  pred274 := ⟨_, rfl⟩
  expr7 := rfl
  expr8 := rfl
  expr0 := rfl
  expr1 := rfl
  expr2 := rfl
  expr3 := rfl
  expr4 := rfl
  expr5 := rfl
  inSource_A := by
    decide +kernel
  lensA := by
    decide +kernel
  boolChecks := by
    decide +kernel
  constsA := by
    decide +kernel
  constsU := by
    decide +kernel
  refsA := by decide +kernel
  lensU := by
    decide +kernel
  valsU := by
    decide +kernel
  sigData := by
    decide +kernel
  boundZW := by
    decide +kernel

/-- **Domain `A`'s obligation** (`Emulated.algebraSound`). -/
theorem algebraSound : AlgebraSound := Emulated.algebraSound

end GordieHowe.MLDSA44.Emulated.ROMParams
