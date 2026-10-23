-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.Frontend.Basic
public import GordieHowe.Applications.MLDSA44.Emulated.Frontend.Cross

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Emulated.ROMParams`, the crossing

The emulated frontend's crossing (`GordieHowe.MLDSA44.Emulated.crossSound`, `GordieHowe/Applications/MLDSA44/Emulated/Frontend/Cross.lean`) at
the emulated program at the ROM parameters: its program facts (`GordieHowe.MLDSA44.Emulated.MldsaECross`, decided here).
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open Generated.MLDSA44.Emulated.ROMParams.Program
open HashField (interp)

set_option maxRecDepth 4096 in
/-- The emulated program at the ROM parameters has the crossing's facts. -/
instance : Emulated.MldsaECross program where
  expr6 := rfl
  refsOrdered := (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)
  crossData := by
    decide +kernel
  crossPred := ⟨_, rfl⟩

/-- **`mac.equal` gives the crossing** (`Emulated.crossSound`). -/
theorem crossSound : CrossSound := Emulated.crossSound

end GordieHowe.MLDSA44.Emulated.ROMParams
