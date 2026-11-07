-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Emulated.ROMParams.Frontend.Basic
public import GordieHoweCerts.Applications.MLDSA44.Emulated.Frontend.Cross
public import GordieHoweCerts.Generated.MLDSA44.Emulated.ROMParams.ShapeFacts

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Emulated.ROMParams`, the crossing

The emulated frontend's crossing (`GordieHowe.MLDSA44.Emulated.crossSound`, `GordieHoweCerts/Applications/MLDSA44/Emulated/Frontend/Cross.lean`) at
the emulated program at the ROM parameters: its program facts (`GordieHowe.MLDSA44.Emulated.MldsaECross`, decided here).
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open Generated.MLDSA44.Emulated.ROMParams.Program

set_option maxRecDepth 4096 in
/-- The emulated program at the ROM parameters has the crossing's facts. -/
instance : Emulated.MldsaECross program where
  expr6 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eright_eq
  refsOrdered := Generated.MLDSA44.Emulated.ROMParams.conditions.wellFormed.refsOrdered
  crossData := by
    shape_decide
  crossPred := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.predicate_mac_2eequal_body

/-- **`mac.equal` gives the crossing** (`Emulated.crossSound`). -/
theorem crossSound : CrossSound := Emulated.crossSound

end GordieHowe.MLDSA44.Emulated.ROMParams
