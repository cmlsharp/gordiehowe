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

/-- **The digit layout of `MLDSA44.Emulated.ROMParams`**: `w'` in three base-`256` digits
(`577`–`579`), `z + 130993`, the offset and the slack in two base-`645` digits each (`580`, `581`;
`585`, `586`; `587`, `588`); the offset's and the slack's bound `645^2`. -/
def layout : Emulated.MldsaELayout where
  w := ⟨256, [577, 578, 579]⟩
  z := ⟨645, [580, 581]⟩
  offset := ⟨645, [585, 586]⟩
  slack := ⟨645, [587, 588]⟩
  offsetBound := 416025

set_option maxRecDepth 4096 in
/-- The emulated program at the ROM parameters has domain `A`'s facts. -/
instance : Emulated.MldsaEAlgebra program where
  layout := layout
  offsetBound_lt := by decide
  lenWeight := by shape_decide
  lenSigL := by shape_decide
  pred0 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.predicate_hint_2ew1_5fbound_body
  pred1 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.predicate_hint_2edecompose_body
  pred2 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.predicate_hint_2einterval_body
  pred11 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.predicate_signature_2ew_body
  pred12 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.predicate_norm_2ez_body
  pred13 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.predicate_hint_2eoffset_body
  pred14 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.predicate_hint_2eslack_body
  pred15 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.predicate_hint_5fweight_2eweight_body
  pred274 := by
    obtain ⟨r, h, hf, -⟩ := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.predicate_signature_2erelation_2esource_body
    exact ⟨r, h, by rw [hf]; rfl⟩
  expr7 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.expr_signature_2erelation_2eshape_2eleft_2efirst_2esecond_2efirst_2efirst_eq
  expr8 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.expr_signature_2erelation_2eshape_2eleft_2esecond_2efirst_2efirst_eq
  expr0 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.expr_hint_2einterval_2eshape_2eright_2efirst_2eshared_2esecond_2eshared_2efirst_eq
  expr1 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.expr_hint_2edecompose_2eshape_2eleft_2efirst_2eshared_2efirst_2efirst_2esecond_2efirst_2efirst_2efirst_2efirst_2esecond_2efirst_eq
  expr2 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.expr_hint_2einterval_2eshape_2eright_2efirst_2eshared_2efirst_2esecond_eq
  expr3 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.expr_hint_2einterval_2eshape_2eright_2efirst_2eshared_2esecond_eq
  expr4 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.expr_hint_2einterval_2eshape_2eright_2efirst_eq
  expr5 := Generated.MLDSA44.Emulated.ROMParams.ShapeFacts.expr_hint_2edecompose_2eshape_2eleft_2efirst_eq
  inSource_A := by
    shape_decide
  lensA := by
    shape_decide
  boolChecks := by
    shape_decide
  constsA := by
    shape_decide
  constsU := by
    shape_decide
  refsA := by shape_decide
  lensU := by
    shape_decide
  valsU := by
    shape_decide
  sigData := by
    shape_decide
  boundZW := by
    shape_decide

/-- **Domain `A`'s obligation** (`Emulated.algebraSound`). -/
theorem algebraSound : AlgebraSound := Emulated.algebraSound

end GordieHowe.MLDSA44.Emulated.ROMParams
