-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.Frontend.Algebra
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.Frontend.Shape

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Native.QROMParams`

The native ML-DSA frontend at the native ML-DSA-44 program at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Native.QROMParams.Program.program`, export `c825eb05`): the program facts of
domain `A` (`MldsaABase`, `MldsaACross`, `MldsaAAlgebra`), decided here (domain `H`'s are in
`GordieHowe/Applications/MLDSA44/Native/QROMParams/Frontend/Shape.lean`); domain `A` over `F_q^11` (`MldsaQField fq11`), domain `H` over
`GF(2^256)`.
-/

namespace GordieHowe.MLDSA44.Native.QROMParams

open Generated.MLDSA44.Native.QROMParams.Program (program)
open ROMParams

set_option maxRecDepth 8192 in
/-- The native program at the QROM parameters has these facts. -/
instance : MldsaABase program where
  projReads := by shape_decide

set_option maxRecDepth 8192 in
/-- The native program at the QROM parameters has these facts. -/
instance : MldsaACross program where
  lt7 := by shape_decide
  expr7 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_mac_2eequal_2eshape_2eright_eq
  len63 := by shape_decide
  len60 := by shape_decide
  len525 := by shape_decide
  domainField0 := by shape_decide
  src272 := by shape_decide
  crossPred := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_mac_2eequal_body

set_option maxRecDepth 8192 in
/-- The native program at the QROM parameters has these facts. -/
instance : MldsaAAlgebra program where
  kind56 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_key_2ea_5fhat_kind
  kind57 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.value_key_2et1_kind
  lenWeight := by shape_decide
  pred0 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_signature_2erelation_body
  pred1 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_hint_2ew1_5fbound_body
  pred2 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_hint_2edecompose_body
  pred3 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_hint_2einterval_body
  pred11 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_norm_2ez_body
  pred12 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_hint_2eoffset_body
  pred13 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_hint_2eslack_body
  pred14 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.predicate_hint_5fweight_2eweight_body
  expr0 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_signature_2erelation_2eshape_2eleft_2efirst_2esecond_2efirst_2efirst_eq
  expr1 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_signature_2erelation_2eshape_2eleft_2esecond_2efirst_2efirst_eq
  expr2 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_hint_2einterval_2eshape_2eright_2efirst_2eshared_2esecond_2eshared_2efirst_eq
  expr3 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_hint_2edecompose_2eshape_2eleft_2efirst_2efirst_2esecond_2efirst_2efirst_2efirst_2efirst_2esecond_2efirst_eq
  expr4 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_hint_2einterval_2eshape_2eright_2efirst_2eshared_2efirst_2esecond_eq
  expr5 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_hint_2einterval_2eshape_2eright_2efirst_2eshared_2esecond_eq
  expr6 := Generated.MLDSA44.Native.QROMParams.ShapeFacts.expr_hint_2einterval_2eshape_2eright_2efirst_eq
  inSource_A := by
    shape_decide
  predicates_length := by shape_decide
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

end GordieHowe.MLDSA44.Native.QROMParams
