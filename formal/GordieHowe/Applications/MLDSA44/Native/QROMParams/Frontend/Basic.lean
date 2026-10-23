-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Algebra
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
  projReads := by decide +kernel

set_option maxRecDepth 8192 in
/-- The native program at the QROM parameters has these facts. -/
instance : MldsaACross program where
  const6 := by decide +kernel
  entries6 := by decide +kernel
  field6 := by decide +kernel
  lt7 := by decide +kernel
  expr7 := rfl
  len63 := by decide +kernel
  len60 := by decide +kernel
  len525 := by decide +kernel
  domainField0 := by decide +kernel
  src272 := ⟨by decide +kernel, by decide +kernel⟩
  crossPred := ⟨_, rfl⟩

set_option maxRecDepth 8192 in
/-- The native program at the QROM parameters has these facts. -/
instance : MldsaAAlgebra program where
  kind56 := rfl
  kind57 := rfl
  lenWeight := by decide +kernel
  pred0 := rfl
  pred1 := rfl
  pred2 := rfl
  pred3 := rfl
  pred6 := rfl
  pred7 := rfl
  pred8 := rfl
  pred9 := rfl
  pred11 := rfl
  pred12 := rfl
  pred13 := rfl
  pred14 := rfl
  expr0 := rfl
  expr1 := rfl
  expr2 := rfl
  expr3 := rfl
  expr4 := rfl
  expr5 := rfl
  expr6 := rfl
  inSource_A := by
    decide +kernel
  predicates_length := by decide +kernel
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

end GordieHowe.MLDSA44.Native.QROMParams
