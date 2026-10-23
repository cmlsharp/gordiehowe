-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.FieldInterps.GF256
public import GordieHowe.Foundations.Algebra.RelativePackingAdditive
public import GordieHowe.Language.Export.Valid
public import GordieHowe.Foundations.Fields.GF2_256Relative
public import GordieHowe.Foundations.Fields.GF2_256Dual
public import GordieHowe.Foundations.Fields.GF2_256Skip
public import GordieHowe.Applications.Falcon512.Ring.Carrier.QROMParams.Interp
public import GordieHowe.Foundations.ToMathlib.NNRealDyadic
public import GordieHowe.Applications.Shared.Tableaux
public import GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Program
public import GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Plan
public import GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Valid
public import GordieHowe.ProofSystem.Program.FieldHonest
public import GordieHowe.ProofSystem.Program.FieldPackings

@[expose] public section

/-!
# GordieHowe: the interpretation and domain `H` of `MLDSA44.Emulated.QROMParams`

The interpretation of the realized program of the emulated ML-DSA-44 proof of possession at the
QROM parameters
(`GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Program.program`) and its domain `H`'s circuit `c.H` with its
nodes:

* **the interpretation** (`interp`, `GordieHowe.RealizedProgram.mldsaQROMInterp`): field `0` is Goldilocks⁴
  (`GordieHowe.RealizedProgram.gold4`), field `1` is `GF(2^256)` (`gf256`,
  `GordieHowe/Applications/FieldInterps/GF256.lean`).

* **domain `H`'s ready data** (`readyH`, `GordieHowe.RealizedProgram.FieldReady`): the packing `gf256Packing` and the
  tableau `gf256K339R2Cert` with the checks `fieldOkH` by `decide +kernel`, from which domain `H`'s
  proof is the generic per-field one (`GordieHowe.RealizedProgram.fieldProof`).
-/

namespace GordieHowe.MLDSA44.Emulated.QROMParams.HashField

open RealizedProgram.Export RelativePacking Ligero.MaskRow
open Generated.MLDSA44.Emulated.QROMParams.Program (program)
open scoped NNReal

/-! ## The interpretation -/

/-- **The interpretation of the program of `MLDSA44.Emulated.QROMParams`**: field `0` is Goldilocks⁴
(`RealizedProgram.gold4`), field `1` (and any other identifier) `GF(2^256)`; the opaque
functions `targetBitsFn`. -/
abbrev interp : RealizedProgram.Interp := RealizedProgram.mldsaQROMInterp RealizedProgram.gold4

/-! ## Domain `H`'s ready data -/

/-- Domain `H`'s packing facts. -/
abbrev fieldPkH : (interp.field (program.domainField 1)).Packing := RealizedProgram.gf256Packing

/-- **Domain `H`'s checks** (`RealizedProgram.fieldOkB`). -/
theorem fieldOkH : program.fieldOkB (I := interp) 1 Generated.MLDSA44.Emulated.QROMParams.Plan.plan fieldPkH
    RealizedProgram.gf256K339R2Cert = true := by
  decide +kernel

/-- **Domain `H`'s ready data** (`RealizedProgram.FieldReady`). -/
def readyH :
    program.FieldReady interp 1 Generated.MLDSA44.Emulated.QROMParams.Plan.plan :=
  ⟨fieldPkH, RealizedProgram.gf256K339R2Cert, fieldOkH, Generated.MLDSA44.Emulated.QROMParams.Valid.wellFormed⟩

end GordieHowe.MLDSA44.Emulated.QROMParams.HashField
