-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.FieldInterps.Odd
public import GordieHowe.Applications.FieldInterps.GF256
public import GordieHowe.Foundations.Algebra.RelativePackingAdditive
public import GordieHowe.Language.Export.Valid
public import GordieHowe.Foundations.Fields.GF2_256Relative
public import GordieHowe.Foundations.Fields.GF2_256Dual
public import GordieHowe.Foundations.Fields.GF2_256Skip
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11
public import GordieHowe.Foundations.ToMathlib.NNRealDyadic
public import GordieHowe.Applications.Shared.Tableaux
public import GordieHowe.Generated.MLDSA44.Native.QROMParams.Program
public import GordieHowe.Generated.MLDSA44.Native.QROMParams.Plan

@[expose] public section

/-!
# GordieHowe: the interpretation of `MLDSA44.Native.QROMParams`

The interpretation of the realized program of the native ML-DSA-44 proof of possession at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Native.QROMParams.Program.program`, export `c825eb05`: domains `A` over `F_q^11`
and `H` over `GF(2^256)`) and its circuit `c.H`; domain `H`'s circuit proof is the generic per-field
domain proof (`GordieHowe.MLDSA44.Native.QROMParams.readyH`, `GordieHowe/Applications/MLDSA44/Native/QROMParams/ProofSystem.lean`):

* **the interpretation** (`interp`, `GordieHowe.RealizedProgram.mldsaQROMInterp`): field `0` is `F_q^11` (`fq11`), field `1` is
  `GF(2^256)` (`gf256`, `GordieHowe/Applications/FieldInterps/GF256.lean`).
-/

namespace GordieHowe.MLDSA44.Native.QROMParams.HashField

open RealizedProgram.Export
open Generated.MLDSA44.Native.QROMParams.Program (program)

/-! ## The interpretation -/

/-- **The interpretation of the native ML-DSA program at the QROM parameters**: field `0` is `F_q^11`, field `1`
(and any other identifier) `GF(2^256)`; the opaque functions `targetBitsFn`. -/
abbrev interp : RealizedProgram.Interp := RealizedProgram.mldsaQROMInterp RealizedProgram.fq11

end GordieHowe.MLDSA44.Native.QROMParams.HashField
