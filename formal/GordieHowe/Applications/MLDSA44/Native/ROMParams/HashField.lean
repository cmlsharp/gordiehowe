-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.FieldInterps.Odd
public import GordieHowe.Applications.MLDSA44.Interp
public import GordieHowe.Foundations.Algebra.RelativePackingAdditive
public import GordieHowe.Language.Export.Valid
public import GordieHowe.Foundations.Fields.GF2_128Relative
public import GordieHowe.Foundations.Fields.GF2_128Dual
public import GordieHowe.Foundations.Fields.GF2_128Skip
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6
public import GordieHowe.Foundations.ToMathlib.NNRealDyadic
public import GordieHowe.Applications.Shared.Tableaux
public import GordieHowe.Generated.MLDSA44.Native.ROMParams.Program
public import GordieHowe.Generated.MLDSA44.Native.ROMParams.Plan

@[expose] public section

/-!
# GordieHowe: the interpretation of `MLDSA44.Native.ROMParams`

The interpretation of the realized program of the native ML-DSA-44 proof of possession at the ROM parameters
(`GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.program`, export `c825eb05`: domains `A` over `F_q^6`
and `H` over `GF(2^128)`) and its circuit `c.H`; domain `H`'s circuit proof is the generic per-field
domain proof (`GordieHowe.MLDSA44.Native.ROMParams.readyH`, `GordieHowe/Applications/MLDSA44/Native/ROMParams/ProofSystem.lean`):

* **the interpretation** (`interp`): field `0` is `F_q^6` (`MLDSANativeField6`, the registry entry
  `mldsaNative6Entry`; the node `GF(p^1)` the prime subfield), field `1` is `GF(2^128)` (`gf128`,
  `GordieHowe/Applications/FieldInterps/Basic.lean`); the opaque function `mac.target_bits` returns bit `i` of
  the integer reading of its argument, the MAC tag's message in `GF(2^128)` (`targetBitsFn`), and
  the program's other opaque values take no arguments (`tr`, `key.a_hat`, `key.t1`, read from the
  statement).
-/

namespace GordieHowe.MLDSA44.Native.ROMParams.HashField

open RealizedProgram.Export
open Generated.MLDSA44.Native.ROMParams.Program (program)

/-! ## The interpretation -/

/-- **The interpretation of the native ML-DSA program at the ROM parameters**: field `0` is `F_q^6`, field `1`
(and any other identifier) `GF(2^128)`; the opaque functions `targetBitsFn`. -/
abbrev interp : RealizedProgram.Interp := RealizedProgram.mldsaInterp RealizedProgram.fq6

end GordieHowe.MLDSA44.Native.ROMParams.HashField
