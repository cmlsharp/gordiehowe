-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.FieldInterps.Basic

@[expose] public section

/-!
# GordieHowe: the interpretation of the ML-DSA programs at the ROM parameters

The ML-DSA programs at the ROM parameters (`MLDSA44.Native.ROMParams`, `MLDSA44.Emulated.ROMParams`,
export `c825eb05`) have
two fields: domain `A`'s (`F_q^6` native, Goldilocks² emulated) and domain `H`'s `GF(2^128)`
(`gf128`, `GordieHowe/Applications/FieldInterps/Basic.lean`). Their interpretations differ only in field `0`
(`mldsaInterp`), so the frontend's facts about domain `H` are stated once for any field `0` and read
at each arm's.
-/

namespace GordieHowe.RealizedProgram

/-- **The interpretation of an ML-DSA program** with domain `A` over `F0` and domain `H` over
`FH`: field `0` is `F0`, field `1` (and any other identifier) `FH`; the opaque function
`mac.target_bits` returns bit `i` of the integer reading of its argument (`targetBitsFn`), and the
program's other opaque values take no arguments. -/
abbrev mldsaInterpOf (F0 FH : FieldInterp) : Interp :=
  ⟨fun n => match n with | 0 => F0 | _ => FH, targetBitsFn⟩

/-- **The interpretation of an ML-DSA program at the ROM parameters** with domain `A` over `F0`: domain `H` over
`GF(2^128)` (`mldsaInterpOf F0 gf128`). -/
abbrev mldsaInterp (F0 : FieldInterp) : Interp := mldsaInterpOf F0 gf128

/-- **The field models of an ML-DSA interpretation**: field `0` has `F0`'s model, every other field
`FH`'s. -/
theorem mldsaInterpOf_models {F0 FH : FieldInterp} {p0 b0 pH bH : List String}
    (h0 : F0.Model p0 b0) (hH : FH.Model pH bH) :
    (mldsaInterpOf F0 FH).Models (twoFieldNodes p0 pH) (twoFieldNodes b0 bH)
  | 0 => h0
  | _ + 1 => hH

end GordieHowe.RealizedProgram
