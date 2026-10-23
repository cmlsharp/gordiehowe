-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11
public import GordieHowe.Language.Realizations.MaskSubfield

@[expose] public section

/-!
# The constant coordinate of `MLDSANativeField11`

The constant coordinate of an element of `MLDSANativeField11` (`mldsaNative11Coords x 0`) is the
element of `ZMod 8380417` a natural or the prime field's `algebraMap` casts to it: the casts are the
constant polynomials of the coefficient-vector representation (`PolyRep.const`). The realized program's integer
reading of this field reads the constant coordinate (`GordieHowe/Applications/MLDSA44/Native/QROMParams/HashField.lean`).
-/

namespace GordieHowe

/-- **The constant coordinate of a natural's cast** in `MLDSANativeField11` is its cast in
`ZMod 8380417`. -/
theorem mldsaNative11Coords_natCast (n : ℕ) :
    mldsaNative11Coords (n : MLDSANativeField11) 0 = (n : ZMod 8380417) :=
  PolyRep.coordsEquiv_const_zero (n := 11) (by norm_num) (n : ZMod 8380417)

/-- **The constant coordinate of the prime field's image** in `MLDSANativeField11` is the
element. -/
theorem mldsaNative11Coords_algebraMap (z : ZMod 8380417) :
    mldsaNative11Coords (algebraMap (ZMod 8380417) MLDSANativeField11 z) 0 = z := by
  have h : algebraMap (ZMod 8380417) MLDSANativeField11 z = ((z.val : ℕ) : MLDSANativeField11) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    exact map_natCast _ _
  rw [h, mldsaNative11Coords_natCast, ZMod.natCast_zmod_val]

end GordieHowe
