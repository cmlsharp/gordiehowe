-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6
public import GordieHowe.Language.Realizations.MaskSubfield

@[expose] public section

/-!
# The constant coordinate of `MLDSANativeField6`

The constant coordinate of an element of `MLDSANativeField6` (`mldsaNative6Coords x 0`) is the
element of `ZMod 8380417` a natural or the prime field's `algebraMap` casts to it: the casts are the
constant polynomials of the coefficient-vector representation (`PolyRep.const`). The realized program's integer
reading of this field reads the constant coordinate (`GordieHowe/Applications/MLDSA44/Native/ROMParams/HashField.lean`).
-/

namespace GordieHowe

/-- **The constant coordinate of a natural's cast** in `MLDSANativeField6` is its cast in
`ZMod 8380417`. -/
theorem mldsaNative6Coords_natCast (n : ℕ) :
    mldsaNative6Coords (n : MLDSANativeField6) 0 = (n : ZMod 8380417) :=
  PolyRep.coordsEquiv_const_zero (n := 6) (by norm_num) (n : ZMod 8380417)

/-- **The constant coordinate of the prime field's image** in `MLDSANativeField6` is the
element. -/
theorem mldsaNative6Coords_algebraMap (z : ZMod 8380417) :
    mldsaNative6Coords (algebraMap (ZMod 8380417) MLDSANativeField6 z) 0 = z := by
  have h : algebraMap (ZMod 8380417) MLDSANativeField6 z = ((z.val : ℕ) : MLDSANativeField6) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    exact map_natCast _ _
  rw [h, mldsaNative6Coords_natCast, ZMod.natCast_zmod_val]

end GordieHowe
