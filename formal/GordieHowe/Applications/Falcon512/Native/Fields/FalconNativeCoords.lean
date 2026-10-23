-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative9
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20
public import GordieHowe.Language.Realizations.MaskSubfield

@[expose] public section

/-!
# The constant coordinate of the native Falcon fields

The constant coordinate of an element of `FalconNativeField9` (`falconNative9Coords x 0`) and of
`FalconNativeField20` (`falconQuarticCoords (falconNative20Coords x 0) 0`) is the element of
`ZMod 12289` a natural or the prime field's `algebraMap` casts to it: the casts are the constant
polynomials of the coefficient-vector representations (`PolyRep.const`). The realized programs' integer
readings of these fields read the constant coordinate
(`GordieHowe/Applications/Falcon512/Ring/Native/ROMParams/Interp.lean`,
`GordieHowe/Applications/Falcon512/Ring/Native/QROMParams/Interp.lean`).
-/

namespace GordieHowe

/-- **The constant coordinate of a natural's cast** in `FalconNativeField9` is its cast in
`ZMod 12289`. -/
theorem falconNative9Coords_natCast (n : ℕ) :
    falconNative9Coords (n : FalconNativeField9) 0 = (n : ZMod 12289) :=
  PolyRep.coordsEquiv_const_zero (n := 9) (by norm_num) (n : ZMod 12289)

/-- **The constant coordinate of the prime field's image** in `FalconNativeField9` is the
element. -/
theorem falconNative9Coords_algebraMap (z : ZMod 12289) :
    falconNative9Coords (algebraMap (ZMod 12289) FalconNativeField9 z) 0 = z := by
  have h : algebraMap (ZMod 12289) FalconNativeField9 z = ((z.val : ℕ) : FalconNativeField9) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    exact map_natCast _ _
  rw [h, falconNative9Coords_natCast, ZMod.natCast_zmod_val]

/-- **The coordinates of a sum** in `FalconNativeField9` are the sums of the coordinates
(coefficientwise addition, `PolyRep.add`). -/
theorem falconNative9Coords_add (x y : FalconNativeField9) (i : Fin 9) :
    falconNative9Coords (x + y) i = falconNative9Coords x i + falconNative9Coords y i := by
  show PolyRep.coordsEquiv (PolyRep.add (n := 9) x y) i = _
  simp [PolyRep.add, falconNative9Coords]
  rfl

/-- **The coordinates of `0`** in `FalconNativeField9` are `0`. -/
theorem falconNative9Coords_zero (i : Fin 9) :
    falconNative9Coords (0 : FalconNativeField9) i = 0 := by
  show PolyRep.coordsEquiv (PolyRep.zero : Vector (ZMod 12289) 9) i = 0
  simp [PolyRep.zero]

/-- **The constant coordinate's natural, cast back, is additive** in `FalconNativeField9`. -/
theorem falconNative9Coords_val_cast_add (x y : FalconNativeField9) :
    (((falconNative9Coords (x + y) 0).val : ℕ) : FalconNativeField9) =
      ((falconNative9Coords x 0).val : FalconNativeField9) +
        ((falconNative9Coords y 0).val : FalconNativeField9) := by
  rw [falconNative9Coords_add, ZMod.natCast_val, ZMod.natCast_val, ZMod.natCast_val,
    ZMod.cast_add (dvd_refl _)]

/-- **The constant coordinate of a natural's cast** in `FalconNativeField20`, through
`FalconQuartic`, is its cast in `ZMod 12289`. -/
theorem falconNative20Coords_natCast (n : ℕ) :
    falconQuarticCoords (falconNative20Coords (n : FalconNativeField20) 0) 0 = (n : ZMod 12289) := by
  have h1 : falconNative20Coords (n : FalconNativeField20) 0 = (n : FalconQuartic) :=
    PolyRep.coordsEquiv_const_zero (K := FalconQuartic) (n := 5) (by norm_num) (n : FalconQuartic)
  rw [h1]
  exact PolyRep.coordsEquiv_const_zero (n := 4) (by norm_num) (n : ZMod 12289)

/-- **The constant coordinate of the prime field's image** in `FalconNativeField20` is the
element. -/
theorem falconNative20Coords_algebraMap (z : ZMod 12289) :
    falconQuarticCoords (falconNative20Coords (algebraMap (ZMod 12289) FalconNativeField20 z) 0) 0 =
      z := by
  have h : algebraMap (ZMod 12289) FalconNativeField20 z = ((z.val : ℕ) : FalconNativeField20) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    exact map_natCast _ _
  rw [h, falconNative20Coords_natCast, ZMod.natCast_zmod_val]

/-- **The coordinates of a sum** in `FalconQuartic` are the sums of the coordinates. -/
theorem falconQuarticCoords_add (x y : FalconQuartic) (i : Fin 4) :
    falconQuarticCoords (x + y) i = falconQuarticCoords x i + falconQuarticCoords y i := by
  show PolyRep.coordsEquiv (PolyRep.add (n := 4) x y) i = _
  simp [PolyRep.add, falconQuarticCoords]
  rfl

/-- **The coordinates of a sum** in `FalconNativeField20` are the sums of the coordinates. -/
theorem falconNative20Coords_add (x y : FalconNativeField20) (i : Fin 5) :
    falconNative20Coords (x + y) i = falconNative20Coords x i + falconNative20Coords y i := by
  show PolyRep.coordsEquiv (PolyRep.add (n := 5) x y) i = _
  simp [PolyRep.add, falconNative20Coords]
  rfl

/-- **The constant coordinate's natural, cast back, is additive** in `FalconNativeField20`. -/
theorem falconNative20Coords_val_cast_add (x y : FalconNativeField20) :
    (((falconQuarticCoords (falconNative20Coords (x + y) 0) 0).val : ℕ) : FalconNativeField20) =
      ((falconQuarticCoords (falconNative20Coords x 0) 0).val : FalconNativeField20) +
        ((falconQuarticCoords (falconNative20Coords y 0) 0).val : FalconNativeField20) := by
  rw [falconNative20Coords_add, falconQuarticCoords_add, ZMod.natCast_val, ZMod.natCast_val,
    ZMod.natCast_val, ZMod.cast_add (dvd_refl _)]

end GordieHowe
