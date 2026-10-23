-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.Goldilocks
public import GordieHowe.Foundations.Fields.GoldilocksQuartic
public import GordieHowe.Language.Realizations.MaskSubfield

@[expose] public section

/-!
# The constant coordinate of the Goldilocks extensions

The constant coordinate of an element of `GoldilocksExt2` (`goldilocksExt2Coords x 0`) and of
`GoldilocksExt4` (`goldilocksExt4Coords x 0`) is the element of `ZMod pGold` a natural or the prime
field's `algebraMap` casts to it: the casts are the constant polynomials of the coefficient-vector
representations (`PolyRep.const`). The plan's integer readings of these fields read the constant
coordinate (`GordieHowe/Applications/Falcon512/Ring/Carrier/`).
-/

namespace GordieHowe

/-- **The constant coordinate of a natural's cast** in `GoldilocksExt2` is its cast in
`ZMod pGold`. -/
theorem goldilocksExt2Coords_natCast (n : ℕ) :
    goldilocksExt2Coords (n : GoldilocksExt2) 0 = (n : ZMod pGold) :=
  PolyRep.coordsEquiv_const_zero (n := 2) (by norm_num) (n : ZMod pGold)

/-- **The constant coordinate of the prime field's image** in `GoldilocksExt2` is the element. -/
theorem goldilocksExt2Coords_algebraMap (z : ZMod pGold) :
    goldilocksExt2Coords (algebraMap (ZMod pGold) GoldilocksExt2 z) 0 = z := by
  have h : algebraMap (ZMod pGold) GoldilocksExt2 z = ((z.val : ℕ) : GoldilocksExt2) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    exact map_natCast _ _
  rw [h, goldilocksExt2Coords_natCast, ZMod.natCast_zmod_val]

/-- **The constant coordinate of a natural's cast** in `GoldilocksExt4` is its cast in
`ZMod pGold`. -/
theorem goldilocksExt4Coords_natCast (n : ℕ) :
    goldilocksExt4Coords (n : GoldilocksExt4) 0 = (n : ZMod pGold) :=
  PolyRep.coordsEquiv_const_zero (n := 4) (by norm_num) (n : ZMod pGold)

/-- **The constant coordinate of the prime field's image** in `GoldilocksExt4` is the element. -/
theorem goldilocksExt4Coords_algebraMap (z : ZMod pGold) :
    goldilocksExt4Coords (algebraMap (ZMod pGold) GoldilocksExt4 z) 0 = z := by
  have h : algebraMap (ZMod pGold) GoldilocksExt4 z = ((z.val : ℕ) : GoldilocksExt4) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    exact map_natCast _ _
  rw [h, goldilocksExt4Coords_natCast, ZMod.natCast_zmod_val]

/-- **The coordinates of a sum** in `GoldilocksExt2` are the sums of the coordinates. -/
theorem goldilocksExt2Coords_add (x y : GoldilocksExt2) (i : Fin 2) :
    goldilocksExt2Coords (x + y) i = goldilocksExt2Coords x i + goldilocksExt2Coords y i := by
  show PolyRep.coordsEquiv (PolyRep.add (n := 2) x y) i = _
  simp [PolyRep.add, goldilocksExt2Coords]
  rfl

/-- **The coordinates of a sum** in `GoldilocksExt4` are the sums of the coordinates. -/
theorem goldilocksExt4Coords_add (x y : GoldilocksExt4) (i : Fin 4) :
    goldilocksExt4Coords (x + y) i = goldilocksExt4Coords x i + goldilocksExt4Coords y i := by
  show PolyRep.coordsEquiv (PolyRep.add (n := 4) x y) i = _
  simp [PolyRep.add, goldilocksExt4Coords]
  rfl

end GordieHowe
