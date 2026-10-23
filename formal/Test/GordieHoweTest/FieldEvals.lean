-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

/-
Evaluation checks of the executable fields: each `#guard` evaluates a field identity on the
compiled field operations (`X^k` equals the reduction constant, a product with an inverse is `1`)
and fails the build if it is false. Not proofs. They live here rather than in the field modules
because evaluation is slow and every importer of those modules would otherwise rebuild them, and
because this file is not a `module` (see `MLDSAVectors.lean`'s header on `#eval` in modules).
-/
import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20
import GordieHowe.Foundations.Fields.GF2_256
import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative9
import GordieHowe.Foundations.Fields.Goldilocks
import GordieHowe.Foundations.Fields.GoldilocksQuartic
import GordieHowe.Foundations.Fields.GF2_128
import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11
import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6
import GordieHowe.Foundations.Fields.GF2_128Exec
import GordieHowe.Foundations.Algebra.Conv

namespace GordieHowe

/-! ## `GordieHowe.Fields.FalconNative20`

Not proofs: the executable fields compute. `u⁴ = 11`, `v⁵ = u + 2`, and a product with an inverse
is `1` in both steps of the tower. -/

#guard falconU ^ 4 == 11
#guard falconV ^ 5 == algebraMap FalconQuartic FalconNativeField20 (falconU + 2)
#guard (falconQuarticCoords.symm ![3, 1, 4, 1])⁻¹ * falconQuarticCoords.symm ![3, 1, 4, 1] == 1
#guard (falconNative20Coords.symm fun j => falconQuarticCoords.symm fun i => (4 * j + i + 1 : ℕ))⁻¹ *
  falconNative20Coords.symm (fun j => falconQuarticCoords.symm fun i => (4 * j + i + 1 : ℕ)) == 1

/-! ## `GordieHowe.Fields.GF2_256`

Not proofs: the executable field computes. `x²⁵⁶` is the reduction bits `0x425`, and a product
with an inverse is `1`. -/

#guard gf2_256Root ^ 256 == gf2_256OfNat 0x425
#guard (gf2_256OfNat 0x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef)⁻¹ *
  gf2_256OfNat 0x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef == 1

/-! ## `GordieHowe.Fields.FalconNative9`

Not proofs: the executable field computes. `X⁹ = 2`, and a product with an inverse is `1`. -/

#guard falconNative9Gen ^ 9 == algebraMap (ZMod 12289) FalconNativeField9 2
#guard (falconNative9Coords.symm ![3, 1, 4, 1, 5, 9, 2, 6, 5])⁻¹ *
  falconNative9Coords.symm ![3, 1, 4, 1, 5, 9, 2, 6, 5] == 1

/-! ## `GordieHowe.Fields.Goldilocks`

Not proofs: the executable field computes. `X² = 7`, and a product with an inverse is `1`. -/

#guard goldilocksExt2Gen ^ 2 == algebraMap (ZMod pGold) GoldilocksExt2 7
#guard (goldilocksExt2Coords.symm ![314159265358979, 271828182845904])⁻¹ *
  goldilocksExt2Coords.symm ![314159265358979, 271828182845904] == 1

/-! ## `GordieHowe.Fields.GoldilocksQuartic`

Not proofs: the executable field computes. `X⁴ = 7`, and a product with an inverse is `1`. -/

#guard goldilocksExt4Gen ^ 4 == algebraMap (ZMod pGold) GoldilocksExt4 7
#guard (goldilocksExt4Coords.symm ![3, 14159265358979, 2718281828, 1])⁻¹ *
  goldilocksExt4Coords.symm ![3, 14159265358979, 2718281828, 1] == 1

/-! ## `GordieHowe.Fields.GF2_128`

Not proofs: the executable field computes. `x¹²⁸` is the reduction bits `0x87`, and a product
with an inverse is `1`. -/

#guard gf2_128Root ^ 128 == gf2_128OfBitVec 0x87#128
#guard (gf2_128OfBitVec 0xdeadbeefcafebabe0011223344556677#128)⁻¹ *
  gf2_128OfBitVec 0xdeadbeefcafebabe0011223344556677#128 == 1

/-! ## `GordieHowe.Fields.MLDSANative11`

Not proofs: the executable field computes. `X¹¹ = 2`, and a product with an inverse is `1`. -/

#guard mldsaNative11Gen ^ 11 == algebraMap (ZMod 8380417) MLDSANativeField11 2
#guard (mldsaNative11Coords.symm ![3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5])⁻¹ *
  mldsaNative11Coords.symm ![3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] == 1

/-! ## `GordieHowe.Fields.MLDSANative6`

Not proofs: the executable field computes. `X⁶ = 7`, and a product with an inverse is `1`. -/

#guard mldsaNative6Gen ^ 6 == algebraMap (ZMod 8380417) MLDSANativeField6 7
#guard (mldsaNative6Coords.symm ![3, 1, 4, 1, 5, 9])⁻¹ * mldsaNative6Coords.symm ![3, 1, 4, 1, 5, 9] == 1

/-! ## `GordieHowe.Fields.GF2_128Exec`

`gfMul` agrees with `Conv.applyConv` reduced mod `2`. -/

namespace GF2_128Exec

/-- The bits of a `BitVec 128` as a `Fin 128 → ℕ` of `0`/`1`, `GordieHowe.Conv`'s
input shape. -/
def natBitsOfBitVec (bv : BitVec 128) (i : Fin 128) : ℕ := if bv.getLsbD i then 1 else 0

/-- The inverse of `natBitsOfBitVec`, for reading back a `GordieHowe.Conv.applyConv`
result reduced mod `2`. -/
def bitVecOfNatBits (v : Fin 128 → ℕ) : BitVec 128 :=
  (List.finRange 128).foldl
    (fun acc i => if v i % 2 = 1 then acc ||| ((1 : BitVec 128) <<< (i : ℕ)) else acc) 0

/-- A test value. -/
def a1 : BitVec 128 := 0x0123456789abcdef0123456789abcdef#128
/-- A test value. -/
def b1 : BitVec 128 := 0xdeadbeefcafebabe0011223344556677#128
/-- `X⁶⁴`. -/
def x64 : BitVec 128 := (1#128) <<< 64

-- `gfMul` agrees with `GordieHowe.Conv.applyConv` reduced mod `2`, the executable
-- form of `Conv.conv_parity` for the concrete reduction polynomial.
#guard bitVecOfNatBits (fun i => Conv.applyConv Conv.gf2_128Taps (natBitsOfBitVec a1) (natBitsOfBitVec b1) i % 2) ==
  gfMul a1 b1
#guard bitVecOfNatBits (fun i => Conv.applyConv Conv.gf2_128Taps (natBitsOfBitVec a1) (natBitsOfBitVec x64) i % 2) ==
  gfMul a1 x64
#guard bitVecOfNatBits (fun i => Conv.applyConv Conv.gf2_128Taps (natBitsOfBitVec b1) (natBitsOfBitVec b1) i % 2) ==
  gfMul b1 b1

end GF2_128Exec

end GordieHowe
