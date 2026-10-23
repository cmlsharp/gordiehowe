-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Sampler.ChallengeReader
public import GordieHowe.Foundations.Fields.GF2_128
public import GordieHowe.Foundations.Fields.GF2_256
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative9
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11
public import GordieHowe.Foundations.Fields.Goldilocks
public import GordieHowe.Foundations.Fields.GoldilocksQuartic

@[expose] public section

/-!
# The field element readers

The C++ `sample` of each field of the flagship configurations (the field aliases of the `GordieHowe.MLDSA44.Native.ROMParams` and
`GordieHowe.MLDSA44.Native.QROMParams` profiles, `lib/params/param_sets.h` lines 100–105 and 140–145), as a `CReader`.
The configuration-specific instantiation of the generic readers of
`GordieHowe/SPBCS/Sampler/ChallengeReader.lean`, so it lives with the instances. The benchmark report
(`lib/bench/report_bench.cc`) selects the profile by `PQ_FIELD_PROFILE`, and each
configuration of `lib/gordiehowe/examples` draws its challenges in that profile's fields:

| Lean field | C++ type | draw |
|---|---|---|
| `GF2_128` | `GF2_128<>` | 16 bytes, no rejection (`gf2_128.h` lines 197–205) |
| `GF2_256` | `GF2_256<>` | 32 bytes, no rejection (`gf2_256.h` lines 195–203) |
| `ZMod 12289` | `Fp14` | 2 bytes, masked to 14 bits, rejected if `≥ 12289` (`fp14.h` lines 292–305) |
| `ZMod 8380417` | `Fp24` | 3 bytes, masked to 23 bits, rejected if `≥ 8380417` (`fp24.h` lines 286–299) |
| `ZMod pGold` | `Fp64G` | 8 bytes, rejected if `≥ p` (`fp_goldilocks.h` lines 167–174) |
| `FalconNativeField9` | `Fp14_N<9,2>` | 9 `Fp14` coordinates of `X^9 - 2` (`fp14_n.h` line 258) |
| `FalconNativeField20` | `NativeWide<Fp14,20,11,2,…,Tower=true>` | 20 `Fp14` coordinates, `e[4j+i]` the coefficient of `u^i v^j` (`fp_native_wide.h` lines 44, 372–379) |
| `MLDSANativeField6` | `Fp24_6` | 6 `Fp24` coordinates of `X^6 - 7` (`fp24_6.h` line 209) |
| `MLDSANativeField11` | `NativeWide<Fp24,11,2,0,…>` | 11 `Fp24` coordinates of `X^11 - 2` |
| `GoldilocksExt2` | `Fp64G2` | 2 Goldilocks coordinates of `X^2 - 7` (`fp_goldilocks.h` lines 344–349) |
| `GoldilocksExt4` | `Fp64G4` | 4 Goldilocks coordinates of `X^4 - 7` (`fp_goldilocks4.h` line 180) |

The binary fields read their bytes as a little-endian integer whose bit `i` is the coefficient of
`X^i` (`GF2Poly::of_bytes`, `gf2poly.h` line 55): bit `i` of byte `j` is the coefficient of
`X^(8j + i)` (`bytesEquiv`). An extension coordinate `i` is the coefficient of `X^i` in the power
basis of the defining polynomial (the coefficient vector the field stores, `falconNative9Coords` and
the like); for the tower `FalconNativeField20` coordinate `4j + i` is the coefficient of `u^i v^j`
(`falcon20Equiv`).
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

open Polynomial

/-! ### Coordinates -/

/-- **The bits of `b` bytes**, bit `i` of byte `j` at position `8j + i` (a little-endian
integer read bitwise). -/
def bytesEquiv (b : ℕ) : (Fin b → Byte) ≃ (Fin (b * 8) → ZMod 2) :=
  (Equiv.piCongrRight fun _ => (finCongr (by norm_num : 256 = 2 ^ 8)).trans
    finFunctionFinEquiv.symm).trans
    ((Equiv.curry (Fin b) (Fin 8) (Fin 2)).symm.trans
      (Equiv.arrowCongr finProdFinEquiv (Equiv.refl _)))

/-- The `20` coordinates of the tower `F_q[u]/(u^4 - 11)[v]/(v^5 - (u + 2))`: coordinate `4j + i`
the coefficient of `u^i v^j`. -/
def falcon20Equiv : (Fin 20 → ZMod 12289) ≃ FalconNativeField20 :=
  (Equiv.arrowCongr (finProdFinEquiv (m := 5) (n := 4)).symm (Equiv.refl _)).trans
    ((Equiv.curry (Fin 5) (Fin 4) (ZMod 12289)).trans
      ((Equiv.piCongrRight fun _ => falconQuarticCoords.symm).trans falconNative20Coords.symm))

/-! ### Byte lengths -/

theorem byteLen_eq {n l : ℕ} (h1 : n < 256 ^ l) (h2 : 256 ^ (l - 1) ≤ n) (hl : 0 < l) :
    Rejection.byteLen n = l := by
  have ha := (Rejection.lt_pow_iff_byteLen_le n l).1 h1
  have hb : ¬ Rejection.byteLen n ≤ l - 1 := fun h =>
    absurd ((Rejection.lt_pow_iff_byteLen_le n (l - 1)).2 h) (not_lt.2 h2)
  omega

theorem byteLen_12289 : Rejection.byteLen 12289 = 2 := byteLen_eq (by norm_num) (by norm_num) (by norm_num)

/-! ### The readers -/

namespace CReader

/-- A `GF(2^128)` element: 16 bytes. -/
def gf2_128 : CReader GF2_128 :=
  binary ((bytesEquiv 16).trans gf2_128Coords.symm)

/-- A `GF(2^256)` element: 32 bytes. -/
def gf2_256 : CReader GF2_256 :=
  binary ((bytesEquiv 32).trans gf2_256Coords.symm)

/-- An element of `ZMod q`, `q > 0`: `nat(q)`. -/
def zmod (q : ℕ) [NeZero q] : CReader (ZMod q) :=
  prime (Nat.pos_of_ne_zero (NeZero.ne q)) (ZMod.finEquiv q).toEquiv

/-- A `FalconNativeField9` element (native Falcon at the ROM parameters, `Fp14_9`). -/
def falconNative : CReader FalconNativeField9 :=
  ext (zmod 12289) falconNative9Coords.symm

/-- A `FalconNativeField20` element (native Falcon at the QROM parameters, the tower `FalconField20`). -/
def falconNative20 : CReader FalconNativeField20 := ext (zmod 12289) falcon20Equiv

/-- An `MLDSANativeField6` element (native ML-DSA at the ROM parameters, `Fp24_6`). -/
def mldsaNative : CReader MLDSANativeField6 :=
  ext (zmod 8380417) mldsaNative6Coords.symm

/-- An `MLDSANativeField11` element (native ML-DSA at the QROM parameters, `MlDsaField11`). -/
def mldsaNative11 : CReader MLDSANativeField11 :=
  ext (zmod 8380417) mldsaNative11Coords.symm

/-- A `GoldilocksExt2` element (the emulated arms at the ROM parameters, `Fp64G2`). -/
def goldilocksExt2 : CReader GoldilocksExt2 :=
  ext (zmod pGold) goldilocksExt2Coords.symm

/-- A `GoldilocksExt4` element (the emulated arms at the QROM parameters, `Fp64G4`). -/
def goldilocksExt4 : CReader GoldilocksExt4 :=
  ext (zmod pGold) goldilocksExt4Coords.symm

@[simp] theorem gf2_128_load : gf2_128.load = ⟨1, 16⟩ := rfl
@[simp] theorem gf2_256_load : gf2_256.load = ⟨1, 32⟩ := rfl
@[simp] theorem falconNative20_load : falconNative20.load = ⟨20, 2⟩ := by
  simp [falconNative20, zmod, Load.nsmul, byteLen_12289]

end CReader

end GordieHowe.SPBCS
