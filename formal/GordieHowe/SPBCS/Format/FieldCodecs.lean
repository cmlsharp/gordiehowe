-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Format.SpecWrites
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
# The C++ byte layout of the fields' elements

The bytes of a field element as the C++ `to_bytes_field` writes them (`Codec.FieldBytes.ofCoords`:
the coordinates in the C++ basis, coordinate `i` as the bits `[b · i, b · i + b)` of a
little-endian integer), for the eight fields of the configurations:

| field | C++ class | basis | bits per coordinate | bytes |
|---|---|---|---|---|
| `GF(2^128)` | `GF2_128` | `x^i` mod `x^128 + x^7 + x^2 + x + 1` | `1` | `16` |
| `GF(2^256)` | `GF2_256` | `x^i` mod `x^256 + x^10 + x^5 + x^2 + 1` | `1` | `32` |
| `GF(12289^9)` | `Fp14_9` | `x^i` mod `x^9 - 2` | `16` | `18` |
| `GF(12289^20)` | `FalconField20` | `u^i v^j` at `4j + i` | `14` | `35` |
| `GF(8380417^6)` | `Fp24_6` | `x^i` mod `x^6 - 7` | `24` | `18` |
| `GF(8380417^11)` | `MlDsaField11` | `x^i` mod `x^11 - 2` | `23` | `32` |
| `GF(p^2)`, Goldilocks | `Fp64G2` | `x^i` mod `x^2 - 7` | `64` | `16` |
| `GF(p^4)`, Goldilocks | `Fp64G4` | `v^i` mod `v^4 - 7` | `64` | `32` |

Sources (`lib/`): `gf2k/gf2_128.h` lines 193–195 and `gf2k/gf2_256.h` lines 191–193 (the bits of the
polynomial as a little-endian integer, `algebra/limb.h` lines 69–73); `algebra/fp14_n.h` lines
273–276 and `algebra/fp24_6.h` lines 224–227 (each coefficient as `2` or `3` little-endian bytes);
`algebra/fp_native_wide.h` lines 387–401 (a little-endian bitstream of `floor(log2 p) + 1` bits per
coefficient, `e[4j + i]` the coefficient of `u^i v^j` in the tower `u^4 = 11`, `v^5 = u + 2`, lines
43–45); `algebra/fp_goldilocks.h` lines 330–333 and `algebra/fp_goldilocks4.h` lines 166–169 (each
coefficient as `8` little-endian bytes). Every coefficient is written as its residue in `[0, p)`.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

open Polynomial

namespace Codec.FieldBytes

/-- **The coordinates in a tower** `R ⊂ A ⊂ B` from coordinates `e₁` of `A` over `R` and `e₂` of
`B` over `A`: coordinate `a · j + i` of `x` is coordinate `i` of coordinate `j` of `x`. -/
def towerCoords {R A B : Type} {a b : ℕ} (e₁ : A ≃ (Fin a → R)) (e₂ : B ≃ (Fin b → A)) :
    B ≃ (Fin (b * a) → R) :=
  e₂.trans ((Equiv.arrowCongr (Equiv.refl _) e₁).trans
    ((Equiv.curry (Fin b) (Fin a) R).symm.trans (finProdFinEquiv.arrowCongr (Equiv.refl R))))

/-- The bytes of a `GF(2^128)` element: its `128` polynomial coefficients as bits, `16` bytes. -/
def gf2_128 : FieldBytes GF2_128 16 :=
  ofCoords gf2_128Coords (b := 1) (by norm_num)
    (by norm_num)

/-- The bytes of a `GF(2^256)` element: its `256` polynomial coefficients as bits, `32` bytes. -/
def gf2_256 : FieldBytes GF2_256 32 :=
  ofCoords gf2_256Coords (b := 1) (by norm_num)
    (by norm_num)

/-- The bytes of an element of the degree-9 Falcon field: its `9` coefficients, `2` bytes each. -/
def falconNative : FieldBytes FalconNativeField9 18 :=
  ofCoords falconNative9Coords (b := 16)
    (by norm_num) (by norm_num)

/-- The bytes of an element of the degree-20 Falcon field: its `20` tower coefficients, `14` bits
each, `35` bytes. -/
def falconNative20 : FieldBytes FalconNativeField20 35 :=
  ofCoords (towerCoords falconQuarticCoords
    falconNative20Coords) (b := 14)
    (by norm_num) (by norm_num)

/-- The bytes of an element of the degree-6 ML-DSA field: its `6` coefficients, `3` bytes each. -/
def mldsaNative : FieldBytes MLDSANativeField6 18 :=
  ofCoords mldsaNative6Coords (b := 24)
    (by norm_num) (by norm_num)

/-- The bytes of an element of the degree-11 ML-DSA field: its `11` coefficients, `23` bits
each, `32` bytes. -/
def mldsaNative11 : FieldBytes MLDSANativeField11 32 :=
  ofCoords mldsaNative11Coords (b := 23)
    (by norm_num) (by norm_num)

/-- The bytes of an element of the quadratic Goldilocks extension: its `2` coefficients, `8`
bytes each. -/
def goldilocksExt2 : FieldBytes GoldilocksExt2 16 :=
  ofCoords goldilocksExt2Coords (b := 64)
    (by norm_num [pGold]) (by norm_num)

/-- The bytes of an element of the quartic Goldilocks extension: its `4` coefficients, `8` bytes
each. -/
def goldilocksExt4 : FieldBytes GoldilocksExt4 32 :=
  ofCoords goldilocksExt4Coords (b := 64)
    (by norm_num [pGold]) (by norm_num)

end Codec.FieldBytes

end GordieHowe.SPBCS
