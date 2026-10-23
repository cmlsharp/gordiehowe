-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.System.MAC
public import GordieHowe.Foundations.Fields.GF2_256Conv
public import GordieHowe.Foundations.Fields.GF2_128Conv
public import GordieHowe.Applications.MLDSA44.Fields.GF2_256
public import GordieHowe.Applications.MLDSA44.Fields.GF2_128
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11Relative
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6Relative

@[expose] public section

/-!
# ML-DSA: the concrete field data

The masking subfields of `F_q^11` and `F_q^6` (`mldsa11Mask`, `mldsa6Mask`) and the field data of
the two profiles, instantiated once for the concrete fields of the C++ profiles
(`../params/param_sets.h`): the QROM parameters (`GordieHowe.MLDSA44.Native.QROMParams.fieldData`: H over
`GF(2^256)`, A over `F_q^11`) and the ROM parameters (`GordieHowe.MLDSA44.Native.ROMParams.fieldData`: `GF(2^128)`,
`F_q^6`).
-/

namespace GordieHowe.MLDSA44.Native

open Params RelativePacking

/-! ### The masking subfields -/

/-- **`F_q` in `MLDSANativeField11`**: the embedding `algebraMap` and the constant coefficient as
its left inverse (computable). -/
def mldsa11Mask : MaskSubfield (ZMod 8380417) MLDSANativeField11 where
  embed := algebraMap (ZMod 8380417) MLDSANativeField11
  coord x := mldsaNative11Coords x 0
  coord_embed s := by
    change mldsaNative11Coords (ZMod.cast s) 0 = s
    rw [ZMod.cast_eq_val]
    exact (PolyRep.coordsEquiv_const_zero (n := 11) (by decide) _).trans (ZMod.natCast_zmod_val s)

/-- **`F_q` in `MLDSANativeField6`**: the embedding `algebraMap` and the constant coefficient as
its left inverse (computable). -/
def mldsa6Mask : MaskSubfield (ZMod 8380417) MLDSANativeField6 where
  embed := algebraMap (ZMod 8380417) MLDSANativeField6
  coord x := mldsaNative6Coords x 0
  coord_embed s := by
    change mldsaNative6Coords (ZMod.cast s) 0 = s
    rw [ZMod.cast_eq_val]
    exact (PolyRep.coordsEquiv_const_zero (n := 6) (by decide) _).trans (ZMod.natCast_zmod_val s)

/-! ### The QROM parameters -/

namespace QROMParams

/-- **The field data at the QROM parameters**: `F_q` in `MLDSANativeField11` (`mldsa11Mask`), the
selection field `gf2_256SelectionField` at degree `264`, `θ = gf2_256Theta`, the record packing's injectivity
(`gf2_256_pack_injOn`), the MAC basis `gf2_256ConvBasis` and the packing basis
`gf2_256PackedBasis` of `GF(2^256)`. -/
def fieldData : FieldData Profile.qrom GF2_256 MLDSANativeField11 (ZMod 8380417) where
  σ := mldsa11Mask
  sel := gf2_256SelectionField.ofLE (by decide)
  Θ := gf2_256Theta
  θ_mem := gf2_256Theta_mem
  packing3 _ _ ha hb h := gf2_256_pack_injOn ha hb h
  basis := gf2_256ConvBasis
  packing := gf2_256PackedBasis

end QROMParams

/-! ### The ROM parameters -/

namespace ROMParams

/-- **The field data at the ROM parameters**: `F_q` in `MLDSANativeField6` (`mldsa6Mask`), the
selection field `gf2_128SelectionField` at degree `264`, `θ = gf2_128Theta`, the record packing's injectivity
(`gf2_128_pack_injOn`), the MAC basis `gf2_128ConvBasis` and the packing basis
`gf2_128PackedBasis` of `GF(2^128)`. -/
def fieldData : FieldData Profile.rom GF2_128 MLDSANativeField6 (ZMod 8380417) where
  σ := mldsa6Mask
  sel := gf2_128SelectionField.ofLE (by decide)
  Θ := gf2_128Theta
  θ_mem := gf2_128Theta_mem
  packing3 _ _ ha hb h := gf2_128_pack_injOn ha hb h
  basis := gf2_128ConvBasis
  packing := gf2_128PackedBasis

end ROMParams

end GordieHowe.MLDSA44.Native
