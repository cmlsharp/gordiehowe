-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.Conv
public import GordieHowe.Foundations.Fields.GF2_256

@[expose] public section

/-!
# `Conv(r)` for the concrete `GF(2²⁵⁶)`

The polynomial basis `gf2_256MACBasis` with its parity property, the `ConvBasis 256` of
the 256-bit MAC chunks. The taps `gf2_256Taps = {0, 2, 5, 10}` are the low terms of the
reduction polynomial `X²⁵⁶ + X¹⁰ + X⁵ + X² + 1` (`lib/gf2k/sysdep256.h:6`), the taps of
the C++ MAC basis (`kMacBasisGF2_256{256, {10, 5, 2, 0}}`, `lib/gordiehowe/core.h:2498`).

`convMax 256 gf2_256Taps = 1017` (`Conv.convMax_gf2_256`, in `GordieHowe.Foundations.Algebra.ConvMatrix`, by kernel
evaluation of the packed row sums of `Conv(1…1)`), the per-chunk bound the C++ A circuit checks
against the field (`nch * 1017 + 1`, `mac_acc_max` in `lib/gordiehowe/ops/operators.h`).
-/

namespace GordieHowe

open Conv

/-- The taps of `X²⁵⁶ + X¹⁰ + X⁵ + X² + 1` lie below the width. -/
theorem gf2_256Taps_lt : ∀ t ∈ gf2_256Taps, t < 256 := by
  decide

/-- The parity property of `applyConv` in the polynomial basis of `GF2_256`. -/
theorem gf2_256_conv_parity (r x : GF2_256) (m : Fin 256) :
    applyConv gf2_256Taps (bitsNat gf2_256MACBasis r) (bitsNat gf2_256MACBasis x) m % 2 =
      bitsNat gf2_256MACBasis (r * x) m := by
  refine mod_two_eq_bitsNat gf2_256MACBasis ?_ m
  have hr := pack_bitsNat gf2_256MACBasis r
  have hx := pack_bitsNat gf2_256MACBasis x
  simp only [MAC.pack, show gf2_256MACBasis.e = gf2_256E from rfl, gf2_256E] at hr hx ⊢
  rw [applyConv_eval gf2_256Taps_lt (by rw [sum_gf2_256Taps]; exact gf2_256_root_pow_256), hr, hx]

/-- The polynomial basis of `GF(2²⁵⁶)` as a `ConvBasis` at the 256-bit MAC shape. -/
def gf2_256ConvBasis : ConvBasis 256 gf2_256Taps GF2_256 where
  toMACBasis := gf2_256MACBasis
  taps_lt := gf2_256Taps_lt
  conv_parity := gf2_256_conv_parity

/-- The basis element `i` of `gf2_256ConvBasis` is `x ^ i` for the polynomial variable
`x = gf2_256Root` (`of_scalar_field(0b10)`), the C++ MAC packing `xp[i] = x^i`
(`lib/gordiehowe/compiler/mac.h:335-338`). -/
theorem gf2_256ConvBasis_e (i : Fin 256) : gf2_256ConvBasis.e i = gf2_256Root ^ (i : ℕ) := rfl

/-- Coordinate `i` of `gf2_256ConvBasis` is bit `i` of the packed element, the coefficient of
`x ^ i`: the C++ `Elt::operator[]` (`lib/gf2k/gf2_256.h:92-96`) read by `polynomial_bits`
(`lib/gordiehowe/core.h:2558-2578`) and `CoefficientBits` (`lib/gordiehowe/compiler/mac.h:359`). -/
theorem gf2_256ConvBasis_unpack (x : GF2_256) (i : Fin 256) :
    gf2_256ConvBasis.unpack x i = BitVec.getLsbD (w := 256) x i := rfl

end GordieHowe
