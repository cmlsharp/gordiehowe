-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.Conv
public import GordieHowe.Foundations.Fields.GF2_128

@[expose] public section

/-!
# `Conv(r)` for the concrete `GF(2¹²⁸)`

The polynomial basis `gf2_128Basis128` with its parity property: the root of
`X¹²⁸ + X⁷ + X² + X + 1` satisfies the positive reduction rule `X¹²⁸ = X⁷ + X² + X + 1`
(`gf2_128_root_pow_128`), the sum over `gf2_128Taps` (`sum_gf2_128Taps`), so `applyConv_eval` packs
the output of `applyConv` to the product, and `mod_two_eq_bitsNat` reads its parities as the bits of
the product.
-/

namespace GordieHowe

open Conv

/-- The taps of `X¹²⁸ + X⁷ + X² + X + 1` lie below the width. -/
theorem gf2_128Taps_lt : ∀ t ∈ gf2_128Taps, t < macChunkBits := by
  decide

/-- The parity property of `applyConv` in the polynomial basis of `GF2_128`. -/
theorem gf2_128_conv_parity (r x : GF2_128) (m : Fin macChunkBits) :
    applyConv gf2_128Taps (bitsNat gf2_128Basis128 r) (bitsNat gf2_128Basis128 x) m % 2 =
      bitsNat gf2_128Basis128 (r * x) m := by
  refine mod_two_eq_bitsNat gf2_128Basis128 ?_ m
  have hr := pack_bitsNat gf2_128Basis128 r
  have hx := pack_bitsNat gf2_128Basis128 x
  simp only [MAC.pack, show gf2_128Basis128.e = gf2_128E from rfl, gf2_128E] at hr hx ⊢
  rw [applyConv_eval gf2_128Taps_lt (by rw [sum_gf2_128Taps]; exact gf2_128_root_pow_128), hr, hx]

/-- The polynomial basis of `GF(2¹²⁸)` as a `ConvBasis` at the flagship shape. -/
def gf2_128ConvBasis : ConvBasis128 GF2_128 where
  toMACBasis := gf2_128Basis128
  taps_lt := gf2_128Taps_lt
  conv_parity := gf2_128_conv_parity

end GordieHowe
