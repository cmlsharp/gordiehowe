-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.ConvMatrix
public import GordieHowe.Language.Realizations.MAC

@[expose] public section

/-!
# `Conv(r)` in a polynomial basis

`GordieHowe.Foundations.Algebra.ConvMatrix` defines the integer matrix `Conv(r)` for a chunk width `w` and reduction
taps `T`. This file connects it to a field `K` through a `MACBasis w K`: `bitsNat` reads the bits of
a field element, and `ConvBasis w T K` adds, as field facts, the bound `t < w` on the taps and the
parity property `(Conv(r) · bits(x)) mod 2 = bits(r · x)`. `mod_two_eq_bitsNat` turns
`applyConv_eval` into the parity property in characteristic two; the concrete `GF(2¹²⁸)` instance,
at the flagship shape `ConvBasis128`, is discharged in `GordieHowe.Foundations.Fields.GF2_128Conv`.
-/

namespace GordieHowe.Conv

variable {w : ℕ}

/-- Bits of a field element as naturals `0` or `1`. -/
def bitsNat {K : Type*} [Field K] (B : MACBasis w K) (r : K) (i : Fin w) : ℕ :=
  if B.unpack r i then 1 else 0

/-- The polynomial basis of `GF(2^w)` together with the tap bound and the parity property that
makes `Conv(r)` for the taps `T` an integer representation of multiplication
by `r`.  A field fact, discharged once for the concrete field with the
reduction polynomial `X^w + Σ_{t ∈ T} X^t`. -/
structure ConvBasis (w : ℕ) (T : Finset ℕ) (K : Type*) [Field K] extends MACBasis w K where
  /-- every tap lies below the width, so every reduction target lies below its source -/
  taps_lt : ∀ t ∈ T, t < w
  conv_parity : ∀ r x : K, ∀ m : Fin w,
    applyConv T (bitsNat toMACBasis r) (bitsNat toMACBasis x) m % 2 = bitsNat toMACBasis (r * x) m

/-- The basis at the flagship shape: width `macChunkBits = 128`, taps
`gf2_128Taps` of `X¹²⁸ + X⁷ + X² + X + 1`. -/
abbrev ConvBasis128 (K : Type*) [Field K] := ConvBasis macChunkBits gf2_128Taps K

/-- Packing Boolean coordinates and then reading them through the same basis
recovers those coordinates as naturals. -/
theorem bitsNat_pack {K : Type*} [Field K] (B : MACBasis w K) (b : Fin w → Bool) :
    bitsNat B (MAC.pack B fun i => if b i then 1 else 0) =
      fun i => if b i then 1 else 0 := by
  have hunpack : B.unpack (MAC.pack B fun i => if b i then 1 else 0) = b := by
    apply B.pack_injective
    rw [B.pack_unpack]
    simp [MAC.pack]
  funext i
  rw [bitsNat, hunpack]

/-- Packing the bits of `r` recovers `r`. -/
theorem pack_bitsNat {K : Type*} [Field K] (B : MACBasis w K) (r : K) :
    MAC.pack B (fun i => (bitsNat B r i : K)) = r := by
  conv_rhs => rw [← B.pack_unpack r]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : B.unpack r i <;> simp [bitsNat, h]

/-- In characteristic two, natural coordinates whose casts pack to `y` have the
bits of `y` as parities. -/
theorem mod_two_eq_bitsNat {K : Type*} [Field K] [CharP K 2] (B : MACBasis w K)
    {c : Fin w → ℕ} {y : K} (h : MAC.pack B (fun i => (c i : K)) = y) (i : Fin w) :
    c i % 2 = bitsNat B y i := by
  have hbits : (fun i => decide (c i % 2 = 1)) = B.unpack y := by
    apply B.pack_injective
    rw [B.pack_unpack, ← h, MAC.pack]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [CharP.cast_eq_mod K 2 (c i)]
    rcases Nat.mod_two_eq_zero_or_one (c i) with h2 | h2 <;> simp [h2]
  rw [bitsNat, ← hbits]
  rcases Nat.mod_two_eq_zero_or_one (c i) with h2 | h2 <;> simp [h2]

/-- In characteristic two, packing the integer coordinates produced by
`applyConv` gives multiplication in the hash field. -/
theorem pack_applyConv {K : Type*} [Field K] [CharP K 2]
    {T : Finset ℕ} (B : ConvBasis w T K) (r x : K) :
    MAC.pack B.toMACBasis (fun m =>
      (applyConv T (bitsNat B.toMACBasis r) (bitsNat B.toMACBasis x) m : K)) = r * x := by
  unfold MAC.pack
  calc
    ∑ i, (applyConv T (bitsNat B.toMACBasis r) (bitsNat B.toMACBasis x) i : K) *
        B.toMACBasis.e i =
        ∑ i, if B.toMACBasis.unpack (r * x) i then B.toMACBasis.e i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [CharP.cast_eq_mod K 2, B.conv_parity]
      simp [bitsNat]
    _ = r * x := B.toMACBasis.pack_unpack (r * x)

end GordieHowe.Conv
