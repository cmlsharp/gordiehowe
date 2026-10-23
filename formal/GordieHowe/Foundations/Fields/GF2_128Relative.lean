-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.KummerTrace
public import GordieHowe.Foundations.Fields.BinarySpread
public import GordieHowe.Foundations.Fields.GF2_128Selection

@[expose] public section

/-!
# The relative packing basis of `GF(2¹²⁸)` over `GF(2¹⁶)`

The hash field at the ROM parameters is `GF2_128<>` (`lib/params/param_sets.h`,
`HashField = GF2_128<>`), with reduction polynomial `x¹²⁸ + x⁷ + x² + x + 1`
(`lib/gf2k/gf2_128.h:57-58`, `kProtocolFieldId{2, 128, 0x87, …}`): `GF2_128`. The
relative-extension packing of the batched-Keccak H commitment
(`lib/zk/zk_extension_packed.h`) packs `D = 8` coordinates of the Ligero subfield
`E = GF(2¹⁶)` into one element of `K = GF(2¹²⁸)`:

* `ExtensionTraits<GF2_128<>>`: `degree = 8`, `q = 65536` (lines 25-29), so `φ(x) = x ^ 2¹⁶`
  and `[K : E] = 8`: the instance `RelFrobeniusOrder GF2_128 2 16 8`. The coordinates are
  elements of the fixed field of `φ`, `gf2_128Subfield` (`in_subfield`,
  `lib/gf2k/gf2_128.h:216`), stored in `K` as they are (`ExtensionLayout`, lines 297-311).
* `beta[i] = g ^ i` with `generator = f.of_scalar_field(2)`, the polynomial variable `x`
  (lines 127-130, 139-146): `gf2_128RelBasisElt i = x ^ i`.
* `dual[i] = Σ_j (T⁻¹)_{ij} beta[j]` with `T_{ij} = trace(beta[i] · beta[j])` over `E`
  (lines 150-176).

The dual elements `gf2_128RelDualN` are computed offline by the same Gauss-Jordan
elimination over `E`, and the duality `Tr_{K/E}(dual_i · x ^ j) = δ_ij` for all `64` pairs is
one `decide +kernel` computation in the spread representation of `GordieHowe.Foundations.Fields.BinarySpread`
(`gf2_128Exec`, digits of `16` bits), where one multiplication is one `Nat.mul`.
-/

namespace GordieHowe

open Polynomial BinarySpread RelativePacking

/-- `φ = x ↦ x ^ 2¹⁶` has order dividing `8` on `GF2_128`. -/
instance : RelFrobeniusOrder GF2_128 2 16 8 :=
  .of_card (by rw [gf2_128_card]) (by norm_num)

/-! ## The spread representation -/

/-- The element of `GF2_128` with polynomial-basis coordinates the `128` low bits of `v`. -/
def gf2_128OfNat (v : ℕ) : GF2_128 := gf2_128OfBitVec (BitVec.ofNat 128 v)

theorem gf2_128ToSpec_ofNat (v : ℕ) : gf2_128ToSpec (gf2_128OfNat v) = bitsVal gf2_128Poly 128 v :=
  toSpec_ofNat 128 v

theorem gf2_128Val_ofBits (v : ℕ) :
    val gf2_128Exec gf2_128Poly (gf2_128Exec.ofBits v) = gf2_128ToSpec (gf2_128OfNat v) := by
  rw [gf2_128ToSpec_ofNat]
  exact gf2_128Rep.val_ofBits v

theorem gf2_128OfNat_one : gf2_128OfNat 1 = 1 := gf2_128OfBitVec_one

theorem gf2_128OfNat_zero : gf2_128OfNat 0 = 0 := gf2_128OfBitVec_zero

/-- **`gf2_128OfNat` is additive on xors**: xoring the spread representations adds the elements. -/
theorem gf2_128OfNat_xor (a b : ℕ) : gf2_128OfNat (a ^^^ b) = gf2_128OfNat a + gf2_128OfNat b := by
  unfold gf2_128OfNat
  rw [BitVec.ofNat_xor, gf2_128OfBitVec_xor]

/-- **The element `2^j` is the `j`-th power of `x`** for `j < 128`: its only polynomial-basis bit is
bit `j`. -/
theorem gf2_128OfNat_two_pow {j : ℕ} (hj : j < 128) : gf2_128OfNat (2 ^ j) = gf2_128OfNat 2 ^ j := by
  apply gf2_128ToSpec.injective
  have h2 : bitsVal gf2_128Poly 128 2 = AdjoinRoot.root gf2_128Poly := by
    simpa using bitsVal_two_pow (f := gf2_128Poly) (n := 128) (j := 1) (by norm_num)
  rw [map_pow, gf2_128ToSpec_ofNat, gf2_128ToSpec_ofNat, bitsVal_two_pow hj, h2]

theorem gf2_128Val_ofBits_two :
    val gf2_128Exec gf2_128Poly (gf2_128Exec.ofBits 2) = AdjoinRoot.root gf2_128Poly := by
  rw [gf2_128Rep.val_ofBits]
  simpa using bitsVal_two_pow (f := gf2_128Poly) (n := gf2_128Exec.n) (j := 1) (by decide)

/-- `Exec.trace 16 8` computes `relTrace 2 16 8`. -/
theorem gf2_128Val_relTrace {y : ℕ} (hy : Canon gf2_128Exec y) :
    val gf2_128Exec gf2_128Poly (gf2_128Exec.trace 16 8 y) =
      relTrace 2 16 8 (val gf2_128Exec gf2_128Poly y) := by
  rw [gf2_128Rep.val_trace 16 hy 8, relTrace]
  rfl

theorem gf2_128Val_pow_root {j : ℕ} (hj : j < 8) :
    val gf2_128Exec gf2_128Poly (gf2_128Exec.pow 3 j (gf2_128Exec.ofBits 2)) =
      AdjoinRoot.root gf2_128Poly ^ j := by
  rw [gf2_128Rep.val_pow (Rep.canon_ofBits _) hj, gf2_128Val_ofBits_two]

/-! ## The relative basis -/

/-- The relative basis `beta[i] = x ^ i` (`lib/zk/zk_extension_packed.h:127-130, 139-146`). -/
def gf2_128RelBasisElt (i : Fin 8) : GF2_128 := gf2_128Root ^ (i : ℕ)

/-- The trace-dual basis of `gf2_128RelBasisElt` for `Tr_{K/E}`, as bits, computed offline
by Gauss-Jordan elimination on `[T | I]` over `E` (`lib/zk/zk_extension_packed.h:150-176`). -/
def gf2_128RelDualN : Fin 8 → ℕ :=
  ![
    0x0c33d9efef01f1b8ee534b708de710a2,
    0x3cf1d59bed32844364ee9a28709576d6,
    0x1c73409c1a2dd7fd851c96727f0e2f8c,
    0x79e62febe9d45a708a6ac2442a48da57,
    0x34d0b262e6e9b46ca306cbe2b3fc5a9c,
    0x924b4307e47f6e2aebb8d2fa1a238187,
    0x820a4e78dc0039e1373ab88768858db6,
    0xa69bb9ae25e4131d2dd2e5e8f530caa9]

/-- `Tr_{K/E}(dual_i · x ^ j) = δ_ij`. -/
theorem gf2_128RelDual_trace : ∀ i j : Fin 8,
    gf2_128Exec.trace 16 8
        (gf2_128Exec.mul (gf2_128Exec.ofBits (gf2_128RelDualN i))
          (gf2_128Exec.pow 3 j (gf2_128Exec.ofBits 2))) =
      if i = j then gf2_128Exec.ofBits 1 else 0 := by
  decide +kernel

/-- The relative basis of `GF(2¹²⁸)` over `GF(2¹⁶)` with its trace-dual basis. -/
def gf2_128RelativeBasis : RelativeBasis GF2_128 2 16 8 where
  β := gf2_128RelBasisElt
  dual i := gf2_128OfNat (gf2_128RelDualN i)
  trace_dual i j := by
    have hj : Canon gf2_128Exec (gf2_128Exec.pow 3 j (gf2_128Exec.ofBits 2)) :=
      gf2_128Rep.canon_pow (Rep.canon_ofBits _) 3 j (by omega)
    have hm := gf2_128Rep.canon_mul (Rep.canon_ofBits (gf2_128RelDualN i)) hj
    have h := congrArg (val gf2_128Exec gf2_128Poly) (gf2_128RelDual_trace i j)
    rw [gf2_128Val_relTrace hm, gf2_128Rep.val_mul (Rep.canon_ofBits _) hj, gf2_128Val_ofBits,
      gf2_128Val_pow_root (by omega), Rep.val_ite, gf2_128Val_ofBits, gf2_128OfNat_one,
      gf2_128Rep.val_zero, ← gf2_128ToSpec_root, ← map_pow, ← map_mul, map_one] at h
    refine gf2_128ToSpec.injective ?_
    rw [map_relTrace gf2_128ToSpec, apply_ite gf2_128ToSpec, map_one,
      map_zero]
    exact h

end GordieHowe
