-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.RelativePacking
public import GordieHowe.Foundations.Fields.GF2_256Selection

@[expose] public section

/-!
# The relative packing basis of `GF(2²⁵⁶)` over `GF(2¹⁶)`

The relative-extension packing of the batched-Keccak H commitment
(`lib/zk/zk_extension_packed.h` on `main`, commit `783b08e`) packs `D = 16` coordinates of the Ligero subfield
`E = GF(2¹⁶)` into one element of `K = GF(2²⁵⁶)`:

* `ExtensionTraits<GF2_256<>>`: `degree = 16`, `q = 65536` (lines 46-50), so `φ(x) = x ^ 2¹⁶`
  and `[K : E] = 16`: the instance `RelFrobeniusOrder GF2_256 2 16 16`.
* `beta[i] = g ^ i` with `generator = f.of_scalar_field(2)`, the polynomial variable `x`
  (lines 127-130, 139-146): `gf2_256RelBasisElt i = x ^ i`.
* `dual[i] = Σ_j (T⁻¹)_{ij} beta[j]` with `T_{ij} = trace(beta[i] · beta[j])` over `E`
  (lines 150-176).

The dual elements `gf2_256RelDualN` are computed offline by the same Gauss-Jordan
elimination over `E`, and the duality `Tr_{K/E}(dual_i · x ^ j) = δ_ij` for all `256`
pairs is four `decide +kernel` computations on the spread representation
(`gf2_256RelDual_trace`: `256` products and relative traces of `15 · 16` squarings each).
The fixed field of `φ`, `fixedField GF2_256 2 16`, is `gf2_256Subfield` by definition.
-/

namespace GordieHowe

open BinarySpread RelativePacking

/-- `φ = x ↦ x ^ 2¹⁶` has order dividing `16` on `GF2_256`. -/
instance : RelFrobeniusOrder GF2_256 2 16 16 :=
  .of_frobeniusOrder (M := 256) (by norm_num) (by norm_num)

/-- The relative basis `beta[i] = x ^ i` (`lib/zk/zk_extension_packed.h:105-108, 117-119`). -/
def gf2_256RelBasisElt (i : Fin 16) : GF2_256 := gf2_256Root ^ (i : ℕ)

/-- The trace-dual basis of `gf2_256RelBasisElt` for `Tr_{K/E}`, as bits, computed offline
by Gauss-Jordan elimination on `[T | I]` over `E` (`lib/zk/zk_extension_packed.h:123-149`). -/
def gf2_256RelDualN : Fin 16 → ℕ :=
  ![
    0x800004fc603f26bc24064eb0e904c5ef40c1383681148ab03ed7b7641c09111c,
    0xe0000d240310f6745b6c780436220aa57554e0cfdc4d26c74f84fc15d80324e4,
    0xf000024f69e76f955fe062159fc96994e44a4560b262204d755c92a057347b93,
    0x900005e0043937228a07da2fb08c44ca8bdbf5bf08ede72c3e455094eb366f3b,
    0xd0000c5f82cb87a9aed5156b457325c1204c38ea9347b6a44c01f8696d25ed6f,
    0x50000f1390cbfe2fbbcc55b644f2a6dcd41a0eb090fe31e0b06e7ec03e407685,
    0x10000d5ed61661e35daf785c568a705086ebd9ab1d323004d0c073649049c288,
    0x000007f0409d3ea6f5595e44becfda11b2334a4e3f5781450ada792bc848abc1,
    0xe0000d02a6622b3107f521a94098e68f5c99e620791a4e2f8ca38d66596cd230,
    0xa0000f026bc02699917776091a506cfa45bb17d45c84899540a18d5fe2ce9abb,
    0xe0000563a67402827e36279d058a0150dd240cb56bd719e7212064f2bf82aba6,
    0x7000015e0a311778bf4ed4cdadf1d180b420a335cc7ec5da7dd78e875f632ca1,
    0x000009b83ff111b4acf22be7a372afc4cab3328725f9c3e6a7fd3bda4b18fab2,
    0x30000b4fa7a80cc8b60e820ad7d5a3143ae3920f5df482e694ef948c7ce0e73f,
    0x500004dbd603e63a5f3dfb2e805c50d76de1d7167aa3cf693be820381a4125e7,
    0xc0000192954a9aa2b867ae1420e4cc1bccbe1e0341ea7a686dedc4492e397980]

/-- `gf2_256RelDual_trace` for `i < 4`. The certificate is four kernel checks of `64` pairs each,
which bounds the memory each check holds. -/
theorem gf2_256RelDual_trace_lt_4 : ∀ i j : Fin 16, (i : ℕ) < 4 →
    gf2_256Exec.trace 16 16
        (gf2_256Exec.mul (gf2_256Exec.ofBits (gf2_256RelDualN i))
          (gf2_256Exec.pow 4 j (gf2_256Exec.ofBits 2))) =
      if i = j then gf2_256Exec.ofBits 1 else 0 := by
  decide +kernel

/-- `gf2_256RelDual_trace` for `4 ≤ i < 8`. -/
theorem gf2_256RelDual_trace_lt_8 : ∀ i j : Fin 16, 4 ≤ (i : ℕ) → (i : ℕ) < 8 →
    gf2_256Exec.trace 16 16
        (gf2_256Exec.mul (gf2_256Exec.ofBits (gf2_256RelDualN i))
          (gf2_256Exec.pow 4 j (gf2_256Exec.ofBits 2))) =
      if i = j then gf2_256Exec.ofBits 1 else 0 := by
  decide +kernel

/-- `gf2_256RelDual_trace` for `8 ≤ i < 12`. -/
theorem gf2_256RelDual_trace_lt_12 : ∀ i j : Fin 16, 8 ≤ (i : ℕ) → (i : ℕ) < 12 →
    gf2_256Exec.trace 16 16
        (gf2_256Exec.mul (gf2_256Exec.ofBits (gf2_256RelDualN i))
          (gf2_256Exec.pow 4 j (gf2_256Exec.ofBits 2))) =
      if i = j then gf2_256Exec.ofBits 1 else 0 := by
  decide +kernel

/-- `gf2_256RelDual_trace` for `12 ≤ i`. -/
theorem gf2_256RelDual_trace_ge_12 : ∀ i j : Fin 16, 12 ≤ (i : ℕ) →
    gf2_256Exec.trace 16 16
        (gf2_256Exec.mul (gf2_256Exec.ofBits (gf2_256RelDualN i))
          (gf2_256Exec.pow 4 j (gf2_256Exec.ofBits 2))) =
      if i = j then gf2_256Exec.ofBits 1 else 0 := by
  decide +kernel

/-- `Tr_{K/E}(dual_i · x ^ j) = δ_ij`. -/
theorem gf2_256RelDual_trace : ∀ i j : Fin 16,
    gf2_256Exec.trace 16 16
        (gf2_256Exec.mul (gf2_256Exec.ofBits (gf2_256RelDualN i))
          (gf2_256Exec.pow 4 j (gf2_256Exec.ofBits 2))) =
      if i = j then gf2_256Exec.ofBits 1 else 0 := by
  intro i j
  rcases Nat.lt_or_ge (i : ℕ) 4 with h4 | h4
  · exact gf2_256RelDual_trace_lt_4 i j h4
  rcases Nat.lt_or_ge (i : ℕ) 8 with h8 | h8
  · exact gf2_256RelDual_trace_lt_8 i j h4 h8
  rcases Nat.lt_or_ge (i : ℕ) 12 with h12 | h12
  · exact gf2_256RelDual_trace_lt_12 i j h8 h12
  · exact gf2_256RelDual_trace_ge_12 i j h12

/-- `Exec.trace 16 16` computes `relTrace 2 16 16`. -/
theorem gf2_256Val_relTrace {y : ℕ} (hy : Canon gf2_256Exec y) :
    valVia gf2_256RingEquiv gf2_256Exec (gf2_256Exec.trace 16 16 y) =
      relTrace 2 16 16 (valVia gf2_256RingEquiv gf2_256Exec y) := by
  rw [gf2_256Rep.valVia_trace gf2_256RingEquiv 16 hy 16, relTrace]
  rfl

theorem gf2_256Val_pow_root {j : ℕ} (hj : j < 16) :
    valVia gf2_256RingEquiv gf2_256Exec (gf2_256Exec.pow 4 j (gf2_256Exec.ofBits 2)) =
      gf2_256Root ^ j := by
  rw [gf2_256Rep.valVia_pow gf2_256RingEquiv (Rep.canon_ofBits _) hj, gf2_256Val_ofBits_two]

/-- The relative basis of `GF(2²⁵⁶)` over `GF(2¹⁶)` with its trace-dual basis. -/
def gf2_256RelativeBasis : RelativeBasis GF2_256 2 16 16 where
  β := gf2_256RelBasisElt
  dual i := gf2_256OfNat (gf2_256RelDualN i)
  trace_dual i j := by
    have hj : Canon gf2_256Exec (gf2_256Exec.pow 4 j (gf2_256Exec.ofBits 2)) :=
      gf2_256Rep.canon_pow (Rep.canon_ofBits _) 4 j (by omega)
    have hm := gf2_256Rep.canon_mul (Rep.canon_ofBits (gf2_256RelDualN i)) hj
    have h := congrArg (valVia gf2_256RingEquiv gf2_256Exec) (gf2_256RelDual_trace i j)
    rw [gf2_256Val_relTrace hm, gf2_256Rep.valVia_mul gf2_256RingEquiv (Rep.canon_ofBits _) hj, gf2_256Val_ofBits,
      gf2_256Val_pow_root (by omega), gf2_256Rep.valVia_ite gf2_256RingEquiv, gf2_256Val_ofBits, gf2_256OfNat_one,
      gf2_256Rep.valVia_zero gf2_256RingEquiv] at h
    exact h

end GordieHowe
