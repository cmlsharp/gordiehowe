-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.GF2_128Tower

@[expose] public section

/-!
# The packing tree `GF(2^16) < GF(2^32) < GF(2^128)` of `GF2_128`

The bases of the two subfield-masks stages above the bit stage of a domain whose packing tree is
`GF(2^16) <2 GF(2^32) <4 GF(2^128)`, as the C++ packing stage builds them
(`lib/gordiehowe/compiler/stage.h`, the `PackingStage` constructor and `power_basis`), the same
construction as the tree through `GF(2^64)` (`GordieHowe/Foundations/Fields/GF2_128Tower.lean`):

* **The inner stage** `GF(2^16) < GF(2^32)` (`gf2_128Inner32StageBasis`, top the fixed field of
  `x ↦ x^(2^32)`): `power_basis`'s candidates are `SubfieldInfo<F>::get(f, 32).basis`, the traces
  `Tr_{K/GF(2^32)}(x^j)` of the unit coordinate vectors kept when independent over `GF(2)`
  (`lib/gordiehowe/subfield.h`); `Tr(1) = 0` is dropped, and the first candidate
  `g = Tr_{K/GF(2^32)}(x)` (`gf2_128Inner32GenN`) is not fixed by `φ = x ↦ x^(2^16)`, so
  `β_i = g^i`.
* **The root stage** `GF(2^32) < GF(2^128)` (`gf2_128Root32Basis`): the candidates are
  `ExtensionBasis`'s `beta[i] = x^i`; `1` is fixed by `φ = x ↦ x^(2^32)`, and `1 + x` is not fixed
  by `φ`, `φ^2` or `φ^3`, so `β_j = (1 + x)^j`.

The trace-dual bases (Gauss–Jordan elimination of `Tr_{T/B}(β_i β_j)`) are the unique ones,
computed offline; the dualities and the memberships in `GF(2^32)` are checked by `decide +kernel`
in the spread representation (`gf2_128Exec`).
-/

namespace GordieHowe

open BinarySpread RelativePacking PackingStage

/-- `φ = x ↦ x ^ 2³²` has order dividing `4` on `GF2_128`. -/
instance : RelFrobeniusOrder GF2_128 2 32 4 :=
  .of_frobeniusOrder (M := 128) (by norm_num) (by norm_num)

/-! ## The inner stage `GF(2^16) < GF(2^32)` -/

/-- The inner stage's generator `Tr_{K/GF(2^32)}(x)`, as bits (`SubfieldInfo<F>::get(f, 32)`'s
first basis element). -/
def gf2_128Inner32GenN : ℕ := 0x59aacab2738d1a6bb93a97d1451741a5

/-- The trace-dual basis of `g^i` for `Tr_{GF(2^32)/GF(2^16)}`, as bits, computed offline. -/
def gf2_128Inner32DualN : Fin 2 → ℕ :=
  ![0xa6b2107f4a02cb24c9032252943d16b4, 0x309e41c3a305f809a7f0fcf13fdb57ab]

/-- The generator is `Tr_{K/GF(2^32)}(x) = x + x^(2^32) + x^(2^64) + x^(2^96)`. -/
theorem gf2_128Inner32Gen_trace :
    gf2_128Exec.trace 32 4 (gf2_128Exec.ofBits 2) = gf2_128Exec.ofBits gf2_128Inner32GenN := by
  decide +kernel

/-- `Tr_{GF(2^32)/GF(2^16)}(dual_i · g^j) = δ_ij`. -/
theorem gf2_128Inner32Dual_trace : ∀ i j : Fin 2,
    gf2_128Exec.trace 16 2
        (gf2_128Exec.mul (gf2_128Exec.ofBits (gf2_128Inner32DualN i))
          (gf2_128Exec.pow 1 j (gf2_128Exec.ofBits gf2_128Inner32GenN))) =
      if i = j then gf2_128Exec.ofBits 1 else 0 := by
  decide +kernel

/-- The generator lies in `GF(2^32)`. -/
theorem gf2_128Inner32Gen_sqPow :
    gf2_128Exec.sqPow 32 (gf2_128Exec.ofBits gf2_128Inner32GenN) =
      gf2_128Exec.ofBits gf2_128Inner32GenN := by
  decide +kernel

/-- The dual elements lie in `GF(2^32)`. -/
theorem gf2_128Inner32Dual_sqPow : ∀ i : Fin 2,
    gf2_128Exec.sqPow 32 (gf2_128Exec.ofBits (gf2_128Inner32DualN i)) =
      gf2_128Exec.ofBits (gf2_128Inner32DualN i) := by
  decide +kernel

/-- The relative basis `g^i` of `GF(2^32)` over `GF(2^16)` with its trace-dual basis. -/
def gf2_128Inner32Basis : RelativeBasis GF2_128 2 16 2 where
  β i := gf2_128OfNat gf2_128Inner32GenN ^ (i : ℕ)
  dual i := gf2_128OfNat (gf2_128Inner32DualN i)
  trace_dual := gf2_128Rep.trace_dual_of_spread gf2_128RingEquiv gf2_128OfNat gf2_128ValVia_ofBits
    (by norm_num) gf2_128Inner32Dual_trace

/-- **The inner stage's basis** `GF(2^16) < GF(2^32)` (`stage.h`, `power_basis`): `β_i = g^i` with
`g = Tr_{K/GF(2^32)}(x)` (`gf2_128Inner32StageBasis_β`); top `GF(2^32)`, the fixed field of
`x ↦ x^(2^32)`. -/
def gf2_128Inner32StageBasis : StageBasis GF2_128 2 16 2 :=
  StageBasis.ofFixedField gf2_128Inner32Basis
    (fun _ => pow_mem (gf2_128OfNat_mem_of_sqPow gf2_128Inner32Gen_sqPow) _)
    (fun i => gf2_128OfNat_mem_of_sqPow (gf2_128Inner32Dual_sqPow i))

theorem gf2_128Inner32StageBasis_top :
    gf2_128Inner32StageBasis.top = fixedField GF2_128 2 (16 * 2) :=
  rfl

/-- **The inner stage's basis is the C++ power basis** of
`Tr_{K/GF(2^32)}(x) = x + x^(2^32) + x^(2^64) + x^(2^96)`. -/
theorem gf2_128Inner32StageBasis_β (i : Fin 2) :
    gf2_128Inner32StageBasis.β i =
      (gf2_128Root + gf2_128Root ^ 2 ^ 32 + gf2_128Root ^ 2 ^ 64 + gf2_128Root ^ 2 ^ 96) ^
        (i : ℕ) := by
  change gf2_128OfNat gf2_128Inner32GenN ^ (i : ℕ) = _
  rw [← gf2_128ValVia_ofBits, ← gf2_128Inner32Gen_trace,
    gf2_128Rep.valVia_trace gf2_128RingEquiv 32 (Rep.canon_ofBits _), gf2_128ValVia_ofBits,
    Fin.sum_univ_four]
  simp [gf2_128Root, gf2_128OfNat, add_assoc]

/-! ## The root stage `GF(2^32) < GF(2^128)` -/

/-- The trace-dual basis of `(1 + x)^j` for `Tr_{K/GF(2^32)}`, as bits, computed offline. -/
def gf2_128Root32DualN : Fin 4 → ℕ :=
  ![0x9e5c1addfa5d2e283693c32c6c08932c, 0x24895e12a030ced280a13b185df1750f,
    0x4d1aad312e6948a0e35833f874d25fb7, 0x187a203118eaa908db0d5ca8f8e66170]

/-- `Tr_{K/GF(2^32)}(dual_i · (1 + x)^j) = δ_ij`. -/
theorem gf2_128Root32Dual_trace : ∀ i j : Fin 4,
    gf2_128Exec.trace 32 4
        (gf2_128Exec.mul (gf2_128Exec.ofBits (gf2_128Root32DualN i))
          (gf2_128Exec.pow 2 j (gf2_128Exec.ofBits 3))) =
      if i = j then gf2_128Exec.ofBits 1 else 0 := by
  decide +kernel

/-- **The root stage's relative basis** `GF(2^32) < GF(2^128)` (`stage.h`, `power_basis`):
`β_j = (1 + x)^j` (`gf2_128Root32Basis_β`) with its trace-dual basis. -/
def gf2_128Root32Basis : RelativeBasis GF2_128 2 32 4 where
  β j := gf2_128OfNat 3 ^ (j : ℕ)
  dual i := gf2_128OfNat (gf2_128Root32DualN i)
  trace_dual := gf2_128Rep.trace_dual_of_spread gf2_128RingEquiv gf2_128OfNat gf2_128ValVia_ofBits
    (by norm_num) gf2_128Root32Dual_trace

/-- **The root stage's basis is the C++ power basis** of `1 + x`. -/
theorem gf2_128Root32Basis_β (j : Fin 4) :
    gf2_128Root32Basis.β j = (1 + gf2_128Root) ^ (j : ℕ) := by
  change gf2_128OfNat 3 ^ (j : ℕ) = _
  rw [show (3 : ℕ) = 1 ^^^ 2 from rfl, gf2_128OfNat_xor, gf2_128OfNat_one]
  rfl

end GordieHowe
