-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.BinarySpreadBasis
public import GordieHowe.Foundations.Fields.GF2_128Relative
public import GordieHowe.Foundations.Fields.GF2_128Dual

@[expose] public section

/-!
# The packing tree `GF(2^16) < GF(2^64) < GF(2^128)` of `GF2_128`

The bases of the two subfield-masks stages above the bit stage of the H domain at the ROM parameters (the plan's
packing edges `GF(2^16) <4 GF(2^64) <2 GF(2^128)`), as the C++ packing stage builds them
(`lib/gordiehowe/compiler/stage.h:91-126`, the `PackingStage` constructor: a stage over
`B = GF(2^b)` with `b` a multiple of the designated degree `16` has subfield masks; when it is not
the root stage `GF(2^16) < K`, which takes `ExtensionBasis`'s basis, it takes `power_basis`,
lines 415-463):

* **The inner stage** `GF(2^16) < GF(2^64)` (`gf2_128InnerStageBasis`, top the fixed field of
  `x ↦ x^(2^64)`): `power_basis`'s candidates are `SubfieldInfo<F>::get(f, 64).basis`
  (`stage.h:417-423`), the traces `Tr_{K/GF(2^64)}(x^j) = x^j + x^(j 2^64)` of the unit
  coordinate vectors `x^j` kept when independent over `GF(2)` (`lib/gordiehowe/subfield.h:299-313`,
  with `of_bytes_field` the little-endian polynomial-basis bits, `lib/gf2k/gf2_128.h:187-191`).
  `Tr(1) = 0` is dropped, so the first candidate is `Tr(x)`, and `power_basis` takes the first
  candidate `g` (or sum of two) with `φ^k(g) ≠ g` for `0 < k < 4`, `φ = x ↦ x^(2^16)`
  (`stage.h:424-433`): `g = Tr(x)` itself (`gf2_128InnerGenN`), `β_i = g^i`.
* **The root stage** `GF(2^64) < GF(2^128)` (`gf2_128RootBasis`): the candidates are
  `ExtensionBasis`'s `beta[i] = x^i` (`stage.h:418-421`; `lib/zk/zk_extension_packed.h:126-146`);
  `1` is fixed by `φ = x ↦ x^(2^64)`, and the next candidate `beta[0] + beta[1] = 1 + x` is not,
  so `β_j = (1 + x)^j`.

The trace-dual bases (`stage.h:436-463`, Gauss-Jordan elimination of `Tr_{T/B}(β_i β_j)` in `K`)
are the unique ones, computed offline; the dualities and the memberships in `GF(2^64)` are checked
by `decide +kernel` in the spread representation (`gf2_128Exec`).
-/

namespace GordieHowe

open BinarySpread RelativePacking PackingStage

/-- `φ = x ↦ x ^ 2⁶⁴` has order dividing `2` on `GF2_128`. -/
instance : RelFrobeniusOrder GF2_128 2 64 2 :=
  .of_frobeniusOrder (M := 128) (by norm_num) (by norm_num)

/-- The spread natural of the bits `v` represents `gf2_128OfNat v`. -/
theorem gf2_128ValVia_ofBits (v : ℕ) :
    valVia gf2_128RingEquiv gf2_128Exec (gf2_128Exec.ofBits v) = gf2_128OfNat v := by
  unfold valVia
  rw [gf2_128Val_ofBits]
  exact gf2_128RingEquiv.symm_apply_apply _

/-- **Subfield membership by a spread identity**: `x^(2^m) = x` on the spread natural. -/
theorem gf2_128OfNat_mem_of_sqPow {m v : ℕ}
    (h : gf2_128Exec.sqPow m (gf2_128Exec.ofBits v) = gf2_128Exec.ofBits v) :
    gf2_128OfNat v ∈ fixedField GF2_128 2 m := by
  rw [← gf2_128ValVia_ofBits]
  exact gf2_128Rep.valVia_mem_fixedField gf2_128RingEquiv h

/-! ## The inner stage `GF(2^16) < GF(2^64)` -/

/-- The inner stage's generator `Tr_{K/GF(2^64)}(x)`, as bits (`SubfieldInfo<F>::get(f, 64)`'s
first basis element, `lib/gordiehowe/subfield.h:299-313`). -/
def gf2_128InnerGenN : ℕ := 0x61651fea6b5832b944e598a795a299f4

/-- The trace-dual basis of `g^i` for `Tr_{GF(2^64)/GF(2^16)}`, as bits, computed offline
(`stage.h:436-463`). -/
def gf2_128InnerDualN : Fin 4 → ℕ :=
  ![0xcb6c7532892bef5856128a1254df0582, 0x3cb312c3fc9eaa013c3c8832fb95b150,
    0x006df6b73033d932f5a15d20605560d9, 0x8a7b5f8f563fe749ec2d5cda64749a77]

/-- The generator is `Tr_{K/GF(2^64)}(x) = x + x^(2^64)`. -/
theorem gf2_128InnerGen_trace :
    gf2_128Exec.trace 64 2 (gf2_128Exec.ofBits 2) = gf2_128Exec.ofBits gf2_128InnerGenN := by
  decide +kernel

/-- `Tr_{GF(2^64)/GF(2^16)}(dual_i · g^j) = δ_ij`. -/
theorem gf2_128InnerDual_trace : ∀ i j : Fin 4,
    gf2_128Exec.trace 16 4
        (gf2_128Exec.mul (gf2_128Exec.ofBits (gf2_128InnerDualN i))
          (gf2_128Exec.pow 2 j (gf2_128Exec.ofBits gf2_128InnerGenN))) =
      if i = j then gf2_128Exec.ofBits 1 else 0 := by
  decide +kernel

/-- The generator lies in `GF(2^64)`. -/
theorem gf2_128InnerGen_sqPow :
    gf2_128Exec.sqPow 64 (gf2_128Exec.ofBits gf2_128InnerGenN) =
      gf2_128Exec.ofBits gf2_128InnerGenN := by
  decide +kernel

/-- The dual elements lie in `GF(2^64)`. -/
theorem gf2_128InnerDual_sqPow : ∀ i : Fin 4,
    gf2_128Exec.sqPow 64 (gf2_128Exec.ofBits (gf2_128InnerDualN i)) =
      gf2_128Exec.ofBits (gf2_128InnerDualN i) := by
  decide +kernel

/-- The relative basis `g^i` of `GF(2^64)` over `GF(2^16)` with its trace-dual basis. -/
def gf2_128InnerBasis : RelativeBasis GF2_128 2 16 4 where
  β i := gf2_128OfNat gf2_128InnerGenN ^ (i : ℕ)
  dual i := gf2_128OfNat (gf2_128InnerDualN i)
  trace_dual := gf2_128Rep.trace_dual_of_spread gf2_128RingEquiv gf2_128OfNat gf2_128ValVia_ofBits
    (by norm_num) gf2_128InnerDual_trace

/-- **The inner stage's basis** `GF(2^16) < GF(2^64)` (`stage.h`, `power_basis`): `β_i = g^i`
with `g = Tr_{K/GF(2^64)}(x)` (`gf2_128InnerStageBasis_β`); top `GF(2^64)`, the fixed field of
`x ↦ x^(2^64)`. -/
def gf2_128InnerStageBasis : StageBasis GF2_128 2 16 4 :=
  StageBasis.ofFixedField gf2_128InnerBasis
    (fun _ => pow_mem (gf2_128OfNat_mem_of_sqPow gf2_128InnerGen_sqPow) _)
    (fun i => gf2_128OfNat_mem_of_sqPow (gf2_128InnerDual_sqPow i))

theorem gf2_128InnerStageBasis_top :
    gf2_128InnerStageBasis.top = fixedField GF2_128 2 (16 * 4) :=
  rfl

/-- **The inner stage's basis is the C++ power basis** of `Tr_{K/GF(2^64)}(x) = x + x^(2^64)`. -/
theorem gf2_128InnerStageBasis_β (i : Fin 4) :
    gf2_128InnerStageBasis.β i = (gf2_128Root + gf2_128Root ^ 2 ^ 64) ^ (i : ℕ) := by
  change gf2_128OfNat gf2_128InnerGenN ^ (i : ℕ) = _
  rw [← gf2_128ValVia_ofBits, ← gf2_128InnerGen_trace,
    gf2_128Rep.valVia_trace gf2_128RingEquiv 64 (Rep.canon_ofBits _), gf2_128ValVia_ofBits,
    Fin.sum_univ_two]
  simp [gf2_128Root, gf2_128OfNat]

/-! ## The root stage `GF(2^64) < GF(2^128)` -/

/-- The trace-dual basis of `(1 + x)^j` for `Tr_{K/GF(2^64)}`, as bits, computed offline
(`stage.h:436-463`). -/
def gf2_128RootDualN : Fin 2 → ℕ :=
  ![0xa2df0b7966c5849ec2f95f0775bed0ae, 0x9e4af928ddbc838a41a8cafd2c95b018]

/-- `Tr_{K/GF(2^64)}(dual_i · (1 + x)^j) = δ_ij`. -/
theorem gf2_128RootDual_trace : ∀ i j : Fin 2,
    gf2_128Exec.trace 64 2
        (gf2_128Exec.mul (gf2_128Exec.ofBits (gf2_128RootDualN i))
          (gf2_128Exec.pow 1 j (gf2_128Exec.ofBits 3))) =
      if i = j then gf2_128Exec.ofBits 1 else 0 := by
  decide +kernel

/-- **The root stage's relative basis** `GF(2^64) < GF(2^128)` (`stage.h`, `power_basis`):
`β_j = (1 + x)^j` (`gf2_128RootBasis_β`) with its trace-dual basis. -/
def gf2_128RootBasis : RelativeBasis GF2_128 2 64 2 where
  β j := gf2_128OfNat 3 ^ (j : ℕ)
  dual i := gf2_128OfNat (gf2_128RootDualN i)
  trace_dual := gf2_128Rep.trace_dual_of_spread gf2_128RingEquiv gf2_128OfNat gf2_128ValVia_ofBits
    (by norm_num) gf2_128RootDual_trace

/-- **The root stage's basis is the C++ power basis** of `1 + x`. -/
theorem gf2_128RootBasis_β (j : Fin 2) : gf2_128RootBasis.β j = (1 + gf2_128Root) ^ (j : ℕ) := by
  change gf2_128OfNat 3 ^ (j : ℕ) = _
  rw [show (3 : ℕ) = 1 ^^^ 2 from rfl, gf2_128OfNat_xor, gf2_128OfNat_one]
  rfl

end GordieHowe
