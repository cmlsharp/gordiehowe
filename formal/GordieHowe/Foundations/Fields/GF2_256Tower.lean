-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.BinarySpreadBasis
public import GordieHowe.Foundations.Fields.GF2_256Relative
public import GordieHowe.Foundations.Fields.GF2_256

@[expose] public section

/-!
# The packing tree `GF(2^16) < GF(2^64) < GF(2^256)` of `GF2_256`

The bases of the two subfield-masks stages above the bit stage of the H domain at the QROM parameters (the plan's
packing edges `GF(2^16) <4 GF(2^64) <4 GF(2^256)`), as the C++ packing stage builds them
(`lib/gordiehowe/compiler/stage.h:91-126`, the `PackingStage` constructor: a stage over
`B = GF(2^b)` with `b` a multiple of the designated degree `16` has subfield masks; when it is not
the root stage `GF(2^16) < K`, which takes `ExtensionBasis`'s basis, it takes `power_basis`,
lines 415-463):

* **The inner stage** `GF(2^16) < GF(2^64)` (`gf2_256InnerStageBasis`, top the fixed field of
  `x ↦ x^(2^64)`): `power_basis`'s candidates are `SubfieldInfo<F>::get(f, 64).basis`
  (`stage.h:417-423`), the traces `Tr_{K/GF(2^64)}(x^j) = Σ_{k<4} x^(j 2^(64 k))` of the unit
  coordinate vectors `x^j` kept when independent over `GF(2)` (`lib/gordiehowe/subfield.h:299-313`,
  with `of_bytes_field` the little-endian polynomial-basis bits, `lib/gf2k/gf2_256.h:185-189`).
  `Tr(1) = 0` is dropped, so the first candidate is `Tr(x)`, and `power_basis` takes the first
  candidate `g` (or sum of two) with `φ^k(g) ≠ g` for `0 < k < 4`, `φ = x ↦ x^(2^16)`
  (`stage.h:424-433`): `g = Tr(x)` itself (`gf2_256InnerGenN`), `β_i = g^i`.
* **The root stage** `GF(2^64) < GF(2^256)` (`gf2_256RootBasis`): the candidates are
  `ExtensionBasis`'s `beta[i] = x^i` (`stage.h:418-421`; `lib/zk/zk_extension_packed.h:126-146`);
  `1` is fixed by `φ = x ↦ x^(2^64)`, and the next candidate `beta[0] + beta[1] = 1 + x` is not,
  so `β_j = (1 + x)^j`.

The trace-dual bases (`stage.h:436-463`, Gauss-Jordan elimination of `Tr_{T/B}(β_i β_j)` in `K`)
are the unique ones, computed offline; the dualities and the memberships in `GF(2^64)` are checked
by `decide +kernel` in the spread representation (`gf2_256Exec`).
-/

namespace GordieHowe

open BinarySpread RelativePacking PackingStage

/-- `φ = x ↦ x ^ 2⁶⁴` has order dividing `4` on `GF2_256`. -/
instance : RelFrobeniusOrder GF2_256 2 64 4 :=
  .of_frobeniusOrder (M := 256) (by norm_num) (by norm_num)

/-- **Subfield membership by a spread identity**: `x^(2^m) = x` on the spread natural. -/
theorem gf2_256OfNat_mem_of_sqPow {m v : ℕ}
    (h : gf2_256Exec.sqPow m (gf2_256Exec.ofBits v) = gf2_256Exec.ofBits v) :
    gf2_256OfNat v ∈ fixedField GF2_256 2 m := by
  rw [← gf2_256Val_ofBits]
  exact gf2_256Rep.valVia_mem_fixedField gf2_256RingEquiv h

/-! ## The inner stage `GF(2^16) < GF(2^64)` -/

/-- The inner stage's generator `Tr_{K/GF(2^64)}(x)`, as bits (`SubfieldInfo<F>::get(f, 64)`'s
first basis element, `lib/gordiehowe/subfield.h:299-313`). -/
def gf2_256InnerGenN : ℕ := 0xa2daee88420782e7df73cf7b4bfdb8ec462a44537659704545e18efb3a066395

/-- The trace-dual basis of `g^i` for `Tr_{GF(2^64)/GF(2^16)}`, as bits, computed offline
(`stage.h:436-463`). -/
def gf2_256InnerDualN : Fin 4 → ℕ :=
  ![0x30e41f5256688b1a78c6be4a451413f4e5281629dc137942c981ee4da7bb7cf1,
    0x41878466fa69c732215488737b1bab384787e458a75f47ddd93a595732cd5016,
    0x110b46cb251191d55b2791c4bf30d2ead63e22f3bd839e08c5693cc1a12c8984,
    0x910079995849460c3b824c5315190408af1e04b1e863b94979adf041f1967b8a]

/-- The generator is `Tr_{K/GF(2^64)}(x) = Σ_{k<4} x^(2^(64 k))`. -/
theorem gf2_256InnerGen_trace :
    gf2_256Exec.trace 64 4 (gf2_256Exec.ofBits 2) = gf2_256Exec.ofBits gf2_256InnerGenN := by
  decide +kernel

/-- `Tr_{GF(2^64)/GF(2^16)}(dual_i · g^j) = δ_ij`. -/
theorem gf2_256InnerDual_trace : ∀ i j : Fin 4,
    gf2_256Exec.trace 16 4
        (gf2_256Exec.mul (gf2_256Exec.ofBits (gf2_256InnerDualN i))
          (gf2_256Exec.pow 2 j (gf2_256Exec.ofBits gf2_256InnerGenN))) =
      if i = j then gf2_256Exec.ofBits 1 else 0 := by
  decide +kernel

/-- The generator lies in `GF(2^64)`. -/
theorem gf2_256InnerGen_sqPow :
    gf2_256Exec.sqPow 64 (gf2_256Exec.ofBits gf2_256InnerGenN) =
      gf2_256Exec.ofBits gf2_256InnerGenN := by
  decide +kernel

/-- The dual elements lie in `GF(2^64)`. -/
theorem gf2_256InnerDual_sqPow : ∀ i : Fin 4,
    gf2_256Exec.sqPow 64 (gf2_256Exec.ofBits (gf2_256InnerDualN i)) =
      gf2_256Exec.ofBits (gf2_256InnerDualN i) := by
  decide +kernel

/-- The relative basis `g^i` of `GF(2^64)` over `GF(2^16)` with its trace-dual basis. -/
def gf2_256InnerBasis : RelativeBasis GF2_256 2 16 4 where
  β i := gf2_256OfNat gf2_256InnerGenN ^ (i : ℕ)
  dual i := gf2_256OfNat (gf2_256InnerDualN i)
  trace_dual := gf2_256Rep.trace_dual_of_spread gf2_256RingEquiv gf2_256OfNat gf2_256Val_ofBits
    (by norm_num) gf2_256InnerDual_trace

/-- **The inner stage's basis** `GF(2^16) < GF(2^64)` (`stage.h`, `power_basis`): `β_i = g^i`
with `g = Tr_{K/GF(2^64)}(x)` (`gf2_256InnerStageBasis_β`); top `GF(2^64)`, the fixed field of
`x ↦ x^(2^64)`. -/
def gf2_256InnerStageBasis : StageBasis GF2_256 2 16 4 :=
  StageBasis.ofFixedField gf2_256InnerBasis
    (fun _ => pow_mem (gf2_256OfNat_mem_of_sqPow gf2_256InnerGen_sqPow) _)
    (fun i => gf2_256OfNat_mem_of_sqPow (gf2_256InnerDual_sqPow i))

theorem gf2_256InnerStageBasis_top :
    gf2_256InnerStageBasis.top = fixedField GF2_256 2 (16 * 4) :=
  rfl

/-- **The inner stage's basis is the C++ power basis** of `Tr_{K/GF(2^64)}(x)`. -/
theorem gf2_256InnerStageBasis_β (i : Fin 4) :
    gf2_256InnerStageBasis.β i = (∑ k : Fin 4, gf2_256Root ^ 2 ^ (64 * (k : ℕ))) ^ (i : ℕ) := by
  change gf2_256OfNat gf2_256InnerGenN ^ (i : ℕ) = _
  rw [← gf2_256Val_ofBits, ← gf2_256InnerGen_trace,
    gf2_256Rep.valVia_trace gf2_256RingEquiv 64 (Rep.canon_ofBits _), gf2_256Val_ofBits]
  rfl

/-! ## The root stage `GF(2^64) < GF(2^256)` -/

/-- The trace-dual basis of `(1 + x)^j` for `Tr_{K/GF(2^64)}`, as bits, computed offline
(`stage.h:436-463`). -/
def gf2_256RootDualN : Fin 4 → ℕ :=
  ![0x10f7c3e8650819446c3d87b396a33fba9f6c00539764e4f2a96ee2df68a90d7e,
    0xa0394b47304094867bceedc35e59cb118d6d2f9696520a4b01b89b084880afe5,
    0x004cb9a0afb78c8eccf417fd7e5d9c5a8a50278505724e2839793403bc5fd988,
    0x10260cffac1ffd3b645877ddefa07ee2b48d14f7c8f82be0909d2d14bbfe6a17]

/-- `Tr_{K/GF(2^64)}(dual_i · (1 + x)^j) = δ_ij`. -/
theorem gf2_256RootDual_trace : ∀ i j : Fin 4,
    gf2_256Exec.trace 64 4
        (gf2_256Exec.mul (gf2_256Exec.ofBits (gf2_256RootDualN i))
          (gf2_256Exec.pow 2 j (gf2_256Exec.ofBits 3))) =
      if i = j then gf2_256Exec.ofBits 1 else 0 := by
  decide +kernel

/-- `1 + x` in the spread representation. -/
theorem gf2_256OfBits_three :
    gf2_256Exec.ofBits 3 = gf2_256Exec.add (gf2_256Exec.ofBits 1) (gf2_256Exec.ofBits 2) := by
  decide +kernel

/-- **The root stage's relative basis** `GF(2^64) < GF(2^256)` (`stage.h`, `power_basis`):
`β_j = (1 + x)^j` (`gf2_256RootBasis_β`) with its trace-dual basis. -/
def gf2_256RootBasis : RelativeBasis GF2_256 2 64 4 where
  β j := gf2_256OfNat 3 ^ (j : ℕ)
  dual i := gf2_256OfNat (gf2_256RootDualN i)
  trace_dual := gf2_256Rep.trace_dual_of_spread gf2_256RingEquiv gf2_256OfNat gf2_256Val_ofBits
    (by norm_num) gf2_256RootDual_trace

/-- **The root stage's basis is the C++ power basis** of `1 + x`. -/
theorem gf2_256RootBasis_β (j : Fin 4) : gf2_256RootBasis.β j = (1 + gf2_256Root) ^ (j : ℕ) := by
  change gf2_256OfNat 3 ^ (j : ℕ) = _
  rw [← gf2_256Val_ofBits, gf2_256OfBits_three,
    gf2_256Rep.valVia_add gf2_256RingEquiv (Rep.canon_ofBits _) (Rep.canon_ofBits _),
    gf2_256Val_ofBits, gf2_256Val_ofBits, gf2_256OfNat_one]
  rfl

end GordieHowe
