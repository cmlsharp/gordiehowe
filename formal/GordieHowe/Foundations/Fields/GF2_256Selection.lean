-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.GF2_256
public import GordieHowe.Applications.Params
public import GordieHowe.Applications.Spec.SelectionField
public import GordieHowe.Foundations.ToMathlib.OrderOf
public import GordieHowe.Foundations.Algebra.RecordPacking

@[expose] public section

/-!
# The sixteen-bit subfield of `GF(2²⁵⁶)` and the selection field data

The constants of the C++ class `GF2_256<>` (`lib/gf2k/gf2_256.h` on `main`, commit
`f4e27b3c`; `subfield_log_bits = 4` by default, line 34):

* the subfield `E = GF(2¹⁶)`, the fixed points of `y ↦ y ^ 2¹⁶`, spanned by `beta_`
  (`in_subfield`, lines 214-218);
* `X` is the polynomial variable `x` (`kx_ = of_scalar_field(0b10)`, line 109), the
  selection encoding's `kappa = lc.f_.x()` (`lib/schemes/common/gp_select.h`);
* `g = x ^ ((2²⁵⁶ - 1) / (2¹⁶ - 1))` (`subfield_generator()`, lines 372-394, which computes
  the exponent as `(2¹⁶ + 1)(2³² + 1)(2⁶⁴ + 1)(2¹²⁸ + 1)`; `kg_ = g`, lines 116-117);
* `e i = g ^ i` for `i < 16` (`beta_`, lines 120-124).

Falcon's hash-to-point selection reads the counter `F.as_counter(n).e`, which is `g ^ n`.

The facts about concrete elements are `decide +kernel` computations on the spread
representation (`GordieHowe.Foundations.Fields.BinarySpread`): `g` equals the bits `gf2_256SubfieldGenN`,
`g ^ (65535 / r) ≠ 1` for the prime factors `r` of `65535 = 3 · 5 · 17 · 257`, and
`x ^ 2¹⁶ ≠ x`. So `g` has order `65535`, which gives `g ∈ E`, distinct powers up to `S`,
and degree at least `16` over `GF(2)`, which makes `1, g, …, g¹⁵` linearly independent.
-/

namespace GordieHowe

open BinarySpread

/-- The sixteen-bit subfield `GF(2¹⁶)` of `GF2_256`: the fixed points of the
`2¹⁶`-power Frobenius map (`in_subfield`, `lib/gf2k/gf2_256.h:214-218`). -/
def gf2_256Subfield : Subfield GF2_256 :=
  (iterateFrobenius GF2_256 2 16).eqLocusField (RingHom.id _)

theorem mem_gf2_256Subfield {y : GF2_256} : y ∈ gf2_256Subfield ↔ y ^ 2 ^ 16 = y :=
  Iff.rfl

/-! ## The variable `x` -/

theorem gf2_256_sqPow_16_two_ne :
    gf2_256Exec.sqPow 16 (gf2_256Exec.ofBits 2) ≠ gf2_256Exec.ofBits 2 := by decide +kernel

/-- The polynomial variable is outside the subfield: `x ^ 2¹⁶ ≠ x`. -/
theorem gf2_256_root_not_mem_subfield : gf2_256Root ∉ gf2_256Subfield := by
  rw [mem_gf2_256Subfield, ← gf2_256Val_ofBits_two,
    ← gf2_256Rep.valVia_sqPow gf2_256RingEquiv (Rep.canon_ofBits _)]
  exact gf2_256Val_ne (gf2_256Rep.canon_sqPow (Rep.canon_ofBits _) _) (Rep.canon_ofBits _)
    gf2_256_sqPow_16_two_ne

theorem gf2_256_sqPow_32_two_ne :
    gf2_256Exec.sqPow 32 (gf2_256Exec.ofBits 2) ≠ gf2_256Exec.ofBits 2 := by decide +kernel

/-- The polynomial variable lies in no quadratic extension of the subfield: `x ^ 2³² ≠ x`. -/
theorem gf2_256_root_pow_two_pow_32_ne : gf2_256Root ^ 2 ^ 32 ≠ gf2_256Root := by
  rw [← gf2_256Val_ofBits_two, ← gf2_256Rep.valVia_sqPow gf2_256RingEquiv (Rep.canon_ofBits _)]
  exact gf2_256Val_ne (gf2_256Rep.canon_sqPow (Rep.canon_ofBits _) _) (Rep.canon_ofBits _)
    gf2_256_sqPow_32_two_ne

/-- **The record packing at `x` is injective on triples of the subfield**
(`lib/gordiehowe/lib/permutation.h:26-31`, `selection_kappa`): `x` lies in no extension of degree
`1` or `2` of `GF(2¹⁶)` (`RecordPacking.pack_injOn`). -/
theorem gf2_256_pack_injOn {a b : Fin 3 → GF2_256} (ha : ∀ i, a i ∈ gf2_256Subfield)
    (hb : ∀ i, b i ∈ gf2_256Subfield)
    (h : RecordPacking.pack gf2_256Root a = RecordPacking.pack gf2_256Root b) : a = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine RecordPacking.pack_injOn (p := 2) (k := 16) (E := gf2_256Subfield)
    (fun y hy => mem_gf2_256Subfield.mp hy) (fun m hm hm3 => ?_) ha hb h
  interval_cases m
  · rw [pow_one]
    exact gf2_256_root_not_mem_subfield
  · rw [← pow_mul]
    exact gf2_256_root_pow_two_pow_32_ne

theorem gf2_256_root_ne_zero : gf2_256Root ≠ 0 := fun h =>
  gf2_256_root_not_mem_subfield (by rw [mem_gf2_256Subfield, h, zero_pow (by norm_num)])

/-- An element of order `m` has degree at least `s` over `GF(2)` once `2 ^ (s - 1) ≤ m`. -/
theorem gf2_256_le_natDegree_minpoly {x : GF2_256} {s : ℕ} (hx : x ≠ 0)
    (hord : 2 ^ (s - 1) ≤ orderOf x) : s ≤ (minpoly (ZMod 2) x).natDegree :=
  le_natDegree_minpoly_of_card_pow_le_orderOf (.of_finite _ _) hx (by rwa [Nat.card_zmod])

/-! ## The subfield generator -/

/-- The subfield generator `g = x ^ ((2²⁵⁶ - 1) / (2¹⁶ - 1))`
(`subfield_generator()`, `lib/gf2k/gf2_256.h:372-394`; `kg_`, line 117). -/
def gf2_256SubfieldGen : GF2_256 :=
  gf2_256Root ^ ((2 ^ 256 - 1) / (2 ^ 16 - 1))

/-- `gf2_256SubfieldGen` as bits, computed offline; `gf2_256_pow_subfieldGen` checks it. -/
def gf2_256SubfieldGenN : ℕ := 0xd5d973b1d7d8ef95b8e11e538f3b7f1e228b41efeda6b0b43900773419e531aa

theorem gf2_256_pow_subfieldGen :
    gf2_256Exec.pow 256 ((2 ^ 256 - 1) / (2 ^ 16 - 1)) (gf2_256Exec.ofBits 2) =
      gf2_256Exec.ofBits gf2_256SubfieldGenN := by
  decide +kernel

theorem gf2_256Val_subfieldGen :
    valVia gf2_256RingEquiv gf2_256Exec (gf2_256Exec.ofBits gf2_256SubfieldGenN) = gf2_256SubfieldGen := by
  rw [← gf2_256_pow_subfieldGen, gf2_256Rep.valVia_pow gf2_256RingEquiv (Rep.canon_ofBits _) (by norm_num),
    gf2_256Val_ofBits_two, gf2_256SubfieldGen]

/-- `g ^ (65535 / r) ≠ 1` for each prime factor `r` of `65535`. -/
theorem gf2_256_pow_subfieldGen_ne_one : ∀ r ∈ [3, 5, 17, 257],
    gf2_256Exec.pow 16 (65535 / r) (gf2_256Exec.ofBits gf2_256SubfieldGenN) ≠
      gf2_256Exec.ofBits 1 := by
  decide +kernel

theorem gf2_256SubfieldGen_pow_65535 : gf2_256SubfieldGen ^ 65535 = 1 := by
  rw [gf2_256SubfieldGen, ← pow_mul, show (2 ^ 256 - 1) / (2 ^ 16 - 1) * 65535 = 2 ^ 256 - 1 by
    norm_num, ← gf2_256_card]
  exact FiniteField.pow_card_sub_one_eq_one _ gf2_256_root_ne_zero

theorem orderOf_gf2_256SubfieldGen : orderOf gf2_256SubfieldGen = 65535 := by
  refine orderOf_eq_prod_of_pow_ne_one (l := [3, 5, 17, 257]) (by norm_num)
    gf2_256SubfieldGen_pow_65535 fun r hr h => gf2_256Val_ne
      (gf2_256Rep.canon_pow (Rep.canon_ofBits _) _ _ ((Nat.div_le_self _ _).trans_lt (by norm_num)))
      (Rep.canon_ofBits _) (gf2_256_pow_subfieldGen_ne_one r hr) ?_
  rw [gf2_256Rep.valVia_pow gf2_256RingEquiv (Rep.canon_ofBits _) ((Nat.div_le_self _ _).trans_lt (by norm_num)),
    gf2_256Val_subfieldGen,
    gf2_256Val_ofBits, gf2_256OfNat_one]
  exact h

theorem gf2_256SubfieldGen_mem : gf2_256SubfieldGen ∈ gf2_256Subfield := by
  rw [mem_gf2_256Subfield, show 2 ^ 16 = 65535 + 1 by norm_num, pow_succ,
    gf2_256SubfieldGen_pow_65535, one_mul]

theorem gf2_256SubfieldGen_ne_zero : gf2_256SubfieldGen ≠ 0 := fun h => by
  simpa [h] using gf2_256SubfieldGen_pow_65535

/-- The degree of `g` over `GF(2)` is at least `16`: its order `65535` is at most
`2 ^ d - 1`. -/
theorem sixteen_le_natDegree_minpoly_gf2_256SubfieldGen :
    16 ≤ (minpoly (ZMod 2) gf2_256SubfieldGen).natDegree :=
  gf2_256_le_natDegree_minpoly gf2_256SubfieldGen_ne_zero
    (by rw [orderOf_gf2_256SubfieldGen]; norm_num)

/-- The subfield basis `e i = g ^ i` (`beta_`, `lib/gf2k/gf2_256.h:120-124`). -/
def gf2_256SubfieldBasis (i : Fin 16) : GF2_256 := gf2_256SubfieldGen ^ (i : ℕ)

theorem gf2_256SubfieldBasis_mem (i : Fin 16) : gf2_256SubfieldBasis i ∈ gf2_256Subfield :=
  gf2_256Subfield.pow_mem gf2_256SubfieldGen_mem _

theorem linearIndependent_gf2_256SubfieldBasis :
    LinearIndependent (ZMod 2) gf2_256SubfieldBasis := by
  unfold gf2_256SubfieldBasis
  exact (linearIndependent_pow gf2_256SubfieldGen).comp
    (Fin.castLE sixteen_le_natDegree_minpoly_gf2_256SubfieldGen)
    (Fin.castLE_injective sixteen_le_natDegree_minpoly_gf2_256SubfieldGen)

/-- The selection field data of the `GF(2²⁵⁶)` H circuit. -/
def gf2_256SelectionField : SelectionField GF2_256 falcon512.S where
  E := gf2_256Subfield
  X := gf2_256Root
  X_not_mem := gf2_256_root_not_mem_subfield
  e := gf2_256SubfieldBasis
  e_mem := gf2_256SubfieldBasis_mem
  embed_injOn := selectionEmbed_injOn linearIndependent_gf2_256SubfieldBasis
  g := gf2_256SubfieldGen
  g_mem := gf2_256SubfieldGen_mem
  g_order a b ha hb h := by
    have hS : falcon512.S < 65535 := by decide
    refine pow_injOn_Iio_orderOf ?_ ?_ h <;>
      rw [Set.mem_Iio, orderOf_gf2_256SubfieldGen] <;> omega

end GordieHowe
