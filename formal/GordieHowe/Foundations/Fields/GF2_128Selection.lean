-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.GF2_128
public import GordieHowe.Applications.Params
public import GordieHowe.Applications.Spec.SelectionField
public import GordieHowe.Foundations.ToMathlib.FiniteField
public import GordieHowe.Foundations.Algebra.RecordPacking

@[expose] public section

/-!
# The selection field data of `GF(2¹²⁸)`

`gf2_128SelectionField` is the `SelectionField GF2_128 falcon512.S` the
flagship uses, with the constants of `lib/gf2k/gf2_128.h` (class `GF2_128`,
`subfield_log_bits = 4`):

* `E` is the sixteen-bit subfield, the fixed points of `y ↦ y ^ 2¹⁶`;
* `X` is the polynomial variable `x` (`kx_ = of_scalar_field(0b10)`, line 114);
* `g` is `x ^ ((2¹²⁸ - 1) / (2¹⁶ - 1))` (`subfield_generator()`, lines 384-406,
  which computes the exponent as `(2¹⁶ + 1)(2³² + 1)(2⁶⁴ + 1)`; `kg_`, line 124);
* `e i = g ^ i` for `i < 16` (`beta_`, lines 127-131).

The facts about concrete elements are `gfMul` computations checked by `decide +kernel` in the spread
representation `gf2_128Exec` (`gfPow_eq_of_spread`) and carried to `GF2_128` by `gf2_128OfBitVec`:
`g` equals the bits `gf2_128SubfieldGenBV`, `g ^ (65535 / r) ≠ 1` for the prime factors `r` of
`65535 = 3 · 5 · 17 · 257`, and `x ^ 2¹⁶ ≠ x`. So `g` has order `65535`, which gives `g ∈ E`,
distinct powers up to `S`, and, since `65535` divides `2^d - 1` for the degree `d` of `g` over
`GF(2)`, `d ≥ 16`, which makes `1, g, …, g¹⁵` linearly independent.
-/

namespace GordieHowe

open GF2_128Exec

/-! ## The subfield -/

/-- The sixteen-bit subfield `GF(2¹⁶)` of `GF2_128`: the fixed points of the
`2¹⁶`-power Frobenius map. The C++ never names it; its `beta_` spans it
(`lib/gf2k/gf2_128.h:127-131`, `in_subfield`, lines 216-219). -/
def gf2_128Subfield : Subfield GF2_128 :=
  (iterateFrobenius GF2_128 2 16).eqLocusField (RingHom.id _)

theorem mem_gf2_128Subfield {y : GF2_128} : y ∈ gf2_128Subfield ↔ y ^ 2 ^ 16 = y :=
  Iff.rfl

/-! ## The variable `x` -/

theorem sqPow_16_two_ne : sqPow 16 2 ≠ 2 :=
  sqPow_ne_of_spread (by decide +kernel)

/-- The polynomial variable is outside the subfield: `x ^ 2¹⁶ ≠ x`. -/
theorem gf2_128_root_not_mem_subfield : gf2_128Root ∉ gf2_128Subfield := by
  rw [mem_gf2_128Subfield, ← gf2_128OfBitVec_two, ← gf2_128OfBitVec_sqPow]
  exact fun h => sqPow_16_two_ne (gf2_128OfBitVec_injective h)

theorem sqPow_32_two_ne : sqPow 32 2 ≠ 2 :=
  sqPow_ne_of_spread (by decide +kernel)

/-- The polynomial variable lies in no quadratic extension of the subfield: `x ^ 2³² ≠ x`. -/
theorem gf2_128_root_pow_two_pow_32_ne : gf2_128Root ^ 2 ^ 32 ≠ gf2_128Root := by
  rw [← gf2_128OfBitVec_two, ← gf2_128OfBitVec_sqPow]
  exact fun h => sqPow_32_two_ne (gf2_128OfBitVec_injective h)

/-- **The record packing at `x` is injective on triples of the subfield**
(`lib/gordiehowe/lib/permutation.h:26-31`, `selection_kappa`): `x` lies in no extension of degree
`1` or `2` of `GF(2¹⁶)` (`RecordPacking.pack_injOn`). -/
theorem gf2_128_pack_injOn {a b : Fin 3 → GF2_128} (ha : ∀ i, a i ∈ gf2_128Subfield)
    (hb : ∀ i, b i ∈ gf2_128Subfield)
    (h : RecordPacking.pack gf2_128Root a = RecordPacking.pack gf2_128Root b) : a = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine RecordPacking.pack_injOn (p := 2) (k := 16) (E := gf2_128Subfield)
    (fun y hy => mem_gf2_128Subfield.mp hy) (fun m hm hm3 => ?_) ha hb h
  interval_cases m
  · rw [pow_one]
    exact gf2_128_root_not_mem_subfield
  · rw [← pow_mul]
    exact gf2_128_root_pow_two_pow_32_ne

theorem gf2_128_root_ne_zero : gf2_128Root ≠ 0 := fun h =>
  gf2_128_root_not_mem_subfield (by rw [mem_gf2_128Subfield, h, zero_pow (by norm_num)])

/-! ## The subfield generator -/

/-- The subfield generator `g = x ^ ((2¹²⁸ - 1) / (2¹⁶ - 1))`
(`subfield_generator()`, `lib/gf2k/gf2_128.h:384-406`; `kg_`, line 124). -/
def gf2_128SubfieldGen : GF2_128 :=
  gf2_128Root ^ ((2 ^ 128 - 1) / (2 ^ 16 - 1))

/-- `gf2_128SubfieldGen` as bits, computed with `gfPow`; `gfPow_subfieldGen` checks it. -/
def gf2_128SubfieldGenBV : BitVec 128 := 0x5c5971877501d4b8f1871e01b64fda4c#128

theorem gfPow_subfieldGen : gfPow 128 ((2 ^ 128 - 1) / (2 ^ 16 - 1)) 2 = gf2_128SubfieldGenBV :=
  gfPow_eq_of_spread (by norm_num) (by decide +kernel)

theorem gf2_128OfBitVec_subfieldGenBV :
    gf2_128OfBitVec gf2_128SubfieldGenBV = gf2_128SubfieldGen := by
  rw [← gfPow_subfieldGen, gf2_128OfBitVec_gfPow (by norm_num), gf2_128OfBitVec_two,
    gf2_128SubfieldGen]

/-- `g ^ (65535 / r) ≠ 1` for each prime factor `r` of `65535`. -/
theorem gfPow_subfieldGenBV_ne_one :
    ∀ r ∈ [3, 5, 17, 257], gfPow 16 (65535 / r) gf2_128SubfieldGenBV ≠ 1 := by
  have h : ∀ r ∈ [3, 5, 17, 257], gf2_128Exec.pow 16 (65535 / r)
      (gf2_128Exec.ofBits gf2_128SubfieldGenBV.toNat) ≠ gf2_128Exec.ofBits (1 : BitVec 128).toNat := by
    decide +kernel
  exact fun r hr => gfPow_ne_of_spread ((Nat.div_le_self _ _).trans_lt (by norm_num)) (h r hr)

theorem gf2_128SubfieldGen_pow_65535 : gf2_128SubfieldGen ^ 65535 = 1 := by
  rw [gf2_128SubfieldGen, ← pow_mul, show (2 ^ 128 - 1) / (2 ^ 16 - 1) * 65535 = 2 ^ 128 - 1 by
    norm_num, ← gf2_128_card]
  exact FiniteField.pow_card_sub_one_eq_one _ gf2_128_root_ne_zero

theorem orderOf_gf2_128SubfieldGen : orderOf gf2_128SubfieldGen = 65535 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) gf2_128SubfieldGen_pow_65535
    fun p hp hdvd => ?_
  have hr : p ∈ [3, 5, 17, 257] := by
    rw [show 65535 = 3 * (5 * (17 * 257)) by norm_num] at hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hp.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
    rcases hp.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
    rcases hp.dvd_mul.mp hdvd with h | h
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)))
  intro h
  refine gfPow_subfieldGenBV_ne_one p hr (gf2_128OfBitVec_injective ?_)
  rw [gf2_128OfBitVec_gfPow (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by norm_num)),
    gf2_128OfBitVec_subfieldGenBV, h, gf2_128OfBitVec_one]

theorem gf2_128SubfieldGen_mem : gf2_128SubfieldGen ∈ gf2_128Subfield := by
  rw [mem_gf2_128Subfield, show 2 ^ 16 = 65535 + 1 by norm_num, pow_succ,
    gf2_128SubfieldGen_pow_65535, one_mul]

/-- The degree of `g` over `GF(2)` is at least `16`: `g` is fixed by the
`2^d`-power map, so its order `65535` divides `2^d - 1`. -/
theorem sixteen_le_natDegree_minpoly_subfieldGen :
    16 ≤ (minpoly (ZMod 2) gf2_128SubfieldGen).natDegree := by
  have hint : IsIntegral (ZMod 2) gf2_128SubfieldGen := .of_finite _ _
  have hpos := minpoly.natDegree_pos hint
  set d := (minpoly (ZMod 2) gf2_128SubfieldGen).natDegree
  have hfix := pow_card_pow_natDegree_minpoly hint
  rw [Nat.card_zmod] at hfix
  have hne : gf2_128SubfieldGen ≠ 0 := fun h => by
    simpa [h] using gf2_128SubfieldGen_pow_65535
  have hone : gf2_128SubfieldGen ^ (2 ^ d - 1) = 1 := by
    refine mul_left_cancel₀ hne ?_
    rw [← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow, hfix, mul_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hone
  rw [orderOf_gf2_128SubfieldGen] at hdvd
  by_contra hlt
  have hle : 2 ^ d ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := Nat.le_of_dvd (by have := Nat.one_lt_two_pow (n := d) (by omega); omega) hdvd
  omega

/-- The subfield basis `e i = g ^ i` (`beta_`, `lib/gf2k/gf2_128.h:127-131`). -/
def gf2_128SubfieldBasis (i : Fin 16) : GF2_128 := gf2_128SubfieldGen ^ (i : ℕ)

theorem linearIndependent_gf2_128SubfieldBasis :
    LinearIndependent (ZMod 2) gf2_128SubfieldBasis := by
  unfold gf2_128SubfieldBasis
  exact (linearIndependent_pow gf2_128SubfieldGen).comp
    (Fin.castLE sixteen_le_natDegree_minpoly_subfieldGen)
    (Fin.castLE_injective sixteen_le_natDegree_minpoly_subfieldGen)

/-- The selection field data of the flagship `GF(2¹²⁸)` circuits. -/
def gf2_128SelectionField : SelectionField GF2_128 falcon512.S where
  E := gf2_128Subfield
  X := gf2_128Root
  X_not_mem := gf2_128_root_not_mem_subfield
  e := gf2_128SubfieldBasis
  e_mem i := gf2_128Subfield.pow_mem gf2_128SubfieldGen_mem _
  embed_injOn := selectionEmbed_injOn linearIndependent_gf2_128SubfieldBasis
  g := gf2_128SubfieldGen
  g_mem := gf2_128SubfieldGen_mem
  g_order a b ha hb h := by
    have hS : falcon512.S < 65535 := by decide
    refine pow_injOn_Iio_orderOf ?_ ?_ h <;>
      rw [Set.mem_Iio, orderOf_gf2_128SubfieldGen] <;> omega

end GordieHowe
