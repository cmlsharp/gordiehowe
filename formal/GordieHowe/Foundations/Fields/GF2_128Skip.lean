-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.GF2_128Selection
public import GordieHowe.ProofSystem.Zerocheck.UnivariateSkip
public import GordieHowe.Foundations.ToMathlib.OrderOf

@[expose] public section

/-!
# The eight-bit subfield of `GF(2¹²⁸)` and the skip domain

At the ROM parameters the proof system runs the Boolean zerocheck skip (`BooleanSkip`, `lib/sumcheck/boolean_skip.h`)
over `HashField = GF2_128<>` (`lib/params/param_sets.h`) at width `kSkipWidth = 16`
(`pq_profile.h:99`). It evaluates at the `2w - 1` points `embed[0], …, embed[2w - 2]`: the first `w`
are the zero domain (`basis(0, w, r)`, lines 244 and 381) and the next `w - 1` carry the skip
message (`for (unsigned x = w; x < w + extra(); ++x)`, line 181, with
`extra() = (D - 1)(w - 1) = w - 1` at the chi relation's degree `D = 2`, line 129; `skip_basis`,
`basis(0, D * (w - 1) + 1, r)`, lines 383-385). The table `embed` is built from a second field
object with an eight-bit subfield, `SkipByteField<GF2_128<k>>::type = GF2_128<3>` (lines 19-21), at
lines 96-100:

```
Small small_field;
for (unsigned i = 0; i < 256; ++i) {
  small_embed[i] = small_field.of_scalar(i);
  embed[i] = f.of_scalar_field(small_embed[i].unpack().u64());
}
```

`GF2_128<3>` has the same reduction polynomial and representation as `GF2_128<>`, so
`embed[i]` is `small_field.of_scalar(i)` read as an element of `GF2_128`. With
`subfield_log_bits = 3`, `of_scalar(u) = ∑_{k < 8} bit_k(u) · beta_[k]`
(`lib/gf2k/gf2_128.h:166-175`), `beta_[k] = h ^ k` (lines 127-131) and
`h = x ^ ((2¹²⁸ - 1) / (2⁸ - 1))` (`subfield_generator()`, lines 384-405, with the loop
from `i = kSubFieldLogBits = 3`). So `embed i = ∑_{k < 8} bit_k(i) · h ^ k`
(`gf2_128SkipEmbed`).

`h` has order `255 = 3 · 5 · 17` (a `decide +kernel` certificate at each prime, in the spread
representation `gf2_128Exec`), so its degree over `GF(2)` is at least `8`, `1, h, …, h⁷` are
linearly independent, and `gf2_128SkipEmbed` is injective below `256`, giving the `31` points of
`gf2_128SkipDomain`. The packed Keccak trace basis of the same field, a
`PackedClaim.PackedBasis GF2_128 4` of `GF(2¹⁶)`, is `gf2_128PackedBasis` (`GordieHowe.Foundations.Fields.GF2_128Dual`).
-/

namespace GordieHowe

open GF2_128Exec

/-- The eight-bit subfield `GF(2⁸)` of `GF2_128`: the fixed points of the `2⁸`-power map. -/
def gf2_128SkipSubfield : Subfield GF2_128 :=
  (iterateFrobenius GF2_128 2 8).eqLocusField (RingHom.id _)

theorem mem_gf2_128SkipSubfield {y : GF2_128} : y ∈ gf2_128SkipSubfield ↔ y ^ 2 ^ 8 = y :=
  Iff.rfl

/-- The eight-bit subfield generator `h = x ^ ((2¹²⁸ - 1) / (2⁸ - 1))`
(`subfield_generator()` of `GF2_128<3>`, `lib/gf2k/gf2_128.h:384-406`). -/
def gf2_128SkipGen : GF2_128 :=
  gf2_128Root ^ ((2 ^ 128 - 1) / (2 ^ 8 - 1))

/-- `gf2_128SkipGen` as bits, computed offline; `gfPow_skipGen` checks it. -/
def gf2_128SkipGenBV : BitVec 128 := 0xe6114072b8ca57afd9db18ed46787786#128

theorem gfPow_skipGen : gfPow 128 ((2 ^ 128 - 1) / (2 ^ 8 - 1)) 2 = gf2_128SkipGenBV :=
  gfPow_eq_of_spread (by norm_num) (by decide +kernel)

theorem gf2_128OfBitVec_skipGenBV : gf2_128OfBitVec gf2_128SkipGenBV = gf2_128SkipGen := by
  rw [← gfPow_skipGen, gf2_128OfBitVec_gfPow (by norm_num), gf2_128OfBitVec_two, gf2_128SkipGen]

/-- `h ^ (255 / r) ≠ 1` for each prime factor `r` of `255`. -/
theorem gfPow_skipGenBV_ne_one : ∀ r ∈ [3, 5, 17], gfPow 8 (255 / r) gf2_128SkipGenBV ≠ 1 := by
  have h : ∀ r ∈ [3, 5, 17], gf2_128Exec.pow 8 (255 / r) (gf2_128Exec.ofBits gf2_128SkipGenBV.toNat) ≠
      gf2_128Exec.ofBits (1 : BitVec 128).toNat := by
    decide +kernel
  exact fun r hr => gfPow_ne_of_spread ((Nat.div_le_self _ _).trans_lt (by norm_num)) (h r hr)

theorem gf2_128SkipGen_pow_255 : gf2_128SkipGen ^ 255 = 1 := by
  rw [gf2_128SkipGen, ← pow_mul, show (2 ^ 128 - 1) / (2 ^ 8 - 1) * 255 = 2 ^ 128 - 1 by
    norm_num, ← gf2_128_card]
  exact FiniteField.pow_card_sub_one_eq_one _ gf2_128_root_ne_zero

theorem orderOf_gf2_128SkipGen : orderOf gf2_128SkipGen = 255 := by
  refine orderOf_eq_prod_of_pow_ne_one (l := [3, 5, 17]) (by norm_num)
    gf2_128SkipGen_pow_255 fun r hr h => gfPow_skipGenBV_ne_one r hr
      (gf2_128OfBitVec_injective ?_)
  rw [gf2_128OfBitVec_gfPow ((Nat.div_le_self _ _).trans_lt (by norm_num)),
    gf2_128OfBitVec_skipGenBV, gf2_128OfBitVec_one]
  exact h

theorem gf2_128SkipGen_mem : gf2_128SkipGen ∈ gf2_128SkipSubfield := by
  rw [mem_gf2_128SkipSubfield, show 2 ^ 8 = 255 + 1 by norm_num, pow_succ,
    gf2_128SkipGen_pow_255, one_mul]

theorem gf2_128SkipGen_ne_zero : gf2_128SkipGen ≠ 0 := fun h => by
  simpa [h] using gf2_128SkipGen_pow_255

theorem eight_le_natDegree_minpoly_gf2_128SkipGen :
    8 ≤ (minpoly (ZMod 2) gf2_128SkipGen).natDegree :=
  le_natDegree_minpoly_of_card_pow_le_orderOf (.of_finite _ _) gf2_128SkipGen_ne_zero
    (by rw [Nat.card_zmod, orderOf_gf2_128SkipGen]; norm_num)

/-- The basis `beta_[k] = h ^ k` of `GF2_128<3>`'s subfield (`lib/gf2k/gf2_128.h:127-131`). -/
def gf2_128SkipBasis (k : Fin 8) : GF2_128 := gf2_128SkipGen ^ (k : ℕ)

theorem linearIndependent_gf2_128SkipBasis : LinearIndependent (ZMod 2) gf2_128SkipBasis := by
  unfold gf2_128SkipBasis
  exact (linearIndependent_pow gf2_128SkipGen).comp
    (Fin.castLE eight_le_natDegree_minpoly_gf2_128SkipGen)
    (Fin.castLE_injective eight_le_natDegree_minpoly_gf2_128SkipGen)

/-- `embed[i] = small_field.of_scalar(i) = ∑_{k < 8} bit_k(i) · h ^ k`
(`lib/sumcheck/boolean_skip.h:96-100`; `of_scalar`, `lib/gf2k/gf2_128.h:166-175`). -/
def gf2_128SkipEmbed (i : ℕ) : GF2_128 :=
  ∑ k : Fin 8, if i.testBit k then gf2_128SkipBasis k else 0

theorem gf2_128SkipEmbed_mem (i : ℕ) : gf2_128SkipEmbed i ∈ gf2_128SkipSubfield := by
  refine gf2_128SkipSubfield.sum_mem fun k _ => ?_
  split_ifs
  · exact gf2_128SkipSubfield.pow_mem gf2_128SkipGen_mem _
  · exact gf2_128SkipSubfield.zero_mem

/-- `embed` is injective on `[0, 256)`: the eight bits are coefficients against a
linearly independent basis. -/
theorem gf2_128SkipEmbed_injOn : Set.InjOn gf2_128SkipEmbed (Set.Iio 256) := by
  intro i hi j hj h
  have hb := boolSum_injective linearIndependent_gf2_128SkipBasis h
  refine Nat.eq_of_testBit_eq fun t => ?_
  by_cases ht : t < 8
  · exact congrFun hb ⟨t, ht⟩
  · have h8 : 2 ^ 8 ≤ 2 ^ t := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow ((Set.mem_Iio.mp hi).trans_le h8),
      Nat.testBit_lt_two_pow ((Set.mem_Iio.mp hj).trans_le h8)]

/-- The skip domain of the batched-Keccak H circuit at the ROM parameters, at width `16`: `31` distinct points
`embed[0], …, embed[30]` of the eight-bit subfield (`lib/sumcheck/boolean_skip.h:96-100, 181,
244, 383-385`). -/
def gf2_128SkipDomain : Sumcheck.UnivariateSkip.SkipDomain GF2_128 16 :=
  .ofEmbed gf2_128SkipEmbed (gf2_128SkipEmbed_injOn.mono (Set.Iio_subset_Iio (by norm_num)))

theorem gf2_128SkipDomain_mem (x : Fin 16 ⊕ Fin 15) :
    gf2_128SkipDomain.point x ∈ gf2_128SkipSubfield :=
  gf2_128SkipEmbed_mem _

end GordieHowe
