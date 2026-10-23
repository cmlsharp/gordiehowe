-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.GF2_256Selection
public import GordieHowe.ProofSystem.Zerocheck.UnivariateSkip

@[expose] public section

/-!
# The eight-bit subfield of `GF(2²⁵⁶)` and the skip domain

The Boolean zerocheck skip (`BooleanSkip`, `lib/sumcheck/boolean_skip.h`)
evaluates at the `2w - 1` points `embed[0], …, embed[2w - 2]`: the first `w` are the zero
domain (`basis(0, w, r)`, lines 244 and 381) and the next `w - 1` carry the skip message
(`for (unsigned x = w; x < w + extra(); ++x)`, line 181, with `extra() = (D - 1)(w - 1) = w - 1`
at the chi relation's degree `D = 2`, line 129; `skip_basis`, `basis(0, D * (w - 1) + 1, r)`,
lines 383-385). The table `embed` is built from a second field object with an eight-bit
subfield, `SkipByteField<GF2_256<k>>::type = GF2_256<3>` (lines 22-24), at lines 96-100:

```
Small small_field;
for (unsigned i = 0; i < 256; ++i) {
  small_embed[i] = small_field.of_scalar(i);
  embed[i] = f.of_scalar_field(small_embed[i].unpack().u64());
}
```

`GF2_256<3>` has the same reduction polynomial and representation as `GF2_256<>`, so
`embed[i]` is `small_field.of_scalar(i)` read as an element of `GF2_256`. With
`subfield_log_bits = 3`, `of_scalar(i) = ∑_{k < 8} bit_k(i) · beta_[k]`
(`lib/gf2k/gf2_256.h:167-173`), `beta_[k] = h ^ k` (lines 120-124) and
`h = x ^ ((2²⁵⁶ - 1) / (2⁸ - 1))` (`subfield_generator()`, lines 372-394, with the loop
from `i = 3`). So `embed i = ∑_{k < 8} bit_k(i) · h ^ k` (`gf2_256SkipEmbed`).

`h` has order `255 = 3 · 5 · 17` (a `decide +kernel` certificate at each prime), so its
degree over `GF(2)` is at least `8`, `1, h, …, h⁷` are linearly independent, and
`gf2_256SkipEmbed` is injective below `256`. The skip width is `w = 16`, giving the `31`
points of `gf2_256SkipDomain`.
-/

namespace GordieHowe

open BinarySpread

/-- The eight-bit subfield `GF(2⁸)` of `GF2_256`: the fixed points of the `2⁸`-power map. -/
def gf2_256SkipSubfield : Subfield GF2_256 :=
  (iterateFrobenius GF2_256 2 8).eqLocusField (RingHom.id _)

theorem mem_gf2_256SkipSubfield {y : GF2_256} : y ∈ gf2_256SkipSubfield ↔ y ^ 2 ^ 8 = y :=
  Iff.rfl

/-- The eight-bit subfield generator `h = x ^ ((2²⁵⁶ - 1) / (2⁸ - 1))`
(`subfield_generator()` of `GF2_256<3>`, `lib/gf2k/gf2_256.h:372-394`). -/
def gf2_256SkipGen : GF2_256 :=
  gf2_256Root ^ ((2 ^ 256 - 1) / (2 ^ 8 - 1))

/-- `gf2_256SkipGen` as bits, computed offline; `gf2_256_pow_skipGen` checks it. -/
def gf2_256SkipGenN : ℕ := 0xd7ca75e923580a7800469650fe80eb50400c2f28e30e8ed7b2a1916266a97053

theorem gf2_256_pow_skipGen :
    gf2_256Exec.pow 256 ((2 ^ 256 - 1) / (2 ^ 8 - 1)) (gf2_256Exec.ofBits 2) =
      gf2_256Exec.ofBits gf2_256SkipGenN := by
  decide +kernel

theorem gf2_256Val_skipGen :
    valVia gf2_256RingEquiv gf2_256Exec (gf2_256Exec.ofBits gf2_256SkipGenN) = gf2_256SkipGen := by
  rw [← gf2_256_pow_skipGen, gf2_256Rep.valVia_pow gf2_256RingEquiv (Rep.canon_ofBits _) (by norm_num),
    gf2_256Val_ofBits_two, gf2_256SkipGen]

/-- `h ^ (255 / r) ≠ 1` for each prime factor `r` of `255`. -/
theorem gf2_256_pow_skipGen_ne_one : ∀ r ∈ [3, 5, 17],
    gf2_256Exec.pow 8 (255 / r) (gf2_256Exec.ofBits gf2_256SkipGenN) ≠ gf2_256Exec.ofBits 1 := by
  decide +kernel

theorem gf2_256SkipGen_pow_255 : gf2_256SkipGen ^ 255 = 1 := by
  rw [gf2_256SkipGen, ← pow_mul, show (2 ^ 256 - 1) / (2 ^ 8 - 1) * 255 = 2 ^ 256 - 1 by
    norm_num, ← gf2_256_card]
  exact FiniteField.pow_card_sub_one_eq_one _ gf2_256_root_ne_zero

theorem orderOf_gf2_256SkipGen : orderOf gf2_256SkipGen = 255 := by
  refine orderOf_eq_prod_of_pow_ne_one (l := [3, 5, 17]) (by norm_num)
    gf2_256SkipGen_pow_255 fun r hr h => gf2_256Val_ne
      (gf2_256Rep.canon_pow (Rep.canon_ofBits _) _ _ ((Nat.div_le_self _ _).trans_lt (by norm_num)))
      (Rep.canon_ofBits _) (gf2_256_pow_skipGen_ne_one r hr) ?_
  rw [gf2_256Rep.valVia_pow gf2_256RingEquiv (Rep.canon_ofBits _) ((Nat.div_le_self _ _).trans_lt (by norm_num)),
    gf2_256Val_skipGen, gf2_256Val_ofBits, gf2_256OfNat_one]
  exact h

theorem gf2_256SkipGen_mem : gf2_256SkipGen ∈ gf2_256SkipSubfield := by
  rw [mem_gf2_256SkipSubfield, show 2 ^ 8 = 255 + 1 by norm_num, pow_succ,
    gf2_256SkipGen_pow_255, one_mul]

theorem gf2_256SkipGen_ne_zero : gf2_256SkipGen ≠ 0 := fun h => by
  simpa [h] using gf2_256SkipGen_pow_255

theorem eight_le_natDegree_minpoly_gf2_256SkipGen :
    8 ≤ (minpoly (ZMod 2) gf2_256SkipGen).natDegree :=
  gf2_256_le_natDegree_minpoly gf2_256SkipGen_ne_zero (by rw [orderOf_gf2_256SkipGen]; norm_num)

/-- The basis `beta_[k] = h ^ k` of `GF2_256<3>`'s subfield (`lib/gf2k/gf2_256.h:120-124`). -/
def gf2_256SkipBasis (k : Fin 8) : GF2_256 := gf2_256SkipGen ^ (k : ℕ)

theorem linearIndependent_gf2_256SkipBasis : LinearIndependent (ZMod 2) gf2_256SkipBasis := by
  unfold gf2_256SkipBasis
  exact (linearIndependent_pow gf2_256SkipGen).comp
    (Fin.castLE eight_le_natDegree_minpoly_gf2_256SkipGen)
    (Fin.castLE_injective eight_le_natDegree_minpoly_gf2_256SkipGen)

/-- `embed[i] = small_field.of_scalar(i) = ∑_{k < 8} bit_k(i) · h ^ k`
(`lib/sumcheck/boolean_skip.h:96-100`; `of_scalar`, `lib/gf2k/gf2_256.h:167-173`). -/
def gf2_256SkipEmbed (i : ℕ) : GF2_256 :=
  ∑ k : Fin 8, if i.testBit k then gf2_256SkipBasis k else 0

theorem gf2_256SkipEmbed_mem (i : ℕ) : gf2_256SkipEmbed i ∈ gf2_256SkipSubfield := by
  refine gf2_256SkipSubfield.sum_mem fun k _ => ?_
  split_ifs
  · exact gf2_256SkipSubfield.pow_mem gf2_256SkipGen_mem _
  · exact gf2_256SkipSubfield.zero_mem

/-- `embed` is injective on `[0, 256)`: the eight bits are coefficients against a
linearly independent basis. -/
theorem gf2_256SkipEmbed_injOn : Set.InjOn gf2_256SkipEmbed (Set.Iio 256) := by
  intro i hi j hj h
  have hb := boolSum_injective linearIndependent_gf2_256SkipBasis h
  refine Nat.eq_of_testBit_eq fun t => ?_
  by_cases ht : t < 8
  · exact congrFun hb ⟨t, ht⟩
  · have h8 : 2 ^ 8 ≤ 2 ^ t := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow ((Set.mem_Iio.mp hi).trans_le h8),
      Nat.testBit_lt_two_pow ((Set.mem_Iio.mp hj).trans_le h8)]

/-- The skip domain of the batched-Keccak H circuit at width `16`: `31` distinct points
`embed[0], …, embed[30]` of the eight-bit subfield (`lib/sumcheck/boolean_skip.h:96-100,
181, 244, 383-385`). -/
def gf2_256SkipDomain : Sumcheck.UnivariateSkip.SkipDomain GF2_256 16 :=
  .ofEmbed gf2_256SkipEmbed (gf2_256SkipEmbed_injOn.mono (Set.Iio_subset_Iio (by norm_num)))

theorem gf2_256SkipDomain_mem (x : Fin 16 ⊕ Fin 15) :
    gf2_256SkipDomain.point x ∈ gf2_256SkipSubfield :=
  gf2_256SkipEmbed_mem _

end GordieHowe
