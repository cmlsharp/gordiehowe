-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PairKernel
public import GordieHowe.Foundations.ToMathlib.CharacterSums

@[expose] public section

/-!
# The indicator of a small count as a character sum

For counts `k < M`, `1[k ≤ ω] = ∑_{t : ZMod M} c_t e(t k)` with
`c_t = M⁻¹ ∑_{j ≤ ω} e(-t j)` (`ZMod.indicator_le_eq_sum`). Since `e(t k)` with `k` a count of
events is the product of the per-event factors `e(t)`, this writes the hint-count check of the
HighBits regularity argument as a combination of product functions (plan, item 3).

`ZMod.norm_countCoeff_le`: for `t ≠ 0`, `‖c_t‖ ≤ 1 / (2 |t|)`, from the interval character sum
bound `ZMod.norm_sum_stdAddChar_le`.
-/

open Finset
open scoped BigOperators

namespace ZMod

variable {M : ℕ} [NeZero M]

/-- The coefficient `c_t = M⁻¹ ∑_{j ≤ ω} e(-t j)` of the expansion of `1[k ≤ ω]`. -/
noncomputable def countCoeff (M ω : ℕ) [NeZero M] (t : ZMod M) : ℂ :=
  (M : ℂ)⁻¹ * ∑ j ∈ range (ω + 1), stdAddChar (-(t * (j : ZMod M)))

/-- **The indicator of a small count**: `1[k ≤ ω] = ∑_t c_t e(t k)` for `k < M` and `ω < M`. -/
theorem indicator_le_eq_sum {ω k : ℕ} (hω : ω < M) (hk : k < M) :
    (if k ≤ ω then (1 : ℂ) else 0) =
      ∑ t : ZMod M, countCoeff M ω t * stdAddChar (t * (k : ZMod M)) := by
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  simp only [countCoeff, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hj : ∀ j ∈ range (ω + 1), ∑ t : ZMod M, (M : ℂ)⁻¹ * stdAddChar (-(t * (j : ZMod M))) *
      stdAddChar (t * (k : ZMod M)) = if j = k then 1 else 0 := by
    intro j hj
    have : ∀ t : ZMod M, (M : ℂ)⁻¹ * stdAddChar (-(t * (j : ZMod M))) * stdAddChar (t * (k : ZMod M)) =
        (M : ℂ)⁻¹ * stdAddChar (t * ((k : ZMod M) - (j : ZMod M))) := by
      intro t
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    simp_rw [this]
    rw [← Finset.mul_sum, sum_stdAddChar_mul]
    simp only [sub_eq_zero]
    have hjM : j < M := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hω
    have hiff : ((k : ZMod M) = j) ↔ j = k := by
      rw [eq_comm, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hjM, Nat.mod_eq_of_lt hk]
    by_cases h : j = k
    · rw [if_pos (hiff.mpr h), if_pos h, inv_mul_cancel₀ hM]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hj, Finset.sum_ite_eq']
  simp only [Finset.mem_range]
  split_ifs <;> first | rfl | omega

/-- `‖c_t‖ ≤ 1 / (2 |t|)` for `t ≠ 0`. -/
theorem norm_countCoeff_le (ω : ℕ) {t : ZMod M} (ht : t ≠ 0) :
    ‖countCoeff M ω t‖ ≤ 1 / (2 * |((-t).valMinAbs : ℝ)|) := by
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)
  have h := norm_sum_stdAddChar_le (neg_ne_zero.mpr ht) 0 (ω + 1)
  have hrw : ∑ u ∈ range (ω + 1), stdAddChar ((0 + (u : ZMod M)) * -t) =
      ∑ j ∈ range (ω + 1), stdAddChar (-(t * (j : ZMod M))) :=
    Finset.sum_congr rfl fun j _ => by ring_nf
  rw [hrw] at h
  rw [countCoeff, norm_mul, norm_inv, Complex.norm_natCast]
  calc (M : ℝ)⁻¹ * ‖∑ j ∈ range (ω + 1), stdAddChar (-(t * (j : ZMod M)))‖
      ≤ (M : ℝ)⁻¹ * (M / (2 * |((-t).valMinAbs : ℝ)|)) := by gcongr
    _ = 1 / (2 * |((-t).valMinAbs : ℝ)|) := by field_simp

/-- `‖c_0‖ = (ω + 1) / M`. -/
theorem norm_countCoeff_zero (ω : ℕ) : ‖countCoeff M ω 0‖ ≤ (ω + 1) / M := by
  rw [countCoeff]
  simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, norm_mul, norm_inv, Complex.norm_natCast]
  rw [inv_mul_eq_div]
  push_cast
  rfl

end ZMod
