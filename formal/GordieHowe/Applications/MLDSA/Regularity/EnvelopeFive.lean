-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.Envelope

@[expose] public section

/-!
# The numerical envelope with small supports up to five

The envelope of `Envelope.lean` with the small-support block extended to `t ≤ 5`, for the bounds
`cellSupportDelta` (`SmallSupportBridge.lean`): `δ₁ ≤ 2^-512, δ₂ ≤ 2^-358, δ₃ ≤ 2^-214,
δ₄ ≤ 2^-99, δ₅ ≤ 2^-7`. The two-window block then starts at `t = 6`
(`∑ ≤ a^6 / (720 (1 - a))`), and dominates:

- `envelope_five_mldsa65`: the sum is at most `2^-296` (two-window term `2^-297.4`; the fixed
  masks use `X ≤ 1/22`);
- `envelope_five_mldsa87`: the sum is at most `2^-488` (two-window term `2^-489.4`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

/-- The three-block closure of `∑_t C(256, t) supportTerm t` for small supports up to `5`. -/
theorem sum_supportTerm_le_five {k ℓ G : ℕ} {δ : ℕ → ℝ} {S₁ T₂ : ℝ} (hS : 0 ≤ S₁) (hT₂ : 0 ≤ T₂)
    (ha : 256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k < 1) (hX : fixedMaskFactor S₁ k G ℓ ≤ 1) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else supportTerm 256 k ℓ G 5 δ S₁ T₂ t) ≤
      ∑ t ∈ range 6, ((256 : ℕ).choose t : ℝ) *
          (if t = 0 then 0 else ((G : ℝ) / (G : ℝ) ^ ℓ) ^ t * ((1 + δ t) ^ (2 * k) - 1)) +
        (256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k) ^ 6 /
          (720 * (1 - 256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k)) +
        2 ^ 256 * fixedMaskFactor S₁ k G ℓ ^ 129 := by
  set g : ℝ := (G : ℝ) / (G : ℝ) ^ ℓ
  set a : ℝ := 256 * g * T₂ ^ k
  set X := fixedMaskFactor S₁ k G ℓ
  have hg : 0 ≤ g := by positivity
  have ha0 : 0 ≤ a := by positivity
  have hX0 : 0 ≤ X := fixedMaskFactor_nonneg hS k G ℓ
  rw [← Finset.sum_range_add_sum_Ico _ (show 6 ≤ 257 by norm_num),
    ← Finset.sum_Ico_consecutive _ (show 6 ≤ 129 by norm_num) (show 129 ≤ 257 by norm_num)]
  have h1 : ∑ t ∈ range 6, ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else supportTerm 256 k ℓ G 5 δ S₁ T₂ t) =
      ∑ t ∈ range 6, ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else g ^ t * ((1 + δ t) ^ (2 * k) - 1)) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have : t ≤ 5 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    simp only [supportTerm, if_pos this, g]
  have h2 : ∑ t ∈ Ico 6 129, ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else supportTerm 256 k ℓ G 5 δ S₁ T₂ t) ≤ a ^ 6 / (720 * (1 - a)) := by
    calc _ ≤ ∑ t ∈ Ico 6 129, a ^ t / 720 := by
          refine Finset.sum_le_sum fun t ht => ?_
          obtain ⟨ht5, ht129⟩ := Finset.mem_Ico.mp ht
          have hne : t ≠ 0 := by omega
          have hnot : ¬ t ≤ 5 := by omega
          have hmed : t + t ≤ 256 := by omega
          simp only [if_neg hne, supportTerm, if_neg hnot, if_pos hmed]
          have hch : ((256 : ℕ).choose t : ℝ) ≤ (256 : ℝ) ^ t / t.factorial := by
            have := Nat.choose_le_pow_div (α := ℝ) t 256
            simpa using this
          have hfac : (720 : ℝ) ≤ t.factorial := by
            have : (6 : ℕ).factorial ≤ t.factorial := Nat.factorial_le ht5
            exact_mod_cast (show (720 : ℕ) ≤ t.factorial by simpa [Nat.factorial] using this)
          have hY : 0 ≤ g ^ t * (T₂ ^ t) ^ k := by positivity
          calc ((256 : ℕ).choose t : ℝ) * (g ^ t * (T₂ ^ t) ^ k)
              ≤ (256 : ℝ) ^ t / t.factorial * (g ^ t * (T₂ ^ t) ^ k) :=
                mul_le_mul_of_nonneg_right hch hY
            _ ≤ (256 : ℝ) ^ t / 720 * (g ^ t * (T₂ ^ t) ^ k) := by
                gcongr
            _ = a ^ t / 720 := by
                simp only [a]
                rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm t k]
                ring
      _ = (∑ t ∈ Ico 6 129, a ^ t) / 720 := by rw [Finset.sum_div]
      _ ≤ a ^ 6 / (1 - a) / 720 := by
          gcongr
          exact geom_sum_Ico_le_of_lt_one ha0 ha
      _ = a ^ 6 / (720 * (1 - a)) := by rw [div_div, mul_comm]
  have h3 : ∑ t ∈ Ico 129 257, ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else supportTerm 256 k ℓ G 5 δ S₁ T₂ t) ≤ 2 ^ 256 * X ^ 129 := by
    calc _ ≤ ∑ t ∈ range 257, ((256 : ℕ).choose t : ℝ) * X ^ 129 := by
          refine (Finset.sum_le_sum fun t ht => ?_).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => Finset.mem_range.mpr
              (Finset.mem_Ico.mp ht).2) fun t _ _ => by positivity)
          obtain ⟨ht1, ht2⟩ := Finset.mem_Ico.mp ht
          have hne : t ≠ 0 := by omega
          have hnot : ¬ t ≤ 5 := by omega
          have hbig : ¬ t + t ≤ 256 := by omega
          simp only [if_neg hne, supportTerm, if_neg hnot, if_neg hbig]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hX0 hX ht1) (by positivity)
      _ = 2 ^ 256 * X ^ 129 := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose 256
  rw [h1]
  linarith

theorem choose_256_five : (256 : ℕ).choose 5 = 8809549056 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; norm_num [Nat.descFactorial, Nat.factorial]

/-- The five small-support terms in explicit form. -/
theorem sum_range_six_smallTerms (g : ℝ) (k : ℕ) (δ : ℕ → ℝ) :
    ∑ t ∈ range 6, ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else g ^ t * ((1 + δ t) ^ (2 * k) - 1)) =
      256 * (g ^ 1 * ((1 + δ 1) ^ (2 * k) - 1)) + 32640 * (g ^ 2 * ((1 + δ 2) ^ (2 * k) - 1)) +
        2763520 * (g ^ 3 * ((1 + δ 3) ^ (2 * k) - 1)) +
        174792640 * (g ^ 4 * ((1 + δ 4) ^ (2 * k) - 1)) +
        8809549056 * (g ^ 5 * ((1 + δ 5) ^ (2 * k) - 1)) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one, if_pos rfl, if_neg one_ne_zero,
    if_neg two_ne_zero, if_neg three_ne_zero, if_neg four_ne_zero,
    if_neg (by norm_num : (5 : ℕ) ≠ 0), choose_256_one, choose_256_two, choose_256_three,
    choose_256_four, choose_256_five]
  push_cast
  ring

/-- The ML-DSA-65 envelope with small supports up to five: `∑_t C(256, t) supportTerm t ≤
2^-296`. -/
theorem envelope_five_mldsa65 {δ : ℕ → ℝ} (hδ0 : ∀ t, 0 ≤ δ t)
    (hδ1 : δ 1 ≤ 1 / (2 ^ 256) ^ 2) (hδ2 : δ 2 ≤ 1 / (2 ^ 179) ^ 2) (hδ3 : δ 3 ≤ 1 / 2 ^ 214)
    (hδ4 : δ 4 ≤ 1 / 2 ^ 99) (hδ5 : δ 5 ≤ 1 / 2 ^ 7) {S₁ : ℝ} (hS0 : 0 ≤ S₁) (hS : S₁ ≤ 610) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else supportTerm 256 6 5 1048183 5 δ S₁
          (8380417 ^ 2 / (16 * 523383 ^ 2)) t) ≤ 1 / 2 ^ 296 := by
  have hX : fixedMaskFactor S₁ 6 1048183 5 ≤ 1 / 22 :=
    (fixedMaskFactor_mono hS0 hS _ _ _).trans (by rw [fixedMaskFactor_eq]; norm_num)
  refine (sum_supportTerm_le_five hS0 (by positivity) (by norm_num) (hX.trans (by norm_num))).trans ?_
  have hX129 : fixedMaskFactor S₁ 6 1048183 5 ^ 129 ≤ (1 / 22) ^ 129 :=
    pow_le_pow_left₀ (fixedMaskFactor_nonneg hS0 _ _ _) hX _
  rw [sum_range_six_smallTerms]
  have e1 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 1) hδ1 (by norm_num)
  have e2 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 2) hδ2 (by norm_num)
  have e3 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 3) hδ3 (by norm_num)
  have e4 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 4) hδ4 (by norm_num)
  have e5 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 5) hδ5 (by norm_num)
  set g : ℝ := ((1048183 : ℕ) : ℝ) / (1048183 : ℝ) ^ 5
  have hg : 0 ≤ g := by positivity
  have hnum : 256 * (g ^ 1 * (2 * (2 * 6 : ℕ) * (1 / (2 ^ 256) ^ 2))) +
      32640 * (g ^ 2 * (2 * (2 * 6 : ℕ) * (1 / (2 ^ 179) ^ 2))) +
      2763520 * (g ^ 3 * (2 * (2 * 6 : ℕ) * (1 / 2 ^ 214))) +
      174792640 * (g ^ 4 * (2 * (2 * 6 : ℕ) * (1 / 2 ^ 99))) +
      8809549056 * (g ^ 5 * (2 * (2 * 6 : ℕ) * (1 / 2 ^ 7))) +
      (256 * g * (8380417 ^ 2 / (16 * 523383 ^ 2)) ^ 6) ^ 6 /
        (720 * (1 - 256 * g * (8380417 ^ 2 / (16 * 523383 ^ 2)) ^ 6)) +
      2 ^ 256 * (1 / 22) ^ 129 ≤ 1 / 2 ^ 296 := by
    rw [show (2 : ℝ) ^ 296 = (2 ^ 148) ^ 2 by rw [← pow_mul]]
    simp only [g]
    norm_num
  have hpow : ∀ t, 0 ≤ g ^ t := fun t => pow_nonneg hg t
  nlinarith [mul_le_mul_of_nonneg_left e1 (hpow 1), mul_le_mul_of_nonneg_left e2 (hpow 2),
    mul_le_mul_of_nonneg_left e3 (hpow 3), mul_le_mul_of_nonneg_left e4 (hpow 4),
    mul_le_mul_of_nonneg_left e5 (hpow 5),
    mul_le_mul_of_nonneg_left hX129 (by norm_num : (0 : ℝ) ≤ 2 ^ 256)]

/-- The ML-DSA-87 envelope with small supports up to five: `∑_t C(256, t) supportTerm t ≤
2^-488`. -/
theorem envelope_five_mldsa87 {δ : ℕ → ℝ} (hδ0 : ∀ t, 0 ≤ δ t)
    (hδ1 : δ 1 ≤ 1 / (2 ^ 256) ^ 2) (hδ2 : δ 2 ≤ 1 / (2 ^ 179) ^ 2) (hδ3 : δ 3 ≤ 1 / 2 ^ 214)
    (hδ4 : δ 4 ≤ 1 / 2 ^ 99) (hδ5 : δ 5 ≤ 1 / 2 ^ 7) {S₁ : ℝ} (hS0 : 0 ≤ S₁) (hS : S₁ ≤ 610) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else supportTerm 256 8 7 1048335 5 δ S₁
          (8380417 ^ 2 / (16 * 523535 ^ 2)) t) ≤ 1 / 2 ^ 488 := by
  have hX : fixedMaskFactor S₁ 8 1048335 7 ≤ 1 / 2 ^ 20 :=
    (fixedMaskFactor_mono hS0 hS _ _ _).trans (by rw [fixedMaskFactor_eq]; norm_num)
  refine (sum_supportTerm_le_five hS0 (by positivity) (by norm_num) (hX.trans (by norm_num))).trans ?_
  have hX129 : fixedMaskFactor S₁ 8 1048335 7 ^ 129 ≤ (1 / 2 ^ 20) ^ 129 :=
    pow_le_pow_left₀ (fixedMaskFactor_nonneg hS0 _ _ _) hX _
  rw [sum_range_six_smallTerms]
  have e1 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 1) hδ1 (by norm_num)
  have e2 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 2) hδ2 (by norm_num)
  have e3 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 3) hδ3 (by norm_num)
  have e4 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 4) hδ4 (by norm_num)
  have e5 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 5) hδ5 (by norm_num)
  set g : ℝ := ((1048335 : ℕ) : ℝ) / (1048335 : ℝ) ^ 7
  have hg : 0 ≤ g := by positivity
  have hnum : 256 * (g ^ 1 * (2 * (2 * 8 : ℕ) * (1 / (2 ^ 256) ^ 2))) +
      32640 * (g ^ 2 * (2 * (2 * 8 : ℕ) * (1 / (2 ^ 179) ^ 2))) +
      2763520 * (g ^ 3 * (2 * (2 * 8 : ℕ) * (1 / 2 ^ 214))) +
      174792640 * (g ^ 4 * (2 * (2 * 8 : ℕ) * (1 / 2 ^ 99))) +
      8809549056 * (g ^ 5 * (2 * (2 * 8 : ℕ) * (1 / 2 ^ 7))) +
      (256 * g * (8380417 ^ 2 / (16 * 523535 ^ 2)) ^ 8) ^ 6 /
        (720 * (1 - 256 * g * (8380417 ^ 2 / (16 * 523535 ^ 2)) ^ 8)) +
      2 ^ 256 * (1 / 2 ^ 20) ^ 129 ≤ 1 / 2 ^ 488 := by
    rw [show (2 : ℝ) ^ 488 = (2 ^ 244) ^ 2 by rw [← pow_mul]]
    simp only [g]
    norm_num
  have hpow : ∀ t, 0 ≤ g ^ t := fun t => pow_nonneg hg t
  nlinarith [mul_le_mul_of_nonneg_left e1 (hpow 1), mul_le_mul_of_nonneg_left e2 (hpow 2),
    mul_le_mul_of_nonneg_left e3 (hpow 3), mul_le_mul_of_nonneg_left e4 (hpow 4),
    mul_le_mul_of_nonneg_left e5 (hpow 5),
    mul_le_mul_of_nonneg_left hX129 (by norm_num : (0 : ℝ) ≤ 2 ^ 256)]

end GordieHowe.MLDSA.Regularity
