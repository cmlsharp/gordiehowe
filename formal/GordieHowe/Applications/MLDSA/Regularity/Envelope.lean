-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.SecondMoment
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-!
# The numerical envelope of the second moment at ML-DSA-65 and ML-DSA-87

`averagedSecondMoment_le` bounds the averaged second moment by
`∑_{t=1}^{256} C(256, t) · supportTerm t`. With small-support bounds for `t ≤ 4`, this file
closes that sum in three blocks:

- `t ≤ 4`: four explicit terms, with `(1 + δ)^N - 1 ≤ 2Nδ` for `Nδ ≤ 1/2`
  (`one_add_pow_sub_one_le`);
- `5 ≤ t ≤ 128` (two windows): `C(256, t) ≤ 256^t / t!` and a geometric series,
  `∑ ≤ a^5 / (120 (1 - a))` with `a = 256 G^{-(ℓ-1)} T₂^k`;
- `129 ≤ t ≤ 256` (fixed masks): `∑ ≤ 2^256 X^129` for the per-slot factor `X ≤ 1`.

`envelope_mldsa65`, `envelope_mldsa87`: the sum is at most `2^-246` and `2^-406` for the
parameters of ML-DSA-65 (`k = 6, ℓ = 5`, `L = 523383`, `G = 1048183`) and ML-DSA-87
(`k = 8, ℓ = 7`, `L = 523535`, `G = 1048335`), with `T₂ = q² / (16 L²)`, `S₁ ≤ 610` and the
small-support bounds `δ₁ ≤ 2^-512 = (2^256)^-2, δ₂ ≤ 2^-210, δ₃ ≤ 2^-155, δ₄ ≤ 2^-52`. The block `t = 5`
dominates (`2^-246.8` and `2^-406.8`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

/-- `(1 + x)^N - 1 ≤ 2 N x` for `0 ≤ x` and `N x ≤ 1/2`. -/
theorem one_add_pow_sub_one_le {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : N * x ≤ 1 / 2) :
    (1 + x) ^ N - 1 ≤ 2 * N * x := by
  -- `(1 + x)^N (1 - N x) ≤ (1 + x)^N (1 - x)^N ≤ 1`
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hx1 : x ≤ 1 / 2 := le_trans (le_mul_of_one_le_left hx hN1) hN
  have h1 : 1 - N * x ≤ (1 - x) ^ N := by
    have := one_add_mul_le_pow (a := -x) (by linarith) N
    simpa [sub_eq_add_neg, mul_neg] using this
  have h2 : (1 + x) ^ N * (1 - x) ^ N ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hpos : 0 ≤ (1 + x) ^ N := by positivity
  have h3 : (1 + x) ^ N * (1 - N * x) ≤ 1 :=
    (mul_le_mul_of_nonneg_left h1 hpos).trans h2
  have h4 : (1 + x) ^ N ≤ 2 := by nlinarith
  have hNx : 0 ≤ (N : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  nlinarith [mul_le_mul_of_nonneg_right h4 hNx]

/-- The fixed-mask factor in closed form. -/
theorem fixedMaskFactor_eq (S₁ : ℝ) (k G ℓ : ℕ) :
    fixedMaskFactor S₁ k G ℓ = S₁ ^ k * ((G : ℝ) / (G : ℝ) ^ ℓ) +
      S₁ ^ k * ((G : ℝ) ^ 2 / (G : ℝ) ^ ℓ) +
      (S₁ ^ k) ^ 2 * (((G : ℝ) / (G : ℝ) ^ ℓ) * ((G : ℝ) / (G : ℝ) ^ ℓ)) := by
  simp [fixedMaskFactor, Fin.sum_univ_three, slotEventWeight, firstFactor, secondFactor]

theorem fixedMaskFactor_nonneg {S₁ : ℝ} (hS : 0 ≤ S₁) (k G ℓ : ℕ) :
    0 ≤ fixedMaskFactor S₁ k G ℓ := by
  rw [fixedMaskFactor_eq]
  positivity

theorem fixedMaskFactor_mono {S₁ S₁' : ℝ} (hS : 0 ≤ S₁) (h : S₁ ≤ S₁') (k G ℓ : ℕ) :
    fixedMaskFactor S₁ k G ℓ ≤ fixedMaskFactor S₁' k G ℓ := by
  rw [fixedMaskFactor_eq, fixedMaskFactor_eq]
  gcongr

/-- The three-block closure of `∑_t C(256, t) supportTerm t` for small supports up to `4`. -/
theorem sum_supportTerm_le {k ℓ G : ℕ} {δ : ℕ → ℝ} {S₁ T₂ : ℝ} (hS : 0 ≤ S₁) (hT₂ : 0 ≤ T₂)
    (ha : 256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k < 1) (hX : fixedMaskFactor S₁ k G ℓ ≤ 1) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else supportTerm 256 k ℓ G 4 δ S₁ T₂ t) ≤
      ∑ t ∈ range 5, ((256 : ℕ).choose t : ℝ) *
          (if t = 0 then 0 else ((G : ℝ) / (G : ℝ) ^ ℓ) ^ t * ((1 + δ t) ^ (2 * k) - 1)) +
        (256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k) ^ 5 /
          (120 * (1 - 256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k)) +
        2 ^ 256 * fixedMaskFactor S₁ k G ℓ ^ 129 := by
  set g : ℝ := (G : ℝ) / (G : ℝ) ^ ℓ
  set a : ℝ := 256 * g * T₂ ^ k
  set X := fixedMaskFactor S₁ k G ℓ
  have hg : 0 ≤ g := by positivity
  have ha0 : 0 ≤ a := by positivity
  have hX0 : 0 ≤ X := fixedMaskFactor_nonneg hS k G ℓ
  rw [← Finset.sum_range_add_sum_Ico _ (show 5 ≤ 257 by norm_num),
    ← Finset.sum_Ico_consecutive _ (show 5 ≤ 129 by norm_num) (show 129 ≤ 257 by norm_num)]
  have h1 : ∑ t ∈ range 5, ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else supportTerm 256 k ℓ G 4 δ S₁ T₂ t) =
      ∑ t ∈ range 5, ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else g ^ t * ((1 + δ t) ^ (2 * k) - 1)) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have : t ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    simp only [supportTerm, if_pos this, g]
  have h2 : ∑ t ∈ Ico 5 129, ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else supportTerm 256 k ℓ G 4 δ S₁ T₂ t) ≤ a ^ 5 / (120 * (1 - a)) := by
    calc _ ≤ ∑ t ∈ Ico 5 129, a ^ t / 120 := by
          refine Finset.sum_le_sum fun t ht => ?_
          obtain ⟨ht5, ht129⟩ := Finset.mem_Ico.mp ht
          have hne : t ≠ 0 := by omega
          have hnot : ¬ t ≤ 4 := by omega
          have hmed : t + t ≤ 256 := by omega
          simp only [if_neg hne, supportTerm, if_neg hnot, if_pos hmed]
          have hch : ((256 : ℕ).choose t : ℝ) ≤ (256 : ℝ) ^ t / t.factorial := by
            have := Nat.choose_le_pow_div (α := ℝ) t 256
            simpa using this
          have hfac : (120 : ℝ) ≤ t.factorial := by
            have : (5 : ℕ).factorial ≤ t.factorial := Nat.factorial_le ht5
            exact_mod_cast (show (120 : ℕ) ≤ t.factorial by simpa [Nat.factorial] using this)
          have hY : 0 ≤ g ^ t * (T₂ ^ t) ^ k := by positivity
          calc ((256 : ℕ).choose t : ℝ) * (g ^ t * (T₂ ^ t) ^ k)
              ≤ (256 : ℝ) ^ t / t.factorial * (g ^ t * (T₂ ^ t) ^ k) :=
                mul_le_mul_of_nonneg_right hch hY
            _ ≤ (256 : ℝ) ^ t / 120 * (g ^ t * (T₂ ^ t) ^ k) := by
                gcongr
            _ = a ^ t / 120 := by
                simp only [a]
                rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm t k]
                ring
      _ = (∑ t ∈ Ico 5 129, a ^ t) / 120 := by rw [Finset.sum_div]
      _ ≤ a ^ 5 / (1 - a) / 120 := by
          gcongr
          exact geom_sum_Ico_le_of_lt_one ha0 ha
      _ = a ^ 5 / (120 * (1 - a)) := by rw [div_div, mul_comm]
  have h3 : ∑ t ∈ Ico 129 257, ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else supportTerm 256 k ℓ G 4 δ S₁ T₂ t) ≤ 2 ^ 256 * X ^ 129 := by
    calc _ ≤ ∑ t ∈ range 257, ((256 : ℕ).choose t : ℝ) * X ^ 129 := by
          refine (Finset.sum_le_sum fun t ht => ?_).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => Finset.mem_range.mpr
              (Finset.mem_Ico.mp ht).2) fun t _ _ => by positivity)
          obtain ⟨ht1, ht2⟩ := Finset.mem_Ico.mp ht
          have hne : t ≠ 0 := by omega
          have hnot : ¬ t ≤ 4 := by omega
          have hbig : ¬ t + t ≤ 256 := by omega
          simp only [if_neg hne, supportTerm, if_neg hnot, if_neg hbig]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hX0 hX ht1) (by positivity)
      _ = 2 ^ 256 * X ^ 129 := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose 256
  rw [h1]
  linarith

theorem choose_256_one : (256 : ℕ).choose 1 = 256 := by simp

theorem choose_256_two : (256 : ℕ).choose 2 = 32640 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; norm_num [Nat.descFactorial, Nat.factorial]

theorem choose_256_three : (256 : ℕ).choose 3 = 2763520 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; norm_num [Nat.descFactorial, Nat.factorial]

theorem choose_256_four : (256 : ℕ).choose 4 = 174792640 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; norm_num [Nat.descFactorial, Nat.factorial]

/-- The four small-support terms in explicit form. -/
theorem sum_range_five_smallTerms (g : ℝ) (k : ℕ) (δ : ℕ → ℝ) :
    ∑ t ∈ range 5, ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else g ^ t * ((1 + δ t) ^ (2 * k) - 1)) =
      256 * (g ^ 1 * ((1 + δ 1) ^ (2 * k) - 1)) + 32640 * (g ^ 2 * ((1 + δ 2) ^ (2 * k) - 1)) +
        2763520 * (g ^ 3 * ((1 + δ 3) ^ (2 * k) - 1)) +
        174792640 * (g ^ 4 * ((1 + δ 4) ^ (2 * k) - 1)) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, if_pos rfl, if_neg one_ne_zero, if_neg two_ne_zero,
    if_neg three_ne_zero, if_neg four_ne_zero, choose_256_one, choose_256_two, choose_256_three,
    choose_256_four]
  push_cast
  ring

/-- `(1 + δ)^N - 1 ≤ 2Nδ̄` for `0 ≤ δ ≤ δ̄`, `N δ̄ ≤ 1/2`. -/
theorem one_add_pow_sub_one_le_of_le {d d' : ℝ} (hd : 0 ≤ d) (hd' : d ≤ d') {N : ℕ}
    (hN : N * d' ≤ 1 / 2) : (1 + d) ^ N - 1 ≤ 2 * N * d' :=
  (one_add_pow_sub_one_le hd (le_trans (by gcongr) hN)).trans (by gcongr)

/-- The ML-DSA-65 envelope: `∑_t C(256, t) supportTerm t ≤ 2^-246`. -/
theorem envelope_mldsa65 {δ : ℕ → ℝ} (hδ0 : ∀ t, 0 ≤ δ t) (hδ1 : δ 1 ≤ 1 / (2 ^ 256) ^ 2)
    (hδ2 : δ 2 ≤ 1 / 2 ^ 210) (hδ3 : δ 3 ≤ 1 / 2 ^ 155) (hδ4 : δ 4 ≤ 1 / 2 ^ 52) {S₁ : ℝ}
    (hS0 : 0 ≤ S₁) (hS : S₁ ≤ 610) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else supportTerm 256 6 5 1048183 4 δ S₁
          (8380417 ^ 2 / (16 * 523383 ^ 2)) t) ≤ 1 / 2 ^ 246 := by
  have hX : fixedMaskFactor S₁ 6 1048183 5 ≤ 1 / 16 :=
    (fixedMaskFactor_mono hS0 hS _ _ _).trans (by rw [fixedMaskFactor_eq]; norm_num)
  refine (sum_supportTerm_le hS0 (by positivity) (by norm_num) (hX.trans (by norm_num))).trans ?_
  have hX129 : fixedMaskFactor S₁ 6 1048183 5 ^ 129 ≤ (1 / 16) ^ 129 :=
    pow_le_pow_left₀ (fixedMaskFactor_nonneg hS0 _ _ _) hX _
  rw [sum_range_five_smallTerms]
  have e1 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 1) hδ1
    (by norm_num)
  have e2 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 2) hδ2 (by norm_num)
  have e3 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 3) hδ3 (by norm_num)
  have e4 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 4) hδ4 (by norm_num)
  set g : ℝ := ((1048183 : ℕ) : ℝ) / (1048183 : ℝ) ^ 5
  have hg : 0 ≤ g := by positivity
  have hnum : 256 * (g ^ 1 * (2 * (2 * 6 : ℕ) * (1 / (2 ^ 256) ^ 2))) +
      32640 * (g ^ 2 * (2 * (2 * 6 : ℕ) * (1 / 2 ^ 210))) +
      2763520 * (g ^ 3 * (2 * (2 * 6 : ℕ) * (1 / 2 ^ 155))) +
      174792640 * (g ^ 4 * (2 * (2 * 6 : ℕ) * (1 / 2 ^ 52))) +
      (256 * g * (8380417 ^ 2 / (16 * 523383 ^ 2)) ^ 6) ^ 5 /
        (120 * (1 - 256 * g * (8380417 ^ 2 / (16 * 523383 ^ 2)) ^ 6)) +
      2 ^ 256 * (1 / 16) ^ 129 ≤ 1 / 2 ^ 246 := by
    simp only [g]
    norm_num
  have hpow : ∀ t, 0 ≤ g ^ t := fun t => pow_nonneg hg t
  nlinarith [mul_le_mul_of_nonneg_left e1 (hpow 1), mul_le_mul_of_nonneg_left e2 (hpow 2),
    mul_le_mul_of_nonneg_left e3 (hpow 3), mul_le_mul_of_nonneg_left e4 (hpow 4),
    mul_le_mul_of_nonneg_left hX129 (by norm_num : (0 : ℝ) ≤ 2 ^ 256)]

/-- The ML-DSA-87 envelope: `∑_t C(256, t) supportTerm t ≤ 2^-406`. -/
theorem envelope_mldsa87 {δ : ℕ → ℝ} (hδ0 : ∀ t, 0 ≤ δ t) (hδ1 : δ 1 ≤ 1 / (2 ^ 256) ^ 2)
    (hδ2 : δ 2 ≤ 1 / 2 ^ 210) (hδ3 : δ 3 ≤ 1 / 2 ^ 155) (hδ4 : δ 4 ≤ 1 / 2 ^ 52) {S₁ : ℝ}
    (hS0 : 0 ≤ S₁) (hS : S₁ ≤ 610) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else supportTerm 256 8 7 1048335 4 δ S₁
          (8380417 ^ 2 / (16 * 523535 ^ 2)) t) ≤ 1 / 2 ^ 406 := by
  have hX : fixedMaskFactor S₁ 8 1048335 7 ≤ 1 / 2 ^ 20 :=
    (fixedMaskFactor_mono hS0 hS _ _ _).trans (by rw [fixedMaskFactor_eq]; norm_num)
  refine (sum_supportTerm_le hS0 (by positivity) (by norm_num) (hX.trans (by norm_num))).trans ?_
  have hX129 : fixedMaskFactor S₁ 8 1048335 7 ^ 129 ≤ (1 / 2 ^ 20) ^ 129 :=
    pow_le_pow_left₀ (fixedMaskFactor_nonneg hS0 _ _ _) hX _
  rw [sum_range_five_smallTerms]
  have e1 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 1) hδ1
    (by norm_num)
  have e2 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 2) hδ2 (by norm_num)
  have e3 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 3) hδ3 (by norm_num)
  have e4 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 4) hδ4 (by norm_num)
  set g : ℝ := ((1048335 : ℕ) : ℝ) / (1048335 : ℝ) ^ 7
  have hg : 0 ≤ g := by positivity
  have hnum : 256 * (g ^ 1 * (2 * (2 * 8 : ℕ) * (1 / (2 ^ 256) ^ 2))) +
      32640 * (g ^ 2 * (2 * (2 * 8 : ℕ) * (1 / 2 ^ 210))) +
      2763520 * (g ^ 3 * (2 * (2 * 8 : ℕ) * (1 / 2 ^ 155))) +
      174792640 * (g ^ 4 * (2 * (2 * 8 : ℕ) * (1 / 2 ^ 52))) +
      (256 * g * (8380417 ^ 2 / (16 * 523535 ^ 2)) ^ 8) ^ 5 /
        (120 * (1 - 256 * g * (8380417 ^ 2 / (16 * 523535 ^ 2)) ^ 8)) +
      2 ^ 256 * (1 / 2 ^ 20) ^ 129 ≤ 1 / 2 ^ 406 := by
    rw [show (2 : ℝ) ^ 406 = (2 ^ 203) ^ 2 by rw [← pow_mul]]
    simp only [g]
    norm_num
  have hpow : ∀ t, 0 ≤ g ^ t := fun t => pow_nonneg hg t
  nlinarith [mul_le_mul_of_nonneg_left e1 (hpow 1), mul_le_mul_of_nonneg_left e2 (hpow 2),
    mul_le_mul_of_nonneg_left e3 (hpow 3), mul_le_mul_of_nonneg_left e4 (hpow 4),
    mul_le_mul_of_nonneg_left hX129 (by norm_num : (0 : ℝ) ≤ 2 ^ 256)]

end GordieHowe.MLDSA.Regularity
