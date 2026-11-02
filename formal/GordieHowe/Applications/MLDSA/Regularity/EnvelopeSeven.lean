-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.SlotBoxCount

@[expose] public section

/-!
# The numerical envelopes with small supports up to seven

The envelopes of `SlotBoxCount.lean` and `EnvelopeFive.lean` with the small-support bounds up to
seven roots of `SmallSupportWindows.lean` (`δ₂ ≤ 2^-394, δ₃ ≤ 2^-255, δ₄ ≤ 2^-153,
δ₅ ≤ 2^-75, δ₆ ≤ 2^-52, δ₇ ≤ 2^-29` at cell size `523383`). The two-window block then starts at
`t = 8` (`∑ ≤ a^8 / (40320 (1 - a))`), and every `t ≥ 129` takes the hybrid term
(`2^256 Y^129`).

- `sum_min_boxSupportTerm_le_seven`: the closure with the fixed-mode bound for `t ≤ 4` and the
  sharp slot count on `5 ≤ t ≤ 7`; `envelope_box_seven_mldsa44`: at ML-DSA-44 the sum is at most
  `2^-202`. Numerically the sharp term at `t = 5` (`2^-202.7`) dominates, then the two-window
  block (`2^-208.5`).
- `sum_min_supportTerm_le_seven`: the closure with the fixed-mode bound for `t ≤ 7`;
  `envelope_seven_mldsa65` and `envelope_seven_mldsa87`: at ML-DSA-65 and ML-DSA-87 the sum is at
  most `2^-398` and `2^-588`. Numerically the two-window block dominates at ML-DSA-65
  (`2^-399.2`) and the fixed-mode term at `t = 3` at ML-DSA-87 (`2^-588.6`). At these two
  parameter sets the fixed-mode bound `G^{-(ℓ-1)t} ((1 + δ_t)^{2k} - 1)` is numerically smaller
  than the sharp slot count `q^{-(ℓ-1)t} (1 + δ'_t)^{2ℓ} T₂^{kt}` for every `t ≤ 7`, so these
  envelopes do not use the sharp count.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

/-- `C(256, 6)`. -/
theorem choose_256_six : (256 : ℕ).choose 6 = 368532802176 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; norm_num [Nat.descFactorial, Nat.factorial]

/-- `C(256, 7)`. -/
theorem choose_256_seven : (256 : ℕ).choose 7 = 13161885792000 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; norm_num [Nat.descFactorial, Nat.factorial]

/-- The two-window block from `t = 8`:
`∑_{8 ≤ t ≤ 128} C(256, t) g^t (T₂^t)^k ≤ a^8 / (8! (1 - a))` for `a = 256 g T₂^k < 1`. -/
theorem sum_Ico_eight_twoWindows_le {k : ℕ} {g T₂ : ℝ} (hg : 0 ≤ g) (hT₂ : 0 ≤ T₂)
    (ha : 256 * g * T₂ ^ k < 1) (F : ℕ → ℝ)
    (hF : ∀ t ∈ Ico 8 129, F t ≤ ((256 : ℕ).choose t : ℝ) * (g ^ t * (T₂ ^ t) ^ k)) :
    ∑ t ∈ Ico 8 129, F t ≤ (256 * g * T₂ ^ k) ^ 8 / (40320 * (1 - 256 * g * T₂ ^ k)) := by
  set a : ℝ := 256 * g * T₂ ^ k
  have ha0 : 0 ≤ a := by positivity
  calc _ ≤ ∑ t ∈ Ico 8 129, a ^ t / 40320 := by
        refine Finset.sum_le_sum fun t ht => (hF t ht).trans ?_
        obtain ⟨ht8, -⟩ := Finset.mem_Ico.mp ht
        have hch : ((256 : ℕ).choose t : ℝ) ≤ (256 : ℝ) ^ t / t.factorial := by
          have := Nat.choose_le_pow_div (α := ℝ) t 256
          simpa using this
        have hfac : (40320 : ℝ) ≤ t.factorial := by
          have : (8 : ℕ).factorial ≤ t.factorial := Nat.factorial_le ht8
          exact_mod_cast (show (40320 : ℕ) ≤ t.factorial by simpa [Nat.factorial] using this)
        have hX : 0 ≤ g ^ t * (T₂ ^ t) ^ k := by positivity
        calc ((256 : ℕ).choose t : ℝ) * (g ^ t * (T₂ ^ t) ^ k)
            ≤ (256 : ℝ) ^ t / t.factorial * (g ^ t * (T₂ ^ t) ^ k) :=
              mul_le_mul_of_nonneg_right hch hX
          _ ≤ (256 : ℝ) ^ t / 40320 * (g ^ t * (T₂ ^ t) ^ k) := by
              gcongr
          _ = a ^ t / 40320 := by
              simp only [a]
              rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm t k]
              ring
    _ = (∑ t ∈ Ico 8 129, a ^ t) / 40320 := by rw [Finset.sum_div]
    _ ≤ a ^ 8 / (1 - a) / 40320 := by
        gcongr
        exact geom_sum_Ico_le_of_lt_one ha0 ha
    _ = a ^ 8 / (40320 * (1 - a)) := by rw [div_div, mul_comm]

/-- The hybrid block: `∑_{t ≥ 129} C(256, t) Y^t ≤ 2^256 Y^129` for `0 ≤ Y ≤ 1`. -/
theorem sum_Ico_hybrid_le {Y : ℝ} (hY0 : 0 ≤ Y) (hY : Y ≤ 1) (F : ℕ → ℝ)
    (hF : ∀ t ∈ Ico 129 257, F t ≤ ((256 : ℕ).choose t : ℝ) * Y ^ t) :
    ∑ t ∈ Ico 129 257, F t ≤ 2 ^ 256 * Y ^ 129 := by
  calc _ ≤ ∑ t ∈ range 257, ((256 : ℕ).choose t : ℝ) * Y ^ 129 := by
        refine (Finset.sum_le_sum fun t ht => ?_).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => Finset.mem_range.mpr
            (Finset.mem_Ico.mp ht).2) fun t _ _ => by positivity)
        obtain ⟨ht1, -⟩ := Finset.mem_Ico.mp ht
        exact (hF t ht).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hY0 hY ht1)
          (Nat.cast_nonneg _))
    _ = 2 ^ 256 * Y ^ 129 := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose 256

/-- The four-block closure of `∑_t C(256, t) · min (boxSupportTerm t) (Y ^ t)` with small supports
up to `4` and the sharp count on `5 ≤ t ≤ 7`: the small block, the sharp terms, the two-window
block `t ∈ [8, 128]` and the hybrid block `t ≥ 129`. -/
theorem sum_min_boxSupportTerm_le_seven {k ℓ G Q : ℕ} {δ δ' : ℕ → ℝ} {S₁ T₂ Y : ℝ}
    (hT₂ : 0 ≤ T₂) (ha : 256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k < 1) (hY0 : 0 ≤ Y)
    (hY : Y ≤ 1) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else min (boxSupportTerm 256 k ℓ G Q 4 7 δ δ' S₁ T₂ t) (Y ^ t)) ≤
      ∑ t ∈ range 5, ((256 : ℕ).choose t : ℝ) *
          (if t = 0 then 0 else ((G : ℝ) / (G : ℝ) ^ ℓ) ^ t * ((1 + δ t) ^ (2 * k) - 1)) +
        ∑ t ∈ Ico 5 8, ((256 : ℕ).choose t : ℝ) *
          (((Q : ℝ) / (Q : ℝ) ^ ℓ) ^ t * (1 + δ' t) ^ (2 * ℓ) * (T₂ ^ t) ^ k) +
        (256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k) ^ 8 /
          (40320 * (1 - 256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k)) +
        2 ^ 256 * Y ^ 129 := by
  set g : ℝ := (G : ℝ) / (G : ℝ) ^ ℓ
  have hg : 0 ≤ g := by positivity
  rw [← Finset.sum_range_add_sum_Ico _ (show 8 ≤ 257 by norm_num),
    ← Finset.sum_Ico_consecutive _ (show 8 ≤ 129 by norm_num) (show 129 ≤ 257 by norm_num),
    ← Finset.sum_range_add_sum_Ico _ (show 5 ≤ 8 by norm_num)]
  have h1 : ∑ t ∈ range 5, ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else min (boxSupportTerm 256 k ℓ G Q 4 7 δ δ' S₁ T₂ t) (Y ^ t)) ≤
      ∑ t ∈ range 5, ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else g ^ t * ((1 + δ t) ^ (2 * k) - 1)) := by
    refine Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have : t ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    split_ifs with h0
    · exact le_rfl
    · refine (min_le_left _ _).trans (le_of_eq ?_)
      simp only [boxSupportTerm, supportTerm, if_neg (show ¬ (4 < t ∧ t ≤ 7 ∧ t + t ≤ 256) by
        omega), if_pos this, g]
  have h5 : ∑ t ∈ Ico 5 8, ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else min (boxSupportTerm 256 k ℓ G Q 4 7 δ δ' S₁ T₂ t) (Y ^ t)) ≤
      ∑ t ∈ Ico 5 8, ((256 : ℕ).choose t : ℝ) *
        (((Q : ℝ) / (Q : ℝ) ^ ℓ) ^ t * (1 + δ' t) ^ (2 * ℓ) * (T₂ ^ t) ^ k) := by
    refine Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    obtain ⟨ht5, ht8⟩ := Finset.mem_Ico.mp ht
    rw [if_neg (by omega)]
    refine (min_le_left _ _).trans (le_of_eq ?_)
    simp only [boxSupportTerm, if_pos (show 4 < t ∧ t ≤ 7 ∧ t + t ≤ 256 by omega)]
  have h2 := sum_Ico_eight_twoWindows_le hg hT₂ ha (fun t => ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else min (boxSupportTerm 256 k ℓ G Q 4 7 δ δ' S₁ T₂ t) (Y ^ t)))
    fun t ht => by
      obtain ⟨ht8, ht129⟩ := Finset.mem_Ico.mp ht
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [if_neg (by omega)]
      refine (min_le_left _ _).trans (le_of_eq ?_)
      simp only [boxSupportTerm, supportTerm,
        if_neg (show ¬ (4 < t ∧ t ≤ 7 ∧ t + t ≤ 256) by omega),
        if_neg (show ¬ t ≤ 4 by omega), if_pos (show t + t ≤ 256 by omega), g]
  have h3 := sum_Ico_hybrid_le hY0 hY (fun t => ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else min (boxSupportTerm 256 k ℓ G Q 4 7 δ δ' S₁ T₂ t) (Y ^ t)))
    fun t ht => by
      obtain ⟨ht1, -⟩ := Finset.mem_Ico.mp ht
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [if_neg (by omega)]
      exact min_le_right _ _
  linarith

/-- The three-block closure of `∑_t C(256, t) · min (supportTerm t) (Y ^ t)` with small supports
up to `7`: the small block, the two-window block `t ∈ [8, 128]` and the hybrid block
`t ≥ 129`. -/
theorem sum_min_supportTerm_le_seven {k ℓ G : ℕ} {δ : ℕ → ℝ} {S₁ T₂ Y : ℝ}
    (hT₂ : 0 ≤ T₂) (ha : 256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k < 1) (hY0 : 0 ≤ Y)
    (hY : Y ≤ 1) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else min (supportTerm 256 k ℓ G 7 δ S₁ T₂ t) (Y ^ t)) ≤
      ∑ t ∈ range 8, ((256 : ℕ).choose t : ℝ) *
          (if t = 0 then 0 else ((G : ℝ) / (G : ℝ) ^ ℓ) ^ t * ((1 + δ t) ^ (2 * k) - 1)) +
        (256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k) ^ 8 /
          (40320 * (1 - 256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k)) +
        2 ^ 256 * Y ^ 129 := by
  set g : ℝ := (G : ℝ) / (G : ℝ) ^ ℓ
  have hg : 0 ≤ g := by positivity
  rw [← Finset.sum_range_add_sum_Ico _ (show 8 ≤ 257 by norm_num),
    ← Finset.sum_Ico_consecutive _ (show 8 ≤ 129 by norm_num) (show 129 ≤ 257 by norm_num)]
  have h1 : ∑ t ∈ range 8, ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else min (supportTerm 256 k ℓ G 7 δ S₁ T₂ t) (Y ^ t)) ≤
      ∑ t ∈ range 8, ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else g ^ t * ((1 + δ t) ^ (2 * k) - 1)) := by
    refine Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have : t ≤ 7 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    split_ifs with h0
    · exact le_rfl
    · refine (min_le_left _ _).trans (le_of_eq ?_)
      simp only [supportTerm, if_pos this, g]
  have h2 := sum_Ico_eight_twoWindows_le hg hT₂ ha (fun t => ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else min (supportTerm 256 k ℓ G 7 δ S₁ T₂ t) (Y ^ t)))
    fun t ht => by
      obtain ⟨ht8, ht129⟩ := Finset.mem_Ico.mp ht
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [if_neg (by omega)]
      refine (min_le_left _ _).trans (le_of_eq ?_)
      simp only [supportTerm, if_neg (show ¬ t ≤ 7 by omega), if_pos (show t + t ≤ 256 by omega),
        g]
  have h3 := sum_Ico_hybrid_le hY0 hY (fun t => ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else min (supportTerm 256 k ℓ G 7 δ S₁ T₂ t) (Y ^ t)))
    fun t ht => by
      obtain ⟨ht1, -⟩ := Finset.mem_Ico.mp ht
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [if_neg (by omega)]
      exact min_le_right _ _
  linarith

/-- The seven small-support terms in explicit form. -/
theorem sum_range_eight_smallTerms (g : ℝ) (k : ℕ) (δ : ℕ → ℝ) :
    ∑ t ∈ range 8, ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else g ^ t * ((1 + δ t) ^ (2 * k) - 1)) =
      256 * (g ^ 1 * ((1 + δ 1) ^ (2 * k) - 1)) + 32640 * (g ^ 2 * ((1 + δ 2) ^ (2 * k) - 1)) +
        2763520 * (g ^ 3 * ((1 + δ 3) ^ (2 * k) - 1)) +
        174792640 * (g ^ 4 * ((1 + δ 4) ^ (2 * k) - 1)) +
        8809549056 * (g ^ 5 * ((1 + δ 5) ^ (2 * k) - 1)) +
        368532802176 * (g ^ 6 * ((1 + δ 6) ^ (2 * k) - 1)) +
        13161885792000 * (g ^ 7 * ((1 + δ 7) ^ (2 * k) - 1)) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    sum_range_five_smallTerms, if_neg (by norm_num : (5 : ℕ) ≠ 0),
    if_neg (by norm_num : (6 : ℕ) ≠ 0), if_neg (by norm_num : (7 : ℕ) ≠ 0), choose_256_five,
    choose_256_six, choose_256_seven]
  push_cast
  ring

/-- The three sharp terms in explicit form. -/
theorem sum_Ico_five_eight_sharpTerms (gq T₂ : ℝ) (k ℓ : ℕ) (δ' : ℕ → ℝ) :
    ∑ t ∈ Ico 5 8, ((256 : ℕ).choose t : ℝ) * (gq ^ t * (1 + δ' t) ^ (2 * ℓ) * (T₂ ^ t) ^ k) =
      8809549056 * (gq ^ 5 * (1 + δ' 5) ^ (2 * ℓ) * (T₂ ^ 5) ^ k) +
        368532802176 * (gq ^ 6 * (1 + δ' 6) ^ (2 * ℓ) * (T₂ ^ 6) ^ k) +
        13161885792000 * (gq ^ 7 * (1 + δ' 7) ^ (2 * ℓ) * (T₂ ^ 7) ^ k) := by
  rw [Finset.sum_Ico_succ_top (by norm_num), Finset.sum_Ico_succ_top (by norm_num),
    Finset.sum_Ico_succ_top (by norm_num), Finset.Ico_self, Finset.sum_empty, choose_256_five,
    choose_256_six, choose_256_seven]
  push_cast
  ring

/-- **The ML-DSA-44 envelope with the sharp slot count up to seven roots.** With `k = ℓ = 4`,
`L = 190307`, `G = 261987`, `q = 8380417`, `T₂ = q² / (44 L²)`, the kernel bounds
`δ₁ ≤ 2^-512, δ₂ ≤ 2^-210, δ₃ ≤ 2^-155, δ₄ ≤ 2^-52`, the box bounds `δ'₅ ≤ 2^-75, δ'₆ ≤ 2^-52,
δ'₇ ≤ 2^-29`, `S₁ ≤ 1620` and `S₂ ≤ q / L`:
`∑_t C(256, t) · min (boxSupportTerm t) (hybridFactor ^ t) ≤ 2^-202`. The sharp term at
`t = 5` dominates (`2^-202.7`), then the two-window block from `t = 8` (`2^-208.5`). -/
theorem envelope_box_seven_mldsa44 {δ δ' : ℕ → ℝ} (hδ0 : ∀ t, 0 ≤ δ t)
    (hδ1 : δ 1 ≤ 1 / 2 ^ 512) (hδ2 : δ 2 ≤ 1 / 2 ^ 210) (hδ3 : δ 3 ≤ 1 / 2 ^ 155)
    (hδ4 : δ 4 ≤ 1 / 2 ^ 52) (hδ'0 : ∀ t, 0 ≤ δ' t) (hδ'5 : δ' 5 ≤ 1 / 2 ^ 75)
    (hδ'6 : δ' 6 ≤ 1 / 2 ^ 52) (hδ'7 : δ' 7 ≤ 1 / 2 ^ 29) {S₁ S₂ : ℝ}
    (hS₁0 : 0 ≤ S₁) (hS₁ : S₁ ≤ 1620) (hS₂0 : 0 ≤ S₂) (hS₂ : S₂ ≤ 8380417 / 190307) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else min (boxSupportTerm 256 4 4 261987 8380417 4 7 δ δ' S₁
          (8380417 ^ 2 / (44 * 190307 ^ 2)) t) (hybridFactor S₁ S₂ 4 261987 4 ^ t)) ≤
      1 / 2 ^ 202 := by
  have hY := hybridFactor_mldsa44_le hS₁0 hS₁ hS₂0 hS₂
  have hY0 : 0 ≤ hybridFactor S₁ S₂ 4 261987 4 := by
    rw [hybridFactor_eq _ _ _ (show 1 ≤ 261987 by norm_num)]
    positivity
  set Y := hybridFactor S₁ S₂ 4 261987 4
  refine (sum_min_boxSupportTerm_le_seven (by positivity) (by norm_num) hY0
    (hY.trans (by norm_num))).trans ?_
  have h4 : 4 * Y ≤ 1 / 256 := by linarith
  have h40 : 0 ≤ 4 * Y := by positivity
  have hlarge : 2 ^ 256 * Y ^ 129 ≤ (1 / 256) ^ 32 := by
    calc 2 ^ 256 * Y ^ 129 ≤ 2 ^ 256 * Y ^ 128 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hY0 (hY.trans (by norm_num))
            (by norm_num)) (by positivity)
      _ = (4 * Y) ^ 128 := by rw [mul_pow]; norm_num
      _ ≤ (4 * Y) ^ 32 := pow_le_pow_of_le_one h40 (h4.trans (by norm_num)) (by norm_num)
      _ ≤ (1 / 256) ^ 32 := pow_le_pow_left₀ h40 h4 _
  rw [sum_range_five_smallTerms, sum_Ico_five_eight_sharpTerms]
  have e1 := one_add_pow_sub_one_le_of_le (N := 2 * 4) (hδ0 1) hδ1
    (by rw [show (2 : ℝ) ^ 512 = (2 ^ 256) ^ 2 by rw [← pow_mul]]; norm_num)
  have e2 := one_add_pow_sub_one_le_of_le (N := 2 * 4) (hδ0 2) hδ2 (by norm_num)
  have e3 := one_add_pow_sub_one_le_of_le (N := 2 * 4) (hδ0 3) hδ3 (by norm_num)
  have e4 := one_add_pow_sub_one_le_of_le (N := 2 * 4) (hδ0 4) hδ4 (by norm_num)
  set g : ℝ := ((261987 : ℕ) : ℝ) / (261987 : ℝ) ^ 4
  set gq : ℝ := ((8380417 : ℕ) : ℝ) / (8380417 : ℝ) ^ 4
  have hg : 0 ≤ g := by positivity
  have hgq : 0 ≤ gq := by positivity
  set T₂ : ℝ := 8380417 ^ 2 / (44 * 190307 ^ 2)
  have hT₂ : 0 ≤ T₂ := by positivity
  have hsharp : 8809549056 * (gq ^ 5 * (1 + δ' 5) ^ (2 * 4) * (T₂ ^ 5) ^ 4) +
      368532802176 * (gq ^ 6 * (1 + δ' 6) ^ (2 * 4) * (T₂ ^ 6) ^ 4) +
      13161885792000 * (gq ^ 7 * (1 + δ' 7) ^ (2 * 4) * (T₂ ^ 7) ^ 4) ≤
      8809549056 * (gq ^ 5 * (1 + 1 / 2 ^ 75) ^ (2 * 4) * (T₂ ^ 5) ^ 4) +
      368532802176 * (gq ^ 6 * (1 + 1 / 2 ^ 52) ^ (2 * 4) * (T₂ ^ 6) ^ 4) +
      13161885792000 * (gq ^ 7 * (1 + 1 / 2 ^ 29) ^ (2 * 4) * (T₂ ^ 7) ^ 4) := by
    have := hδ'0 5
    have := hδ'0 6
    have := hδ'0 7
    gcongr
  have hnum : 256 * (g ^ 1 * (2 * (2 * 4 : ℕ) * (1 / 2 ^ 512))) +
      32640 * (g ^ 2 * (2 * (2 * 4 : ℕ) * (1 / 2 ^ 210))) +
      2763520 * (g ^ 3 * (2 * (2 * 4 : ℕ) * (1 / 2 ^ 155))) +
      174792640 * (g ^ 4 * (2 * (2 * 4 : ℕ) * (1 / 2 ^ 52))) +
      (8809549056 * (gq ^ 5 * (1 + 1 / 2 ^ 75) ^ (2 * 4) * (T₂ ^ 5) ^ 4) +
        368532802176 * (gq ^ 6 * (1 + 1 / 2 ^ 52) ^ (2 * 4) * (T₂ ^ 6) ^ 4) +
        13161885792000 * (gq ^ 7 * (1 + 1 / 2 ^ 29) ^ (2 * 4) * (T₂ ^ 7) ^ 4)) +
      (256 * g * T₂ ^ 4) ^ 8 / (40320 * (1 - 256 * g * T₂ ^ 4)) +
      (1 / 256) ^ 32 ≤ 1 / 2 ^ 202 := by
    rw [show (2 : ℝ) ^ 512 = (2 ^ 256) ^ 2 by rw [← pow_mul]]
    simp only [g, gq, T₂]
    norm_num
  have hpow : ∀ t, 0 ≤ g ^ t := fun t => pow_nonneg hg t
  nlinarith [mul_le_mul_of_nonneg_left e1 (hpow 1), mul_le_mul_of_nonneg_left e2 (hpow 2),
    mul_le_mul_of_nonneg_left e3 (hpow 3), mul_le_mul_of_nonneg_left e4 (hpow 4)]

/-- The hybrid factor at ML-DSA-65 (`k = 6`, `ℓ = 5`, `G = 1048183`) for `S₁ ≤ 610` and
`S₂ ≤ q / 523383`: `Y ≤ 2^-20`. -/
theorem hybridFactor_mldsa65_le {S₁ S₂ : ℝ} (hS₁0 : 0 ≤ S₁) (hS₁ : S₁ ≤ 610) (hS₂0 : 0 ≤ S₂)
    (hS₂ : S₂ ≤ 8380417 / 523383) : hybridFactor S₁ S₂ 6 1048183 5 ≤ 1 / 2 ^ 20 := by
  rw [hybridFactor_eq _ _ _ (by norm_num)]
  calc _ ≤ 2 * 610 ^ 6 * (((1048183 : ℕ) : ℝ) / ((1048183 : ℕ) : ℝ) ^ 5) +
        (8380417 / 523383) ^ 6 * (((1048183 : ℕ) : ℝ) ^ 2 / ((1048183 : ℕ) : ℝ) ^ 5) +
        ((610 : ℝ) ^ 6) ^ 2 * ((((1048183 : ℕ) : ℝ) / ((1048183 : ℕ) : ℝ) ^ 5) *
          (((1048183 : ℕ) : ℝ) / ((1048183 : ℕ) : ℝ) ^ 5)) := by
        gcongr
    _ ≤ 1 / 2 ^ 20 := by norm_num

/-- The hybrid factor at ML-DSA-87 (`k = 8`, `ℓ = 7`, `G = 1048335`) for `S₁ ≤ 610` and
`S₂ ≤ q / 523535`: `Y ≤ 2^-40`. -/
theorem hybridFactor_mldsa87_le {S₁ S₂ : ℝ} (hS₁0 : 0 ≤ S₁) (hS₁ : S₁ ≤ 610) (hS₂0 : 0 ≤ S₂)
    (hS₂ : S₂ ≤ 8380417 / 523535) : hybridFactor S₁ S₂ 8 1048335 7 ≤ 1 / 2 ^ 40 := by
  rw [hybridFactor_eq _ _ _ (by norm_num)]
  calc _ ≤ 2 * 610 ^ 8 * (((1048335 : ℕ) : ℝ) / ((1048335 : ℕ) : ℝ) ^ 7) +
        (8380417 / 523535) ^ 8 * (((1048335 : ℕ) : ℝ) ^ 2 / ((1048335 : ℕ) : ℝ) ^ 7) +
        ((610 : ℝ) ^ 8) ^ 2 * ((((1048335 : ℕ) : ℝ) / ((1048335 : ℕ) : ℝ) ^ 7) *
          (((1048335 : ℕ) : ℝ) / ((1048335 : ℕ) : ℝ) ^ 7)) := by
        gcongr
    _ ≤ 1 / 2 ^ 40 := by norm_num

/-- The hybrid block at `Y ≤ 2^-20`: `2^256 Y^129 ≤ 2^256 (2^-20)^129 = 2^-2324`. -/
theorem two_pow_mul_pow_129_le {Y : ℝ} (hY0 : 0 ≤ Y) (hY : Y ≤ 1 / 2 ^ 20) :
    2 ^ 256 * Y ^ 129 ≤ 2 ^ 256 * (1 / 2 ^ 20) ^ 129 :=
  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hY0 hY _) (by positivity)

/-- **The ML-DSA-65 envelope with small supports up to seven.** With `k = 6`, `ℓ = 5`,
`L = 523383`, `G = 1048183`, `T₂ = q² / (16 L²)`, the small-support bounds
`δ₁ ≤ 2^-512, δ₂ ≤ 2^-394, δ₃ ≤ 2^-255, δ₄ ≤ 2^-153, δ₅ ≤ 2^-75, δ₆ ≤ 2^-52, δ₇ ≤ 2^-29`,
`S₁ ≤ 610` and `S₂ ≤ q / L`:
`∑_t C(256, t) · min (supportTerm t) (hybridFactor ^ t) ≤ 2^-398`. The two-window block from
`t = 8` dominates (`2^-399.2`). -/
theorem envelope_seven_mldsa65 {δ : ℕ → ℝ} (hδ0 : ∀ t, 0 ≤ δ t)
    (hδ1 : δ 1 ≤ 1 / (2 ^ 256) ^ 2) (hδ2 : δ 2 ≤ 1 / (2 ^ 197) ^ 2) (hδ3 : δ 3 ≤ 1 / 2 ^ 255)
    (hδ4 : δ 4 ≤ 1 / 2 ^ 153) (hδ5 : δ 5 ≤ 1 / 2 ^ 75) (hδ6 : δ 6 ≤ 1 / 2 ^ 52)
    (hδ7 : δ 7 ≤ 1 / 2 ^ 29) {S₁ S₂ : ℝ} (hS₁0 : 0 ≤ S₁) (hS₁ : S₁ ≤ 610) (hS₂0 : 0 ≤ S₂)
    (hS₂ : S₂ ≤ 8380417 / 523383) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else min (supportTerm 256 6 5 1048183 7 δ S₁
          (8380417 ^ 2 / (16 * 523383 ^ 2)) t) (hybridFactor S₁ S₂ 6 1048183 5 ^ t)) ≤
      1 / 2 ^ 398 := by
  have hY := hybridFactor_mldsa65_le hS₁0 hS₁ hS₂0 hS₂
  have hY0 : 0 ≤ hybridFactor S₁ S₂ 6 1048183 5 := by
    rw [hybridFactor_eq _ _ _ (show 1 ≤ 1048183 by norm_num)]
    positivity
  refine (sum_min_supportTerm_le_seven (by positivity) (by norm_num) hY0
    (hY.trans (by norm_num))).trans ?_
  have hlarge := two_pow_mul_pow_129_le hY0 hY
  rw [sum_range_eight_smallTerms]
  have e1 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 1) hδ1 (by norm_num)
  have e2 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 2) hδ2 (by norm_num)
  have e3 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 3) hδ3 (by norm_num)
  have e4 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 4) hδ4 (by norm_num)
  have e5 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 5) hδ5 (by norm_num)
  have e6 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 6) hδ6 (by norm_num)
  have e7 := one_add_pow_sub_one_le_of_le (N := 2 * 6) (hδ0 7) hδ7 (by norm_num)
  set g : ℝ := ((1048183 : ℕ) : ℝ) / (1048183 : ℝ) ^ 5
  have hg : 0 ≤ g := by positivity
  have hnum : 256 * (g ^ 1 * (2 * (2 * 6 : ℕ) * (1 / (2 ^ 256) ^ 2))) +
      32640 * (g ^ 2 * (2 * (2 * 6 : ℕ) * (1 / (2 ^ 197) ^ 2))) +
      2763520 * (g ^ 3 * (2 * (2 * 6 : ℕ) * (1 / 2 ^ 255))) +
      174792640 * (g ^ 4 * (2 * (2 * 6 : ℕ) * (1 / 2 ^ 153))) +
      8809549056 * (g ^ 5 * (2 * (2 * 6 : ℕ) * (1 / 2 ^ 75))) +
      368532802176 * (g ^ 6 * (2 * (2 * 6 : ℕ) * (1 / 2 ^ 52))) +
      13161885792000 * (g ^ 7 * (2 * (2 * 6 : ℕ) * (1 / 2 ^ 29))) +
      (256 * g * (8380417 ^ 2 / (16 * 523383 ^ 2)) ^ 6) ^ 8 /
        (40320 * (1 - 256 * g * (8380417 ^ 2 / (16 * 523383 ^ 2)) ^ 6)) +
      2 ^ 256 * (1 / 2 ^ 20) ^ 129 ≤ 1 / 2 ^ 398 := by
    rw [show (2 : ℝ) ^ 398 = (2 ^ 199) ^ 2 by rw [← pow_mul]]
    simp only [g]
    norm_num
  have hpow : ∀ t, 0 ≤ g ^ t := fun t => pow_nonneg hg t
  nlinarith [mul_le_mul_of_nonneg_left e1 (hpow 1), mul_le_mul_of_nonneg_left e2 (hpow 2),
    mul_le_mul_of_nonneg_left e3 (hpow 3), mul_le_mul_of_nonneg_left e4 (hpow 4),
    mul_le_mul_of_nonneg_left e5 (hpow 5), mul_le_mul_of_nonneg_left e6 (hpow 6),
    mul_le_mul_of_nonneg_left e7 (hpow 7)]

/-- **The ML-DSA-87 envelope with small supports up to seven.** With `k = 8`, `ℓ = 7`,
`L = 523535`, `G = 1048335`, `T₂ = q² / (16 L²)`, the small-support bounds of
`envelope_seven_mldsa65`, `S₁ ≤ 610` and `S₂ ≤ q / L`:
`∑_t C(256, t) · min (supportTerm t) (hybridFactor ^ t) ≤ 2^-588`. The small-support term at
`t = 3` dominates (`2^-588.6`), then `t = 4` (`2^-600.6`). -/
theorem envelope_seven_mldsa87 {δ : ℕ → ℝ} (hδ0 : ∀ t, 0 ≤ δ t)
    (hδ1 : δ 1 ≤ 1 / (2 ^ 256) ^ 2) (hδ2 : δ 2 ≤ 1 / (2 ^ 197) ^ 2) (hδ3 : δ 3 ≤ 1 / 2 ^ 255)
    (hδ4 : δ 4 ≤ 1 / 2 ^ 153) (hδ5 : δ 5 ≤ 1 / 2 ^ 75) (hδ6 : δ 6 ≤ 1 / 2 ^ 52)
    (hδ7 : δ 7 ≤ 1 / 2 ^ 29) {S₁ S₂ : ℝ} (hS₁0 : 0 ≤ S₁) (hS₁ : S₁ ≤ 610) (hS₂0 : 0 ≤ S₂)
    (hS₂ : S₂ ≤ 8380417 / 523535) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else min (supportTerm 256 8 7 1048335 7 δ S₁
          (8380417 ^ 2 / (16 * 523535 ^ 2)) t) (hybridFactor S₁ S₂ 8 1048335 7 ^ t)) ≤
      1 / 2 ^ 588 := by
  have hY := hybridFactor_mldsa87_le hS₁0 hS₁ hS₂0 hS₂
  have hY0 : 0 ≤ hybridFactor S₁ S₂ 8 1048335 7 := by
    rw [hybridFactor_eq _ _ _ (show 1 ≤ 1048335 by norm_num)]
    positivity
  refine (sum_min_supportTerm_le_seven (by positivity) (by norm_num) hY0
    (hY.trans (by norm_num))).trans ?_
  have hlarge := two_pow_mul_pow_129_le hY0 (hY.trans (by norm_num))
  rw [sum_range_eight_smallTerms]
  have e1 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 1) hδ1 (by norm_num)
  have e2 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 2) hδ2 (by norm_num)
  have e3 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 3) hδ3 (by norm_num)
  have e4 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 4) hδ4 (by norm_num)
  have e5 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 5) hδ5 (by norm_num)
  have e6 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 6) hδ6 (by norm_num)
  have e7 := one_add_pow_sub_one_le_of_le (N := 2 * 8) (hδ0 7) hδ7 (by norm_num)
  set g : ℝ := ((1048335 : ℕ) : ℝ) / (1048335 : ℝ) ^ 7
  have hg : 0 ≤ g := by positivity
  have hnum : 256 * (g ^ 1 * (2 * (2 * 8 : ℕ) * (1 / (2 ^ 256) ^ 2))) +
      32640 * (g ^ 2 * (2 * (2 * 8 : ℕ) * (1 / (2 ^ 197) ^ 2))) +
      2763520 * (g ^ 3 * (2 * (2 * 8 : ℕ) * (1 / 2 ^ 255))) +
      174792640 * (g ^ 4 * (2 * (2 * 8 : ℕ) * (1 / 2 ^ 153))) +
      8809549056 * (g ^ 5 * (2 * (2 * 8 : ℕ) * (1 / 2 ^ 75))) +
      368532802176 * (g ^ 6 * (2 * (2 * 8 : ℕ) * (1 / 2 ^ 52))) +
      13161885792000 * (g ^ 7 * (2 * (2 * 8 : ℕ) * (1 / 2 ^ 29))) +
      (256 * g * (8380417 ^ 2 / (16 * 523535 ^ 2)) ^ 8) ^ 8 /
        (40320 * (1 - 256 * g * (8380417 ^ 2 / (16 * 523535 ^ 2)) ^ 8)) +
      2 ^ 256 * (1 / 2 ^ 20) ^ 129 ≤ 1 / 2 ^ 588 := by
    rw [show (2 : ℝ) ^ 588 = (2 ^ 147) ^ 4 by rw [← pow_mul]]
    simp only [g]
    norm_num
  have hpow : ∀ t, 0 ≤ g ^ t := fun t => pow_nonneg hg t
  nlinarith [mul_le_mul_of_nonneg_left e1 (hpow 1), mul_le_mul_of_nonneg_left e2 (hpow 2),
    mul_le_mul_of_nonneg_left e3 (hpow 3), mul_le_mul_of_nonneg_left e4 (hpow 4),
    mul_le_mul_of_nonneg_left e5 (hpow 5), mul_le_mul_of_nonneg_left e6 (hpow 6),
    mul_le_mul_of_nonneg_left e7 (hpow 7)]

end GordieHowe.MLDSA.Regularity
