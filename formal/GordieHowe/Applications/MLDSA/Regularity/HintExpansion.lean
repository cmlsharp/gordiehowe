-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.CountIndicator
public import GordieHowe.Applications.MLDSA.Regularity.KernelMass

@[expose] public section

/-!
# The hint-count expansion and its weight `Λ`

The hint-count check `#fires ≤ ω` of FIPS 204 Algorithm 7 line 28 is a count of `N = 256 k`
events, so `1[#fires ≤ ω] = ∑_{t : ZMod (N+1)} c_t e(t · #fires)` (`ZMod.indicator_le_eq_sum`),
and `e(t · #fires)` is a product of per-coordinate factors (plan, item 3). The weight
`Λ = ∑_t ‖c_t‖` enters the regularity bound linearly. This file bounds it crudely by the
harmonic sum: `Λ ≤ 1 + ∑_{1 ≤ a ≤ M/2} 1/a` (`sum_norm_countCoeff_le`), so `Λ ≤ 11` at
ML-DSA-65 (`M = 1537`, `ω = 55`) and `Λ ≤ 12` at ML-DSA-87 (`M = 2049`, `ω = 75`). The exact
values are `2.62` and `2.74`; the crude bound costs about two bits.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

/-- Folding a sum over `ZMod n` by the centered absolute value: for `g ≥ 0`,
`∑_t g |t| ≤ g 0 + 2 ∑_{1 ≤ a ≤ n/2} g a`. -/
theorem sum_comp_natAbs_valMinAbs_le {n : ℕ} [NeZero n] (g : ℕ → ℝ) (hg : ∀ a, 0 ≤ g a) :
    ∑ t : ZMod n, g t.valMinAbs.natAbs ≤ g 0 + 2 * ∑ a ∈ (Ico 1 (n / 2 + 1) : Finset ℕ), g a := by
  have hn := NeZero.pos n
  have hsum_eq : ∑ t : ZMod n, g t.valMinAbs.natAbs = ∑ v ∈ range n, g (min v (n - v)) := by
    refine Finset.sum_nbij' (fun t : ZMod n => t.val) (fun v => (v : ZMod n))
      (fun t _ => Finset.mem_range.mpr (ZMod.val_lt t)) (fun _ _ => Finset.mem_univ _)
      (fun t _ => ZMod.natCast_zmod_val t) (fun v hv => ZMod.val_natCast_of_lt
        (Finset.mem_range.mp hv)) (fun t _ => by rw [ZMod.valMinAbs_natAbs_eq_min])
  have hsplit : range n = range 1 ∪ ((Ico 1 (n / 2 + 1) : Finset ℕ) ∪ Ico (n / 2 + 1) n) := by
    ext v
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hd1 : Disjoint (range 1) ((Ico 1 (n / 2 + 1) : Finset ℕ) ∪ Ico (n / 2 + 1) n) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at hv hv'
    omega
  have hd2 : Disjoint (Ico 1 (n / 2 + 1) : Finset ℕ) (Ico (n / 2 + 1) n) :=
    Finset.Ico_disjoint_Ico_consecutive _ _ _
  have hlow : ∑ v ∈ (Ico 1 (n / 2 + 1) : Finset ℕ), g (min v (n - v)) =
      ∑ a ∈ (Ico 1 (n / 2 + 1) : Finset ℕ), g a :=
    Finset.sum_congr rfl fun v hv => by
      rw [Finset.mem_Ico] at hv
      rw [min_eq_left (by omega)]
  have hhigh : ∑ v ∈ (Ico (n / 2 + 1) n : Finset ℕ), g (min v (n - v)) ≤
      ∑ a ∈ (Ico 1 (n / 2 + 1) : Finset ℕ), g a := by
    calc ∑ v ∈ (Ico (n / 2 + 1) n : Finset ℕ), g (min v (n - v))
        = ∑ v ∈ (Ico (n / 2 + 1) n : Finset ℕ), g (n - v) :=
          Finset.sum_congr rfl fun v hv => by
            rw [Finset.mem_Ico] at hv
            rw [min_eq_right (by omega)]
      _ = ∑ a ∈ (Ico (n + 1 - n) (n + 1 - (n / 2 + 1)) : Finset ℕ), g a :=
          Finset.sum_Ico_reflect g (n / 2 + 1) (by omega)
      _ ≤ ∑ a ∈ (Ico 1 (n / 2 + 1) : Finset ℕ), g a := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun a _ _ => hg a
          intro a ha
          simp only [Finset.mem_Ico] at ha ⊢
          omega
  rw [hsum_eq, hsplit, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_range_one, hlow]
  simp only [Nat.sub_zero, min_eq_left (Nat.zero_le _)]
  linarith

/-- `Λ ≤ 1 + ∑_{1 ≤ a ≤ M/2} 1/a` for `ω < M`. -/
theorem sum_norm_countCoeff_le (M ω : ℕ) [NeZero M] (hω : ω < M) :
    ∑ t : ZMod M, ‖ZMod.countCoeff M ω t‖ ≤
      1 + ∑ a ∈ (Ico 1 (M / 2 + 1) : Finset ℕ), (1 / (a : ℝ)) := by
  set g : ℕ → ℝ := fun a => if a = 0 then 1 else 1 / (2 * a)
  have hg : ∀ a, 0 ≤ g a := fun a => by simp only [g]; split_ifs <;> positivity
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)
  have hpt : ∀ t : ZMod M, ‖ZMod.countCoeff M ω t‖ ≤ g t.valMinAbs.natAbs := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp only [ZMod.valMinAbs_zero, Int.natAbs_zero, g, if_true]
      refine (ZMod.norm_countCoeff_zero ω).trans ?_
      rw [div_le_one hM]
      exact_mod_cast hω
    · have h0 : t.valMinAbs.natAbs ≠ 0 := by
        rw [Int.natAbs_ne_zero, ne_eq, ZMod.valMinAbs_eq_zero]; exact ht
      simp only [g, if_neg h0]
      refine (ZMod.norm_countCoeff_le ω ht).trans (le_of_eq ?_)
      rw [← ZMod.natAbs_valMinAbs_neg t, Nat.cast_natAbs, Int.cast_abs]
  calc ∑ t : ZMod M, ‖ZMod.countCoeff M ω t‖ ≤ ∑ t : ZMod M, g t.valMinAbs.natAbs :=
        Finset.sum_le_sum fun t _ => hpt t
    _ ≤ g 0 + 2 * ∑ a ∈ (Ico 1 (M / 2 + 1) : Finset ℕ), g a :=
        sum_comp_natAbs_valMinAbs_le g hg
    _ = 1 + ∑ a ∈ (Ico 1 (M / 2 + 1) : Finset ℕ), (1 / (a : ℝ)) := by
        simp only [g, if_true, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [if_neg (by simp at ha; omega)]
        have : (a : ℝ) ≠ 0 := by
          have : 1 ≤ a := (Finset.mem_Ico.mp ha).1
          positivity
        field_simp

/-- `Λ ≤ 11` at ML-DSA-44 (`N = 1024` hint coordinates, `ω = 80`). -/
theorem sum_norm_countCoeff_le_mldsa44 : ∑ t : ZMod 1025, ‖ZMod.countCoeff 1025 80 t‖ ≤ 11 := by
  refine (sum_norm_countCoeff_le 1025 80 (by norm_num)).trans ?_
  have hd := sum_Ico_two_pow_inv_le 0 10
  norm_num at hd
  have hsub : ∑ a ∈ (Ico 1 (1025 / 2 + 1) : Finset ℕ), (1 / (a : ℝ)) ≤
      ∑ a ∈ (Ico 1 1024 : Finset ℕ), (1 / (a : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => by
      rw [Finset.mem_Ico] at ha ⊢; omega) fun a _ _ => one_div_nonneg.mpr (Nat.cast_nonneg a)
  have : ∑ a ∈ (Ico 1 1024 : Finset ℕ), (1 / (a : ℝ)) ≤ 10 := by simpa only [one_div] using hd
  linarith

/-- `Λ ≤ 11` at ML-DSA-65 (`N = 1536` hint coordinates, `ω = 55`). -/
theorem sum_norm_countCoeff_le_mldsa65 : ∑ t : ZMod 1537, ‖ZMod.countCoeff 1537 55 t‖ ≤ 11 := by
  refine (sum_norm_countCoeff_le 1537 55 (by norm_num)).trans ?_
  have hd := sum_Ico_two_pow_inv_le 0 10
  norm_num at hd
  have hsub : ∑ a ∈ (Ico 1 (1537 / 2 + 1) : Finset ℕ), (1 / (a : ℝ)) ≤
      ∑ a ∈ (Ico 1 1024 : Finset ℕ), (1 / (a : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => by
      rw [Finset.mem_Ico] at ha ⊢; omega) fun a _ _ => one_div_nonneg.mpr (Nat.cast_nonneg a)
  have : ∑ a ∈ (Ico 1 1024 : Finset ℕ), (1 / (a : ℝ)) ≤ 10 := by simpa only [one_div] using hd
  linarith

/-- `Λ ≤ 12` at ML-DSA-87 (`N = 2048` hint coordinates, `ω = 75`). -/
theorem sum_norm_countCoeff_le_mldsa87 : ∑ t : ZMod 2049, ‖ZMod.countCoeff 2049 75 t‖ ≤ 12 := by
  refine (sum_norm_countCoeff_le 2049 75 (by norm_num)).trans ?_
  have hd := sum_Ico_two_pow_inv_le 0 11
  norm_num at hd
  have hsub : ∑ a ∈ (Ico 1 (2049 / 2 + 1) : Finset ℕ), (1 / (a : ℝ)) ≤
      ∑ a ∈ (Ico 1 2048 : Finset ℕ), (1 / (a : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => by
      rw [Finset.mem_Ico] at ha ⊢; omega) fun a _ _ => one_div_nonneg.mpr (Nat.cast_nonneg a)
  have : ∑ a ∈ (Ico 1 2048 : Finset ℕ), (1 / (a : ℝ)) ≤ 11 := by simpa only [one_div] using hd
  linarith

end GordieHowe.MLDSA.Regularity
