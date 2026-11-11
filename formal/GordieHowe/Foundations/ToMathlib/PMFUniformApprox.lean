-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFTV

public section

/-!
# Approximating a law by a uniform pushforward

* `exists_map_uniformOfFintype_tvDist_le`: every law `ν` on a finite type `T` is within
  `|T| / D` in total variation of the uniform law on `Fin D` pushed forward by some map: give each
  value `⌊D ν(j)⌋` points of `Fin D` and the rest to one value.

About Mathlib objects only.
-/

open Finset
open scoped BigOperators ENNReal

namespace PMF

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The uniform law on `Fin D` pushed forward through the first component of an equivalence with
a sigma type puts mass `k j / D` on `j`. -/
theorem toReal_map_uniformOfFintype_sigma {D : ℕ} [NeZero D] (k : T → ℕ)
    (e : Fin D ≃ Σ j, Fin (k j)) (j : T) :
    ((uniformOfFintype (Fin D)).map (fun d => (e d).1) j).toReal = (k j : ℝ) / D := by
  classical
  rw [toReal_map_apply]
  simp only [toReal_uniformOfFintype_apply, Fintype.card_fin]
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, div_eq_mul_inv]
  congr 1
  have hc : (univ.filter fun d : Fin D => (e d).1 = j).card =
      (univ.filter fun s : (Σ j, Fin (k j)) => s.1 = j).card := by
    refine Finset.card_bij (fun d _ => e d) (fun d hd => by simpa using hd)
      (fun d _ d' _ h => e.injective h) fun s hs => ⟨e.symm s, by simpa using hs, by simp⟩
  have hs : (univ.filter fun s : (Σ j, Fin (k j)) => s.1 = j) =
      (univ : Finset (Fin (k j))).map ⟨Sigma.mk j, sigma_mk_injective⟩ := by
    ext ⟨j', x⟩
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl; exact ⟨x, rfl⟩
    · rintro ⟨y, h⟩; exact (Sigma.mk.inj_iff.1 h).1.symm
  rw [hc, hs, card_map, card_univ, Fintype.card_fin]

/-- **A law on a finite type is close to a uniform pushforward**: for every `D > 0` there is a
map `f : Fin D → T` with the uniform law on `Fin D` pushed forward by `f` within `|T| / D` of `ν`
in total variation. -/
theorem exists_map_uniformOfFintype_tvDist_le (ν : PMF T) (D : ℕ) [NeZero D] :
    ∃ f : Fin D → T, tvDist ((uniformOfFintype (Fin D)).map f) ν ≤ Fintype.card T / D := by
  classical
  obtain ⟨j₀, -⟩ := ν.support_nonempty
  set a : T → ℝ := fun j => (ν j).toReal
  have ha0 : ∀ j, 0 ≤ a j := fun j => ENNReal.toReal_nonneg
  have ha1 : ∑ j, a j = 1 := sum_toReal ν
  have hD : (0 : ℝ) < D := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne D))
  set fl : T → ℕ := fun j => ⌊(D : ℝ) * a j⌋₊
  set s : ℕ := ∑ j ∈ univ.erase j₀, fl j
  have hfl : ∀ j, (fl j : ℝ) ≤ D * a j := fun j => Nat.floor_le (mul_nonneg hD.le (ha0 j))
  have hfl' : ∀ j, (D : ℝ) * a j - 1 < fl j := fun j => by
    have := Nat.lt_floor_add_one ((D : ℝ) * a j); simp only [fl]; linarith
  have hsD : s ≤ D := by
    have h1 : (s : ℝ) ≤ D := by
      calc (s : ℝ) = ∑ j ∈ univ.erase j₀, (fl j : ℝ) := by simp [s]
        _ ≤ ∑ j ∈ univ.erase j₀, (D : ℝ) * a j := sum_le_sum fun j _ => hfl j
        _ ≤ ∑ j, (D : ℝ) * a j := sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
            fun j _ _ => mul_nonneg hD.le (ha0 j)
        _ = D := by rw [← mul_sum, ha1, mul_one]
    exact_mod_cast h1
  set k : T → ℕ := fun j => if j = j₀ then D - s else fl j
  have hk : ∑ j, k j = D := by
    rw [← add_sum_erase _ _ (mem_univ j₀)]
    simp only [k, ite_eq_left rfl]
    rw [sum_congr rfl fun j hj => ite_eq_right (ne_of_mem_erase hj)]
    exact Nat.sub_add_cancel hsD
  have hcard : Fintype.card (Σ j, Fin (k j)) = D := by
    rw [Fintype.card_sigma]; simpa using hk
  let e : Fin D ≃ Σ j, Fin (k j) := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun d => (e d).1, ?_⟩
  rw [tvDist_eq_sum]
  simp only [toReal_map_uniformOfFintype_sigma k e]
  -- the errors off `j₀`
  have herr : ∀ j, j ≠ j₀ → |(k j : ℝ) / D - a j| ≤ 1 / D := fun j hj => by
    simp only [k, ite_eq_right hj]
    have h1 : (fl j : ℝ) / D ≤ a j := by
      rw [div_le_iff₀ hD]; linarith [hfl j]
    have h2 : a j - 1 / D ≤ fl j / D := by
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hD]; linarith [hfl' j]
    rw [abs_le]
    constructor <;> linarith
  have hsum0 : ∑ j, ((k j : ℝ) / D - a j) = 0 := by
    rw [sum_sub_distrib, ha1, ← sum_div, ← Nat.cast_sum, hk, div_self hD.ne', sub_self]
  have hj₀ : |(k j₀ : ℝ) / D - a j₀| ≤ ∑ j ∈ univ.erase j₀, |(k j : ℝ) / D - a j| := by
    rw [← add_sum_erase _ _ (mem_univ j₀)] at hsum0
    rw [show (k j₀ : ℝ) / D - a j₀ = -∑ j ∈ univ.erase j₀, ((k j : ℝ) / D - a j) by linarith,
      abs_neg]
    exact abs_sum_le_sum_abs _ _
  have hoff : ∑ j ∈ univ.erase j₀, |(k j : ℝ) / D - a j| ≤ Fintype.card T / D := by
    calc ∑ j ∈ univ.erase j₀, |(k j : ℝ) / D - a j| ≤ ∑ _j ∈ univ.erase j₀, (1 : ℝ) / D :=
          sum_le_sum fun j hj => herr j (ne_of_mem_erase hj)
      _ ≤ Fintype.card T / D := by
          rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul, mul_one_div]
          gcongr
          exact_mod_cast Nat.sub_le _ _
  rw [← add_sum_erase _ _ (mem_univ j₀)]
  linarith

end PMF
