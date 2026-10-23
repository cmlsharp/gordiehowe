-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Probability.Distributions.Uniform
public import GordieHowe.Foundations.ToMathlib.PMFTV

@[expose] public section

/-!
# Uniform laws and averages under PMFs on finite types

Candidates for Mathlib:

- `PMF.sum_toReal_map_mul`: an average over the image of a PMF is an average over the PMF;
- `PMF.abs_sum_toReal_mul_sub_le`: averages of a bounded function under two PMFs differ by at most
  the bound times their total variation distance;
- `PMF.map_uniformOfFintype_equiv`, `map_uniformOfFintype_assoc`, `map_fst_uniformOfFintype`,
  `map_snd_uniformOfFintype`: images of uniform laws under equivalences and projections;
- `PMF.toOuterMeasure_uniformOfFintype_fst_eq`: the first component of a uniform pair takes a
  given value with probability `1 / |α|`.
-/

open Finset
open scoped BigOperators

namespace PMF

section Average

variable {α β : Type*} [Fintype α] [Fintype β]

/-- An average over the image of a PMF is an average over the PMF (change of variables). -/
theorem sum_toReal_map_mul (p : PMF α) (f : α → β) (g : β → ℝ) :
    ∑ b, (p.map f b).toReal * g b = ∑ a, (p a).toReal * g (f a) := by
  classical
  simp_rw [toReal_map_apply, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_eq_single (f a) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

/-- The averages of a function with values in `[0, M]` under two PMFs differ by at most `M` times
their total variation distance. -/
theorem abs_sum_toReal_mul_sub_le (p q : PMF β) {g : β → ℝ} {M : ℝ} (hg0 : ∀ b, 0 ≤ g b)
    (hgM : ∀ b, g b ≤ M) :
    |∑ b, (p b).toReal * g b - ∑ b, (q b).toReal * g b| ≤ M * tvDist p q := by
  have hsum : ∑ b, ((p b).toReal - (q b).toReal) * (M / 2) = 0 := by
    rw [← sum_mul, sum_sub_distrib, sum_toReal, sum_toReal, sub_self, zero_mul]
  have h : ∑ b, (p b).toReal * g b - ∑ b, (q b).toReal * g b =
      ∑ b, ((p b).toReal - (q b).toReal) * (g b - M / 2) := by
    have e : ∑ b, ((p b).toReal - (q b).toReal) * (g b - M / 2) =
        ∑ b, ((p b).toReal * g b - (q b).toReal * g b) -
          ∑ b, ((p b).toReal - (q b).toReal) * (M / 2) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun b _ => by ring
    rw [e, hsum, sub_zero, sum_sub_distrib]
  rw [h, tvDist_eq_sum]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_div_assoc', mul_sum, sum_div]
  refine sum_le_sum fun b _ => ?_
  rw [abs_mul]
  have : |g b - M / 2| ≤ M / 2 := abs_sub_le_iff.2 ⟨by linarith [hgM b], by linarith [hg0 b]⟩
  calc |(p b).toReal - (q b).toReal| * |g b - M / 2|
      ≤ |(p b).toReal - (q b).toReal| * (M / 2) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = _ := by ring


end Average

section Uniform

variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]

/-- The image of a uniform law under an equivalence is uniform. -/
theorem map_uniformOfFintype_equiv (e : α ≃ β) :
    (uniformOfFintype α).map e = uniformOfFintype β := by
  classical
  ext b
  rw [map_apply, tsum_eq_single (e.symm b) fun a ha => by
    rw [if_neg (fun h => ha (by rw [h, Equiv.symm_apply_apply]))]]
  simp [uniformOfFintype_apply, Fintype.card_congr e]

/-- A uniform law on `(α × β) × γ` as the uniform `α` followed by the uniform `β × γ`. -/
theorem map_uniformOfFintype_assoc {γ δ : Type*} [Fintype γ] [Nonempty γ] (f : (α × β) × γ → δ) :
    (uniformOfFintype ((α × β) × γ)).map f =
      (uniformOfFintype α).bind fun a => (uniformOfFintype (β × γ)).map fun bc => f ((a, bc.1), bc.2) := by
  rw [← map_uniformOfFintype_equiv (Equiv.prodAssoc α β γ).symm, map_comp,
    uniformOfFintype_prod_eq_bind, map_bind]
  congr 1
  funext a
  rw [map_comp]
  rfl

/-- The first component of a uniform pair is uniform. -/
theorem map_fst_uniformOfFintype :
    (uniformOfFintype (α × β)).map Prod.fst = uniformOfFintype α := by
  rw [uniformOfFintype_prod_eq_bind, map_bind]
  simp only [map_comp]
  have : ∀ a : α, (uniformOfFintype β).map (Prod.fst ∘ Prod.mk a) = pure a := fun a => by
    simp only [Function.comp_def]
    exact map_const _ _
  simp [this]

/-- The second component of a uniform pair is uniform. -/
theorem map_snd_uniformOfFintype :
    (uniformOfFintype (α × β)).map Prod.snd = uniformOfFintype β := by
  rw [← map_fst_uniformOfFintype (α := β) (β := α), ← map_uniformOfFintype_equiv (Equiv.prodComm α β),
    map_comp]
  rfl

/-- The probability that the first component of a uniform pair takes a given value. -/
theorem toOuterMeasure_uniformOfFintype_fst_eq (a : α) :
    ((uniformOfFintype (α × β)).toOuterMeasure {p | p.1 = a}).toReal = (Fintype.card α : ℝ)⁻¹ := by
  classical
  rw [toReal_toOuterMeasure_apply, Fintype.sum_prod_type]
  simp only [Set.mem_ofPred_eq, toReal_uniformOfFintype_apply, Fintype.card_prod]
  rw [Finset.sum_eq_single a (fun a' _ ha' => by simp [ha']) (by simp)]
  simp only [ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul]
  have : (Fintype.card β : ℝ) ≠ 0 := by simp
  field_simp


end Uniform

end PMF
