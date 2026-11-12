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
  given value with probability `1 / |α|`;
- `PMF.tsum_pmf_mul_add`, `PMF.tsum_pmf_mul_le_add`, `PMF.tsum_mul_le_tsum_mul_add`: averages in
  `ℝ≥0∞` of a function plus a constant;
- `PMF.bind_map_pair_apply`, `PMF.toOuterMeasure_bind_map_fst`: the joint law of a draw and a draw
  depending on it, and an event of its first coordinate;
- `ENNReal.tsum_mul_sum_comm`: exchange of a countable sum with a finite sum in `ℝ≥0∞`.
-/

open Finset
open scoped BigOperators ENNReal

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

section Averages

/-- **An average of `f + c` is the average of `f` plus `c`.** -/
theorem tsum_pmf_mul_add {α : Type*} (μ : PMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    ∑' x, μ x * (f x + c) = ∑' x, μ x * f x + c := by
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **An average of `f ≤ g + c` is at most the average of `g` plus `c`.** -/
theorem tsum_pmf_mul_le_add {α : Type*} (μ : PMF α) (f g : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ x, f x ≤ g x + c) : ∑' x, μ x * f x ≤ ∑' x, μ x * g x + c := by
  calc ∑' x, μ x * f x ≤ ∑' x, μ x * (g x + c) :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul_of_nonneg_left (h x) zero_le
    _ = ∑' x, μ x * g x + c := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- An average of bounds `x a ≤ y a + c` over a distribution is a bound `∑ x ≤ ∑ y + c`. -/
theorem tsum_mul_le_tsum_mul_add {α : Type*} (μ : PMF α) {x y : α → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a, x a ≤ y a + c) : ∑' a, μ a * x a ≤ ∑' a, μ a * y a + c := by
  calc ∑' a, μ a * x a ≤ ∑' a, (μ a * y a + μ a * c) :=
        ENNReal.tsum_le_tsum fun a => by rw [← mul_add]; gcongr; exact h a
    _ = ∑' a, μ a * y a + c := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **The joint law of `a ← μ` and `b ← ν a`** at `(a, b)`: `μ a · ν a b`. -/
theorem bind_map_pair_apply {α β : Type} (μ : PMF α) (ν : α → PMF β) (a : α) (b : β) :
    (μ.bind fun a => (ν a).map fun b => (a, b)) (a, b) = μ a * ν a b := by
  classical
  rw [PMF.bind_apply, tsum_eq_single a fun a' ha' => ?_]
  · rw [PMF.map_apply, tsum_eq_single b fun b' hb' => by simp [Ne.symm hb']]
    simp
  · rw [PMF.map_apply, ENNReal.tsum_eq_zero.2 fun b' => by simp [Ne.symm ha'], mul_zero]

/-- **An event of the first coordinate of a pair drawn uniformly then independently** has the
first coordinate's probability. -/
theorem toOuterMeasure_bind_map_fst {α β : Type} [Fintype α] [Nonempty α] (ν : PMF β)
    (p : α → Prop) :
    ((PMF.uniformOfFintype α).bind fun a => ν.map fun b => (a, b)).toOuterMeasure {d | p d.1} =
      (PMF.uniformOfFintype α).toOuterMeasure {a | p a} := by
  classical
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine tsum_congr fun a => ?_
  rw [PMF.toOuterMeasure_map_apply]
  by_cases ha : p a
  · have : (fun b => (a, b)) ⁻¹' {d : α × β | p d.1} = Set.univ := by ext; simp [ha]
    have h1 : ν.toOuterMeasure Set.univ = 1 := by
      rw [PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe]
    rw [this, h1, mul_one, Set.indicator_of_mem (show a ∈ {a | p a} from ha)]
  · have : (fun b => (a, b)) ⁻¹' {d : α × β | p d.1} = ∅ := by ext; simp [ha]
    rw [this, MeasureTheory.measure_empty, mul_zero,
      Set.indicator_of_notMem (show a ∉ {a | p a} from ha)]

end Averages

end PMF

namespace ENNReal

/-- **An average of finite averages is a finite average of averages** (exchange of a sum over a
countable type with a finite sum in `ℝ≥0∞`). -/
theorem tsum_mul_sum_comm {α β : Type*} [Fintype β] (u : α → ℝ≥0∞) (σ : β → ℝ≥0∞)
    (f : β → α → ℝ≥0∞) : ∑' x, u x * ∑ s, σ s * f s x = ∑ s, σ s * ∑' x, u x * f s x := by
  have h : ∀ x, u x * ∑ s, σ s * f s x = ∑ s, σ s * (u x * f s x) := fun x => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  simp_rw [h]
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  simp_rw [ENNReal.tsum_mul_left]

end ENNReal
