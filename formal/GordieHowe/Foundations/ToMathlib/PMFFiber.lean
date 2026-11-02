-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFTV

@[expose] public section

/-!
# Fibre bounds and product events for PMFs

- `PMF.sum_mul_toOuterMeasure_comp_le`: a run that depends on the coins only through `F` hits a
  coin-dependent target with probability at most `γ` when every fibre of `F` gives the target
  conditional probability at most `γ`;
- `PMF.toOuterMeasure_pi_forall`: the probability of a product set under `PMF.pi` is the product
  of the coordinate probabilities;
- `PMF.uniformOfFintype_map_eval`: the value of a uniform random function at a point is uniform;
- `PMF.uniformOfFintype_table_guess_le`: one entry of a uniform table, given the images of all
  entries, is guessed with probability at most `γ` if each entry is.
-/

open scoped ENNReal
open Finset

namespace PMF

/-- A run that depends on the coins only through `F` hits a coin-dependent target with
probability at most `γ`, when every fibre of `F` gives the target conditional probability at most
`γ`. -/
theorem sum_mul_toOuterMeasure_comp_le {T V Ω : Type*} [Fintype T] (μ : PMF T) (F : T → V)
    (ρ : V → PMF Ω) (P : T → Ω → Prop) {γ : ℝ≥0∞}
    (h : ∀ t₀ o, μ.toOuterMeasure {t | F t = F t₀ ∧ P t o} ≤ γ * μ.toOuterMeasure {t | F t = F t₀}) :
    ∑ t, μ t * (ρ (F t)).toOuterMeasure {o | P t o} ≤ γ := by
  classical
  -- regroup a sum over `t` by the value of `F t`
  have hfib : ∀ a : T → ℝ≥0∞,
      ∑ v ∈ univ.image F, ∑ t, (if F t = v then a t else 0) = ∑ t, a t := fun a => by
    rw [sum_comm]
    exact sum_congr rfl fun t _ => by rw [sum_ite_eq]; simp
  have hmeas : ∀ (Q : T → Prop) [DecidablePred Q],
      μ.toOuterMeasure {t | Q t} = ∑ t, if Q t then μ t else 0 := fun Q _ => by
    rw [toOuterMeasure_apply_fintype]
    exact sum_congr rfl fun t _ => by simp [Set.indicator_apply]
  have key : ∀ v ∈ univ.image F,
      ∑ t, (if F t = v then μ t * (ρ (F t)).toOuterMeasure {o | P t o} else 0) ≤
        γ * μ.toOuterMeasure {t | F t = v} := by
    intro v hv
    obtain ⟨t₀, -, rfl⟩ := mem_image.1 hv
    have hrw : ∀ t, (if F t = F t₀ then μ t * (ρ (F t)).toOuterMeasure {o | P t o} else 0) =
        ∑' o, (if F t = F t₀ ∧ P t o then μ t else 0) * ρ (F t₀) o := fun t => by
      by_cases ht : F t = F t₀
      · simp only [ht, ite_true, true_and, toOuterMeasure_apply, Set.indicator_apply,
          Set.mem_ofPred_eq, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun o => by split_ifs <;> simp
      · simp [ht]
    simp_rw [hrw]
    rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
    simp_rw [← sum_mul]
    calc ∑' o, (∑ t, if F t = F t₀ ∧ P t o then μ t else 0) * ρ (F t₀) o
        ≤ ∑' o, γ * μ.toOuterMeasure {t | F t = F t₀} * ρ (F t₀) o := by
          refine ENNReal.tsum_le_tsum fun o => ?_
          gcongr
          rw [← hmeas (fun t => F t = F t₀ ∧ P t o)]
          exact h t₀ o
      _ = γ * μ.toOuterMeasure {t | F t = F t₀} := by
          rw [ENNReal.tsum_mul_left, tsum_coe, mul_one]
  calc ∑ t, μ t * (ρ (F t)).toOuterMeasure {o | P t o}
      = ∑ v ∈ univ.image F,
          ∑ t, (if F t = v then μ t * (ρ (F t)).toOuterMeasure {o | P t o} else 0) :=
        (hfib _).symm
    _ ≤ ∑ v ∈ univ.image F, γ * μ.toOuterMeasure {t | F t = v} := sum_le_sum key
    _ = γ := by
        simp_rw [hmeas, ← mul_sum, hfib]
        rw [sum_coe, mul_one]

/-- The probability of a product set under `PMF.pi` is the product of the coordinate
probabilities. -/
theorem toOuterMeasure_pi_forall {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] (p : ∀ i, PMF (β i)) (A : ∀ i, Set (β i)) :
    (pi p).toOuterMeasure {f | ∀ i, f i ∈ A i} = ∏ i, (p i).toOuterMeasure (A i) := by
  classical
  simp_rw [toOuterMeasure_apply_fintype]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun f _ => ?_
  by_cases hf : ∀ i, f i ∈ A i
  · rw [Set.indicator_of_mem (by exact hf), pi_apply]
    exact prod_congr rfl fun i _ => (Set.indicator_of_mem (hf i) _).symm
  · push Not at hf
    obtain ⟨i, hi⟩ := hf
    rw [Set.indicator_of_notMem (by simpa using ⟨i, hi⟩)]
    exact (prod_eq_zero (mem_univ i) (Set.indicator_of_notMem hi _)).symm

/-- One entry of a uniform table of independent entries, given the images `φ e (t j e)` of all
entries, is guessed with probability at most `γ` if each entry is. -/
theorem uniformOfFintype_table_guess_le {ι E C Y Z : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] [Fintype C] [Nonempty C] (φ : E → C → Y) (g : E → C → Z)
    {γ : ℝ≥0∞}
    (hγ : ∀ e y z, (uniformOfFintype C).toOuterMeasure {c | g e c = z ∧ φ e c = y} ≤
      γ * (uniformOfFintype C).toOuterMeasure {c | φ e c = y})
    (v : ι → E → Y) (j₀ : ι) (e₀ : E) (z : Z) :
    (uniformOfFintype (ι → E → C)).toOuterMeasure
        {t | (fun j e => φ e (t j e)) = v ∧ g e₀ (t j₀ e₀) = z} ≤
      γ * (uniformOfFintype (ι → E → C)).toOuterMeasure {t | (fun j e => φ e (t j e)) = v} := by
  set U := uniformOfFintype C
  have hU : uniformOfFintype (ι → E → C) = pi fun _ => pi fun _ => U := by
    simp only [U, pi_uniformOfFintype]
  -- the two events as product sets
  let A : ι → E → Set C := fun j e => {c | φ e c = v j e ∧ (j = j₀ ∧ e = e₀ → g e c = z)}
  let B : ι → E → Set C := fun j e => {c | φ e c = v j e}
  have hA : {t : ι → E → C | (fun j e => φ e (t j e)) = v ∧ g e₀ (t j₀ e₀) = z} =
      {t | ∀ j, t j ∈ {r : E → C | ∀ e, r e ∈ A j e}} := by
    ext t
    simp only [Set.mem_ofPred_eq, A, funext_iff]
    constructor
    · rintro ⟨h1, h2⟩ j e
      exact ⟨h1 j e, by rintro ⟨rfl, rfl⟩; exact h2⟩
    · intro h
      exact ⟨fun j e => (h j e).1, (h j₀ e₀).2 ⟨rfl, rfl⟩⟩
  have hB : {t : ι → E → C | (fun j e => φ e (t j e)) = v} =
      {t | ∀ j, t j ∈ {r : E → C | ∀ e, r e ∈ B j e}} := by
    ext t
    simp [B, funext_iff]
  rw [hA, hB, hU, toOuterMeasure_pi_forall, toOuterMeasure_pi_forall]
  simp_rw [toOuterMeasure_pi_forall]
  rw [Fintype.prod_eq_mul_prod_compl j₀, Fintype.prod_eq_mul_prod_compl j₀ (fun j => ∏ e, _),
    Fintype.prod_eq_mul_prod_compl e₀ (fun e => U.toOuterMeasure (A j₀ e)),
    Fintype.prod_eq_mul_prod_compl e₀ (fun e => U.toOuterMeasure (B j₀ e))]
  have hrest : ∏ j ∈ {j₀}ᶜ, ∏ e, U.toOuterMeasure (A j e) =
      ∏ j ∈ {j₀}ᶜ, ∏ e, U.toOuterMeasure (B j e) := by
    refine prod_congr rfl fun j hj => prod_congr rfl fun e _ => ?_
    have : j ≠ j₀ := by simpa using hj
    simp [A, B, this]
  have hrest' : ∏ e ∈ {e₀}ᶜ, U.toOuterMeasure (A j₀ e) =
      ∏ e ∈ {e₀}ᶜ, U.toOuterMeasure (B j₀ e) := by
    refine prod_congr rfl fun e he => ?_
    have : e ≠ e₀ := by simpa using he
    simp [A, B, this]
  have h0 : A j₀ e₀ = {c | g e₀ c = z ∧ φ e₀ c = v j₀ e₀} := by
    ext c
    simp [A, and_comm]
  rw [hrest, hrest', h0]
  calc _ ≤ (γ * U.toOuterMeasure (B j₀ e₀) * ∏ e ∈ {e₀}ᶜ, U.toOuterMeasure (B j₀ e)) *
          ∏ j ∈ {j₀}ᶜ, ∏ e, U.toOuterMeasure (B j e) := by
        gcongr
        exact hγ e₀ (v j₀ e₀) z
    _ = _ := by ring

/-- The value of a uniform random function at a point is uniform. -/
theorem uniformOfFintype_map_eval {E C : Type*} [Fintype E] [DecidableEq E] [Fintype C]
    [Nonempty C] (e : E) :
    (uniformOfFintype (E → C)).map (fun t => t e) = uniformOfFintype C := by
  classical
  ext b
  rw [← toOuterMeasure_apply_singleton, toOuterMeasure_map_apply, ← toOuterMeasure_apply_singleton]
  have hset : (fun t : E → C => t e) ⁻¹' {b} =
      {t | ∀ i, t i ∈ (if i = e then {b} else Set.univ : Set C)} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro rfl i
      split_ifs with h
      · subst h; rfl
      · trivial
    · intro h
      simpa using h e
  rw [hset, ← pi_uniformOfFintype, toOuterMeasure_pi_forall, Fintype.prod_eq_single e]
  · simp
  · intro i hi
    simp [hi, ENNReal.mul_inv_cancel]
