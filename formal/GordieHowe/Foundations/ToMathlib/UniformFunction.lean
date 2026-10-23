-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Algebra.Order.BigOperators.Expect
public import GordieHowe.Foundations.ToMathlib.PMFTV

@[expose] public section

/-!
# Uniform random functions

Facts about a uniformly random function `H : X → Y` on finite types, candidates for Mathlib:

- `expect_apply_eq_apply`: two distinct points collide with probability `1 / |Y|`;
- `prob_comp_eq_comp`: the same for the images under a map whose fibres have equal size;
- `prob_comp_eq_comp_of_local`: the same for two points chosen from the function's values on a set
  of other points;
- `splitAlong`: a function on `X'` as its restriction to the complement of the range of an
  embedding `f : A ↪ X'` and its pullback along `f`.
-/

open Finset
open scoped BigOperators

namespace GordieHowe

/-- Two distinct points of a uniform random function collide with probability `1 / |Y|`. -/
theorem expect_apply_eq_apply {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Nonempty Y] {x x' : X} (hx : x ≠ x') :
    𝔼 H : X → Y, (if H x = H x' then (1 : ℝ) else 0) = (Fintype.card Y : ℝ)⁻¹ := by
  set R := {j // j ≠ x} → Y
  have hsplit : ∑ H : X → Y, (if H x = H x' then (1 : ℝ) else 0) =
      ∑ y : Y, ∑ r : R, (if y = r ⟨x', hx.symm⟩ then (1 : ℝ) else 0) := by
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Equiv.funSplitAt x Y) _ _ fun H => by simp
  have hcount : ∑ H : X → Y, (if H x = H x' then (1 : ℝ) else 0) = Fintype.card R := by
    rw [hsplit, sum_comm]
    simp
  have hcard : Fintype.card (X → Y) = Fintype.card Y * Fintype.card R := by
    rw [Fintype.card_congr (Equiv.funSplitAt x Y), Fintype.card_prod]
  have hR : (Fintype.card R : ℝ) ≠ 0 := by
    simp [R]
  rw [Fintype.expect_eq_sum_div_card, hcount, hcard, Nat.cast_mul]
  field_simp

/-- Two distinct points of a uniform function have answers with equal images under a map `g`
whose fibres all have the same size with probability `1 / |Z|`. -/
theorem prob_comp_eq_comp {X' Y' Z : Type*} [Fintype X'] [DecidableEq X'] [Fintype Y'] [Nonempty Y']
    [Fintype Z] [DecidableEq Z] [Nonempty Z] (g : Y' → Z)
    (hg : (PMF.uniformOfFintype Y').map g = PMF.uniformOfFintype Z) {a b : X'} (hab : a ≠ b) :
    ((PMF.uniformOfFintype (X' → Y')).toOuterMeasure {G | g (G a) = g (G b)}).toReal =
      (Fintype.card Z : ℝ)⁻¹ := by
  classical
  have hmap : (PMF.uniformOfFintype (X' → Y')).map (fun G => g ∘ G) = PMF.uniformOfFintype (X' → Z) := by
    rw [← PMF.pi_uniformOfFintype, ← PMF.pi_uniformOfFintype]
    have := PMF.pi_map (fun _ : X' => PMF.uniformOfFintype Y') (fun _ => g)
    rw [show (fun G : X' → Y' => g ∘ G) = fun G i => g (G i) from rfl, this]
    simp only [hg]
  have hset : {G : X' → Y' | g (G a) = g (G b)} = (fun G => g ∘ G) ⁻¹' {G' | G' a = G' b} := rfl
  rw [hset, ← PMF.toOuterMeasure_map_apply, hmap, PMF.toReal_toOuterMeasure_apply]
  have h := expect_apply_eq_apply (X := X') (Y := Z) hab
  rw [Finset.expect_eq_sum_div_card] at h
  rw [← h]
  simp only [Set.mem_ofPred_eq, PMF.toReal_uniformOfFintype_apply, div_eq_mul_inv]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun G _ => by split_ifs <;> simp

/-- Two points of a uniform function chosen from its values on a set `p` of other points, distinct
at every function, have answers with equal images under a map `g` whose fibres all have the same
size with probability `1 / |Z|`. -/
theorem prob_comp_eq_comp_of_local {X' Y' Z : Type*} [Fintype X'] [DecidableEq X'] [Fintype Y']
    [Nonempty Y'] [Fintype Z] [DecidableEq Z] [Nonempty Z] (g : Y' → Z)
    (hg : (PMF.uniformOfFintype Y').map g = PMF.uniformOfFintype Z) (p : X' → Prop) [DecidablePred p]
    {a b : (X' → Y') → X'} (hloc : ∀ G G', (∀ x, p x → G x = G' x) → a G = a G' ∧ b G = b G')
    (ha : ∀ G, ¬ p (a G)) (hb : ∀ G, ¬ p (b G)) (hab : ∀ G, a G ≠ b G) :
    ((PMF.uniformOfFintype (X' → Y')).toOuterMeasure {G | g (G (a G)) = g (G (b G))}).toReal =
      (Fintype.card Z : ℝ)⁻¹ := by
  classical
  have hexp : ∀ {α : Type _} [Fintype α] [Nonempty α] (s : Set α) [DecidablePred (· ∈ s)],
      ((PMF.uniformOfFintype α).toOuterMeasure s).toReal = 𝔼 x, (if x ∈ s then (1 : ℝ) else 0) := by
    intro α _ _ s _
    rw [PMF.toReal_toOuterMeasure_apply, Fintype.expect_eq_sum_div_card, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  set e := Equiv.piEquivPiSubtypeProd p (fun _ : X' => Y')
  rw [hexp]
  rw [(Fintype.expect_equiv e.symm (fun w => if e.symm w ∈ {G : X' → Y' | g (G (a G)) = g (G (b G))}
    then (1 : ℝ) else 0) _ fun w => rfl).symm, ← Finset.univ_product_univ, Finset.expect_product]
  refine (Finset.expect_congr rfl fun u _ => ?_).trans (Finset.expect_const Finset.univ_nonempty _)
  obtain ⟨v₀⟩ : Nonempty ((i : {x // ¬ p x}) → Y') := inferInstance
  set G₀ := e.symm (u, v₀)
  have hagree : ∀ v, ∀ x, p x → e.symm (u, v) x = G₀ x := fun v x hx => by
    simp [G₀, e, Equiv.piEquivPiSubtypeProd_symm_apply, hx]
  have hev : ∀ v : (i : {x // ¬ p x}) → Y', (e.symm (u, v) ∈ {G : X' → Y' | g (G (a G)) = g (G (b G))}) ↔
      g (v ⟨a G₀, ha G₀⟩) = g (v ⟨b G₀, hb G₀⟩) := fun v => by
    obtain ⟨h1, h2⟩ := hloc _ _ (hagree v)
    simp only [Set.mem_ofPred_eq, h1, h2]
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, ha G₀, hb G₀]
  simp only [hev]
  have hpr := prob_comp_eq_comp (X' := {x // ¬ p x}) g hg (a := ⟨a G₀, ha G₀⟩)
    (b := ⟨b G₀, hb G₀⟩) fun he => hab G₀ (congrArg Subtype.val he)
  rw [hexp] at hpr
  simpa only [Set.mem_ofPred_eq] using hpr

section Split

variable {A X' Y' : Type*} [Fintype A] [DecidableEq A] [Fintype X'] [DecidableEq X'] [Fintype Y']
  (f : A ↪ X')

/-- A function on `X'` as its restriction to the complement of the range of `f` and its
pullback along `f`. -/
noncomputable def splitAlong : (X' → Y') ≃ ({x // x ∉ Set.range f} → Y') × (A → Y') :=
  ((Equiv.arrowCongr ((Equiv.Set.sumCompl (Set.range f)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective f f.injective).symm (Equiv.refl _)))
    (Equiv.refl Y')).trans (Equiv.sumArrowEquivProdArrow _ _ _)).trans (Equiv.prodComm _ _)

theorem splitAlong_symm_apply_embed (Fo : {x // x ∉ Set.range f} → Y') (FX : A → Y') (a : A) :
    (splitAlong f).symm (Fo, FX) (f a) = FX a := by
  have h : (Equiv.Set.sumCompl (Set.range f)).symm (f a) = Sum.inl ⟨f a, a, rfl⟩ :=
    Equiv.Set.sumCompl_symm_apply_of_mem (Set.mem_range_self a)
  simp only [splitAlong, Equiv.symm_trans_apply, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.swap_prod_mk, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.symm_symm,
    Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, Equiv.trans_apply, h,
    Equiv.sumCongr_apply, Sum.map_inl, id_eq, Equiv.sumArrowEquivProdArrow_symm_apply_inl]
  congr 1
  exact (Equiv.ofInjective f f.injective).symm_apply_eq.2 rfl

theorem splitAlong_symm_apply_of_notMem (Fo : {x // x ∉ Set.range f} → Y') (FX : A → Y') {x : X'}
    (hx : x ∉ Set.range f) : (splitAlong f).symm (Fo, FX) x = Fo ⟨x, hx⟩ := by
  have h : (Equiv.Set.sumCompl (Set.range f)).symm x = Sum.inr ⟨x, hx⟩ :=
    Equiv.Set.sumCompl_symm_apply_of_notMem hx
  simp only [splitAlong, Equiv.symm_trans_apply, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.swap_prod_mk, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.symm_symm,
    Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, Equiv.trans_apply, h,
    Equiv.sumCongr_apply, Sum.map_inr, id_eq, Equiv.sumArrowEquivProdArrow_symm_apply_inr]

end Split

/-! ### Averages of evaluations of a uniform random function -/

section Evaluations

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- The value of a uniform random function at a point is uniform. -/
theorem expect_comp_apply (x : X) (g : Y → ℂ) : 𝔼 H : X → Y, g (H x) = 𝔼 y, g y := by
  rw [Fintype.expect_equiv (Equiv.funSplitAt x Y) (fun H : X → Y => g (H x)) (fun p => g p.1)
      fun H => rfl,
    ← Finset.univ_product_univ, Finset.expect_product]
  simp

/-- The values of a uniform random function at two distinct points are independent uniform. -/
theorem expect_comp_apply_mul_comp_apply {x x' : X} (hx : x ≠ x') (g h : Y → ℂ) :
    𝔼 H : X → Y, g (H x) * h (H x') = (𝔼 y, g y) * 𝔼 y, h y := by
  rw [Fintype.expect_equiv (Equiv.funSplitAt x Y) (fun H : X → Y => g (H x) * h (H x'))
      (fun p => g p.1 * h (p.2 ⟨x', hx.symm⟩)) fun H => rfl,
    ← Finset.univ_product_univ, Finset.expect_product]
  have hr : 𝔼 r : ({j // j ≠ x} → Y), h (r ⟨x', hx.symm⟩) = 𝔼 y, h y :=
    expect_comp_apply (⟨x', hx.symm⟩ : {j // j ≠ x}) h
  simp only [← Finset.mul_expect, hr, ← Finset.expect_mul]

end Evaluations

end GordieHowe
