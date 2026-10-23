-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.OfflineMemory
public import GordieHowe.Foundations.Probability.ChallengeEvent
public import GordieHowe.Foundations.ToMathlib.Multiset
public import GordieHowe.Foundations.ToMathlib.Polynomial

@[expose] public section

/-!
# The permutation check as a challenge event

`assert_multiset_equal` (`lib/gordiehowe/lib/permutation.h`, `assert_products_equal`): the products
of `δ - x` over two lists of packed records agree. As a challenge event (`permEvent`): the
difference of the two products of `X - C x` is a polynomial of degree at most the longer list's
length, and the check passes with unequal multisets only when `δ` is one of its roots
(`multiset_eq_or_badAt`). The multiset equality follows from the polynomial identity by
`OfflineMemory.multiset_ofList_eq_of_prod_X_sub_C_eq`.
-/

namespace GordieHowe.PermutationEvent

open Polynomial

section CommRing

variable {R : Type*} [CommRing R]

/-- The product `∏ (X - C x)` over a list. -/
noncomputable def prodPoly (l : List R) : R[X] := (l.map fun a => X - C a).prod

theorem natDegree_prodPoly_le (l : List R) : (prodPoly l).natDegree ≤ l.length := by
  induction l with
  | nil => simp [prodPoly]
  | cons a l ih =>
    simp only [prodPoly, List.map_cons, List.prod_cons, List.length_cons] at ih ⊢
    refine (natDegree_mul_le).trans ?_
    have := natDegree_X_sub_C_le (R := R) a
    omega

theorem eval_prodPoly (δ : R) (l : List R) : (prodPoly l).eval δ = (l.map fun a => δ - a).prod := by
  induction l with
  | nil => simp [prodPoly]
  | cons a l ih =>
    simp only [prodPoly, List.map_cons, List.prod_cons, eval_mul, eval_sub, eval_X, eval_C] at ih ⊢
    rw [ih]

/-- Mapping the coefficients of `∏ (X - C x)` maps the list. -/
theorem map_prodPoly {S : Type*} [CommRing S] (f : R →+* S) (l : List R) :
    (prodPoly l).map f = prodPoly (l.map f) := by
  induction l with
  | nil => simp [prodPoly]
  | cons a l ih =>
    simp only [prodPoly, List.map_cons, List.prod_cons, Polynomial.map_mul, Polynomial.map_sub,
      map_X, map_C] at ih ⊢
    rw [ih]

/-- Every coefficient of `∏ (X - C x)` over a list of polynomials has degree at most the length
times a bound on the degrees of the entries: each factor has coefficients `1` and `-x`. -/
theorem natDegree_coeff_prodPoly_le {A : Type*} [CommRing A] {l : List A[X]} {d : ℕ}
    (hl : ∀ a ∈ l, a.natDegree ≤ d) (k : ℕ) : ((prodPoly l).coeff k).natDegree ≤ l.length * d := by
  induction l generalizing k with
  | nil =>
    simp only [prodPoly, List.map_nil, List.prod_nil, coeff_one]
    split_ifs <;> simp
  | cons a l ih =>
    have hfac : ∀ j, ((X - C a).coeff j).natDegree ≤ d := fun j => by
      rw [coeff_sub, coeff_X, coeff_C]
      have ha := hl a List.mem_cons_self
      split_ifs <;> simp_all
    have := Polynomial.natDegree_coeff_mul_le_of_le hfac
      (ih fun b hb => hl b (List.mem_cons_of_mem a hb)) k
    simp only [prodPoly, List.map_cons, List.prod_cons, List.length_cons] at this ⊢
    calc _ ≤ d + l.length * d := this
      _ = (l.length + 1) * d := by ring

end CommRing

variable {K : Type*} [Field K]

/-- **The permutation event** of two lists of packed records: the difference of the two products
`∏ (X - C x)`, of degree at most the longer list's length. -/
noncomputable def permEvent (l₁ l₂ : List K) : ChallengeEvent K :=
  ⟨prodPoly l₁ - prodPoly l₂, max l₁.length l₂.length,
    (natDegree_sub_le _ _).trans (max_le_max (natDegree_prodPoly_le l₁) (natDegree_prodPoly_le l₂))⟩

/-- **The permutation check**: equal products of `δ - x` give equal multisets, or `δ` is a root
of the permutation event. -/
theorem multiset_eq_or_badAt [DecidableEq K] {l₁ l₂ : List K} {δ : K}
    (h : (l₁.map fun a => δ - a).prod = (l₂.map fun a => δ - a).prod) :
    (↑l₁ : Multiset K) = ↑l₂ ∨ (permEvent l₁ l₂).BadAt δ := by
  by_cases hp : prodPoly l₁ - prodPoly l₂ = 0
  · exact Or.inl (OfflineMemory.multiset_ofList_eq_of_prod_X_sub_C_eq (sub_eq_zero.mp hp))
  · refine Or.inr ⟨hp, ?_⟩
    change (prodPoly l₁ - prodPoly l₂).eval δ = 0
    rw [eval_sub, eval_prodPoly, eval_prodPoly, h, sub_self]

/-- Equal multisets pass the check at every `δ`. -/
theorem prod_eq_of_multiset_eq {l₁ l₂ : List K} (h : (↑l₁ : Multiset K) = ↑l₂) (δ : K) :
    (l₁.map fun a => δ - a).prod = (l₂.map fun a => δ - a).prod :=
  ((Multiset.coe_eq_coe.mp h).map _).prod_eq

/-- **The filtered product** (`lib/gordiehowe/lib/permutation.h`, `assert_products_equal`, whose
left factors are `ACTIVE.mux(delta - LEFT, 1)`): with Boolean flags `a`, the product of
`1 + a_i (d_i - 1)` over a list of indices is the product of `d_i` over the indices whose flag is
`1` (an inactive entry contributes `1`). -/
theorem prod_mux_eq_prod_filter [DecidableEq K] {ι : Type*} (l : List ι) (a d : ι → K)
    (ha : ∀ i ∈ l, a i = 0 ∨ a i = 1) :
    (l.map fun i => 1 + a i * (d i - 1)).prod = ((l.filter fun i => a i = 1).map d).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hl : ∀ j ∈ l, a j = 0 ∨ a j = 1 := fun j hj => ha j (List.mem_cons_of_mem i hj)
    rcases ha i List.mem_cons_self with h0 | h1
    · have hne : ¬ a i = 1 := by rw [h0]; exact zero_ne_one
      simp [h0, ih hl]
    · simp [h1, ih hl]

end GordieHowe.PermutationEvent
