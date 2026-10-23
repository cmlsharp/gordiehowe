-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.SpecificDegree

@[expose] public section

/-!
# Roots of a product of linear factors over a `Finset`

Candidate for upstreaming; see Mathlib's `Polynomial.roots_multiset_prod_X_sub_C`.

# Coefficient degrees of a product over a polynomial ring

Candidate for upstreaming next to `Polynomial.natDegree_mul_le_of_le`.

# Irreducibility of `X² − C a` from a non-square witness

Candidate for upstreaming next to `Polynomial.irreducible_of_degree_le_three_of_not_isRoot`.
-/

open Polynomial

/-- The roots of `∏ i ∈ s, (X - C (f i))`, as a multiset, are the image under `f` of the finset's
underlying multiset. Follows from `Polynomial.roots_multiset_prod_X_sub_C` after rewriting the
finset product as the multiset product of the multiset mapped by `f` and then by `a ↦ X - C a`
(`Multiset.map_map`). -/
theorem roots_prod_X_sub_C_image {K : Type*} [Field K] {ι : Type*} (s : Finset ι) (f : ι → K) :
    (∏ i ∈ s, (Polynomial.X - C (f i))).roots = s.val.map f := by
  have h : (∏ i ∈ s, (Polynomial.X - C (f i))) = ((s.val.map f).map fun a => X - C a).prod := by
    rw [Multiset.map_map]; rfl
  rw [h]
  exact Polynomial.roots_multiset_prod_X_sub_C _

/-- `X² − C a` is irreducible over a field where `a` is not a square: a root of
the polynomial would be a square root of `a`. Discharges the degree hypothesis
of `Polynomial.irreducible_of_degree_le_three_of_not_isRoot` from
`Polynomial.natDegree_X_pow_sub_C`. -/
theorem irreducible_X_sq_sub_C_of_not_isSquare {K : Type*} [Field K] {a : K}
    (ha : ¬ IsSquare a) : Irreducible (X ^ 2 - C a) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_X_pow_sub_C, Finset.mem_Icc]; omega
  · intro x hx
    apply ha
    refine ⟨x, ?_⟩
    have hx' : x ^ 2 = a := by
      rw [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hx
      exact hx
    rw [← hx', pow_two]

/-- Over a polynomial ring: if every coefficient of `p` has degree at most `a` and every
coefficient of `q` has degree at most `b`, every coefficient of `p * q` has degree at most
`a + b` (`Polynomial.coeff_mul` and `Polynomial.natDegree_mul_le_of_le`). -/
theorem Polynomial.natDegree_coeff_mul_le_of_le {A : Type*} [Semiring A] {p q : A[X][X]}
    {a b : ℕ} (hp : ∀ j, (p.coeff j).natDegree ≤ a) (hq : ∀ j, (q.coeff j).natDegree ≤ b)
    (k : ℕ) : ((p * q).coeff k).natDegree ≤ a + b := by
  rw [coeff_mul]
  exact natDegree_sum_le_of_forall_le _ _ fun x _ => natDegree_mul_le_of_le (hp x.1) (hq x.2)
