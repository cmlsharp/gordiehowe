-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Products over `List.range` as products over `Fin`

Candidate for upstreaming, next to Mathlib's `Fin.prod_univ_eq_prod_range`.
-/

/-- **The product of `g` mapped over `List.range n`** is the product of `g i` over `i : Fin n`. -/
theorem List.prod_map_range {M : Type*} [CommMonoid M] (n : ℕ) (g : ℕ → M) :
    ((List.range n).map g).prod = ∏ i : Fin n, g i := by
  rw [Fin.prod_univ_eq_prod_range g n, Finset.prod_eq_multiset_prod, Finset.range_val,
    Multiset.range, Multiset.map_coe, Multiset.prod_coe]
