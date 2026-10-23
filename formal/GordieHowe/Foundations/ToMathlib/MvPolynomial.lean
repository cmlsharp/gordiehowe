-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

/-! General degree bounds for products; candidates for upstreaming to Mathlib. -/

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- A list of factors of degree at most `d` has product degree at most `d` times
its length. -/
theorem totalDegree_list_prod_le {l : List (MvPolynomial σ R)} {d : ℕ}
    (h : ∀ p ∈ l, p.totalDegree ≤ d) : l.prod.totalDegree ≤ d * l.length := by
  apply (totalDegree_list_prod l).trans
  have hb := List.sum_le_length_nsmul (l.map totalDegree) d (by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    exact h p hp)
  simpa [List.length_map, Nat.mul_comm] using hb

end MvPolynomial
