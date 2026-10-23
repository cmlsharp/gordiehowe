-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

/-!
# A primitive `2^(n+1)`-th root from a single `-1` witness

The standard order-doubling argument for a power-of-two root of unity: if
`x ^ (2 ^ n) = -1`, then `x` is a primitive `2 ^ (n + 1)`-th root of unity.
Squaring the hypothesis gives `x ^ (2 ^ (n + 1)) = 1`, and it is not the case
that `x ^ (2 ^ n) = 1` (that value is `-1 ≠ 1`), so the order of `x` is
exactly `2 ^ (n + 1)` by `orderOf_eq_prime_pow` at the prime `2`.

Candidate for upstreaming next to `Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots`.
-/

/-- If `x ^ (2 ^ n) = -1`, then `x` is a primitive `2 ^ (n + 1)`-th root of
unity. -/
theorem IsPrimitiveRoot.of_pow_two_pow_eq_neg_one {M : Type*} [CommMonoid M] [HasDistribNeg M]
    {x : M} {n : ℕ} (hneg : (-1 : M) ≠ 1) (h : x ^ 2 ^ n = -1) :
    IsPrimitiveRoot x (2 ^ (n + 1)) := by
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_prime_pow (p := 2) (n := n) ?_ ?_
  · rw [h]; exact hneg
  · rw [pow_succ, pow_mul, h, neg_one_sq]
