-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Minpoly.Field

@[expose] public section

/-!
# Powers of an element of an extension of a finite field

An element `x` algebraic over a finite field `k` with `q` elements lies in the
subfield `k⟮x⟯`, which has `q ^ d` elements for `d` the degree of `x`'s minimal
polynomial, so `x ^ (q ^ d) = x`. Mathlib states the polynomial form
(`Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`); this is its
evaluation at `x`.

Candidate for upstreaming next to `Mathlib.FieldTheory.Finite.Extension`.
-/

open Polynomial

/-- An element algebraic over a finite field `k` of degree `d` is fixed by the
`(card k)^d`-power map. -/
theorem pow_card_pow_natDegree_minpoly {k L : Type*} [Field k] [Finite k] [Field L] [Algebra k L]
    {x : L} (hx : IsIntegral k x) : x ^ Nat.card k ^ (minpoly k x).natDegree = x := by
  obtain ⟨q, hq⟩ :=
    (minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp dvd_rfl
  have h := congrArg (aeval x) hq
  rw [map_mul, minpoly.aeval, zero_mul, map_sub, map_pow, aeval_X] at h
  exact sub_eq_zero.mp h
