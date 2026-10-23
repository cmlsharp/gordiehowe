-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import GordieHowe.Foundations.ToMathlib.FiniteField
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

@[expose] public section

/-!
# Orders of elements from prime-factor certificates

`orderOf_eq_prod_of_pow_ne_one`: an element with `x ^ m = 1` for `m` the product of a
list of primes, and `x ^ (m / q) ≠ 1` for every `q` in the list, has order `m`; the
list is the factorization a certificate checks (`orderOf_eq_of_pow_and_pow_div_prime`
with the prime divisors of `m` enumerated).

`orderOf_le_card_pow_natDegree_minpoly_sub_one`: over a finite field `k` with `q`
elements, an element of order `m` has degree `d` with `m ≤ q ^ d - 1`, because it is
fixed by the `q ^ d`-power map (`pow_card_pow_natDegree_minpoly`). This bounds the
degree of a subfield generator from below by its order.

Candidates for upstreaming next to `Mathlib.GroupTheory.OrderOfElement`.
-/

/-- A prime dividing a product of primes is one of them. -/
theorem Nat.Prime.mem_of_dvd_prod {p : ℕ} {l : List ℕ} (hp : p.Prime) (hl : ∀ q ∈ l, q.Prime)
    (h : p ∣ l.prod) : p ∈ l := by
  obtain ⟨a, ha, hpa⟩ := (Nat.prime_iff.mp hp).dvd_prod_iff.mp h
  rwa [(Nat.prime_dvd_prime_iff_eq hp (hl a ha)).mp hpa]

/-- The order of `x` is the product `m` of the primes in `l` when `x ^ m = 1` and
`x ^ (m / q) ≠ 1` for each `q ∈ l`. -/
theorem orderOf_eq_prod_of_pow_ne_one {G : Type*} [Monoid G] {x : G} {l : List ℕ}
    (hl : ∀ q ∈ l, q.Prime) (hx : x ^ l.prod = 1) (hne : ∀ q ∈ l, x ^ (l.prod / q) ≠ 1) :
    orderOf x = l.prod := by
  have hpos : 0 < l.prod := List.prod_pos fun q hq => (hl q hq).pos
  exact orderOf_eq_of_pow_and_pow_div_prime hpos hx fun p hp hdvd =>
    hne p (hp.mem_of_dvd_prod hl hdvd)

/-- The order of a nonzero element algebraic over a finite field `k` of degree `d` is at
most `(card k) ^ d - 1`. -/
theorem orderOf_le_card_pow_natDegree_minpoly_sub_one {k L : Type*} [Field k] [Finite k]
    [Field L] [Algebra k L] {x : L} (hx : IsIntegral k x) (hx0 : x ≠ 0) :
    orderOf x ≤ Nat.card k ^ (minpoly k x).natDegree - 1 := by
  have hfix := pow_card_pow_natDegree_minpoly hx
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have hd := minpoly.natDegree_pos hx
  have hlt : 1 < Nat.card k ^ (minpoly k x).natDegree := Nat.one_lt_pow hd.ne' hq
  have hone : x ^ (Nat.card k ^ (minpoly k x).natDegree - 1) = 1 := by
    refine mul_left_cancel₀ hx0 ?_
    rw [← pow_succ', Nat.sub_add_cancel hlt.le, hfix, mul_one]
  exact Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hone)

/-- An element algebraic over a finite field `k` whose order is at least `(card k) ^ (s - 1)`
has degree at least `s`. -/
theorem le_natDegree_minpoly_of_card_pow_le_orderOf {k L : Type*} [Field k] [Finite k]
    [Field L] [Algebra k L] {x : L} (hx : IsIntegral k x) (hx0 : x ≠ 0) {s : ℕ}
    (hord : Nat.card k ^ (s - 1) ≤ orderOf x) : s ≤ (minpoly k x).natDegree := by
  have hle := orderOf_le_card_pow_natDegree_minpoly_sub_one hx hx0
  have hq : 0 < Nat.card k := Finite.card_pos
  by_contra hlt
  have := Nat.pow_le_pow_right hq (show (minpoly k x).natDegree ≤ s - 1 by omega)
  have := Nat.one_le_pow (minpoly k x).natDegree _ hq
  omega
