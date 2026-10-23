-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-!
# Counters of the binary fields

`GF2_128::as_counter` and `GF2_256::as_counter` (`lib/gf2k/gf2_128.h:335-346`,
`lib/gf2k/gf2_256.h:316-327` at `f21acd4`) multiply, over the set bits `i < 16` of `a`, the
counter basis `counter_beta_[i] = g ^ (2 ^ i)`, built from `g = kg_` by repeated squaring
(`gf2_128.h:154-157`, `gf2_256.h:146-150`). `GF2_256` multiplies by `1 + (cβ_i + 1) · bit`,
which is `cβ_i` or `1`. `asCounter` is that product; `asCounter_eq_pow` shows it is `g ^ a`
for `a < 2 ^ n`.
-/

namespace GordieHowe

/-- A number below `2 ^ n` is the sum of the powers of two at its set bits. -/
theorem sum_testBit_two_pow : ∀ (n a : ℕ), a < 2 ^ n →
    (∑ i : Fin n, if a.testBit i then 2 ^ (i : ℕ) else 0) = a
  | 0, a, h => by simp_all
  | n + 1, a, h => by
    rw [Fin.sum_univ_succ]
    have ih := sum_testBit_two_pow n (a / 2) (by rw [pow_succ] at h; omega)
    simp only [Fin.val_succ, Nat.testBit_succ, pow_succ, Fin.val_zero, pow_zero]
    rw [show (∑ i : Fin n, if (a / 2).testBit i then 2 ^ (i : ℕ) * 2 else 0) =
        (∑ i : Fin n, if (a / 2).testBit i then 2 ^ (i : ℕ) else 0) * 2 by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp, ih]
    rw [Nat.testBit_zero]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega

/-- The counter `as_counter(a)` over the counter basis `g ^ (2 ^ i)`, `i < n`. -/
def asCounter {M : Type*} [CommMonoid M] (g : M) (n a : ℕ) : M :=
  ∏ i : Fin n, if a.testBit i then g ^ 2 ^ (i : ℕ) else 1

theorem asCounter_eq_pow {M : Type*} [CommMonoid M] (g : M) {n a : ℕ} (ha : a < 2 ^ n) :
    asCounter g n a = g ^ a := by
  unfold asCounter
  conv_rhs => rw [← sum_testBit_two_pow n a ha, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ => by split_ifs <;> simp

end GordieHowe
