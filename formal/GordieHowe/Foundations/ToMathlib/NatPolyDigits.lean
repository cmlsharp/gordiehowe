-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-!
# Natural-number polynomials as base-`β` digit strings

A polynomial `P : ℕ[X]` whose coefficients are below `β` and vanish from degree `n`
on (`Bounded β n P`) is the digit string of the natural number `P.eval β`. This file
proves the facts that make `P ↦ P.eval β` usable for exact arithmetic on packed
digits:

* `Bounded.eval_lt`: `P.eval β < β ^ n`;
* `exists_split`, `Bounded.low`, `Bounded.high`, `Bounded.eval_split`: division and remainder by
  `β ^ n` split `P` into its low and high parts;
* `Bounded.digit`: `P.eval β / β ^ i % β = P.coeff i`;
* `Bounded.mul`, `Bounded.add`: coefficient and degree bounds of products and sums,
  so that products of bounded polynomials evaluate without carries;
* `Bounded.land_ones`: at `β = 2 ^ k`, the bitwise and with `ones k n = ∑_{i<n} β^i`
  replaces every digit by its parity.

Candidate for upstreaming near `Mathlib.Data.Nat.Digits`.
-/

open Polynomial

namespace Polynomial

/-- `P` has coefficients below `c` and vanishes from degree `n` on. -/
structure Bounded (c n : ℕ) (P : ℕ[X]) : Prop where
  coeff_lt : ∀ i, P.coeff i < c
  coeff_eq_zero : ∀ i, n ≤ i → P.coeff i = 0

namespace Bounded

variable {c n : ℕ} {P : ℕ[X]}

theorem mono {c' n' : ℕ} (h : Bounded c n P) (hc : c ≤ c') (hn : n ≤ n') : Bounded c' n' P :=
  ⟨fun i => (h.coeff_lt i).trans_le hc, fun i hi => h.coeff_eq_zero i (hn.trans hi)⟩

theorem divX (h : Bounded c (n + 1) P) : Bounded c n P.divX :=
  ⟨fun i => by rw [coeff_divX]; exact h.coeff_lt _,
    fun i hi => by rw [coeff_divX]; exact h.coeff_eq_zero _ (by omega)⟩

theorem eq_zero (h : Bounded c 0 P) : P = 0 :=
  Polynomial.ext fun i => by rw [h.coeff_eq_zero i (Nat.zero_le _), coeff_zero]

end Bounded

/-- `P.eval β = P.coeff 0 + β * P.divX.eval β`. -/
theorem eval_eq_coeff_zero_add_mul_divX (β : ℕ) (P : ℕ[X]) :
    P.eval β = P.coeff 0 + β * P.divX.eval β := by
  conv_lhs => rw [← divX_mul_X_add P]
  simp only [eval_add, eval_mul, eval_X, eval_C]
  ring

theorem Bounded.eval_lt {β n : ℕ} {P : ℕ[X]} (h : Bounded β n P) : P.eval β < β ^ n := by
  induction n generalizing P with
  | zero => rw [h.eq_zero, eval_zero]; exact Nat.one_pos
  | succ n ih =>
    have h1 := ih h.divX
    have h0 := h.coeff_lt 0
    rw [eval_eq_coeff_zero_add_mul_divX, pow_succ]
    calc P.coeff 0 + β * P.divX.eval β < β + β * P.divX.eval β := by omega
      _ = β * (P.divX.eval β + 1) := by ring
      _ ≤ β * β ^ n := Nat.mul_le_mul_left _ h1
      _ = β ^ n * β := mul_comm _ _

/-- The split of `P` at degree `n` into a low part below `X ^ n` and a high part. -/
theorem exists_split (n : ℕ) (P : ℕ[X]) : ∃ L H : ℕ[X], P = L + X ^ n * H ∧
    (∀ i, L.coeff i = if i < n then P.coeff i else 0) ∧ ∀ i, H.coeff i = P.coeff (i + n) := by
  induction n generalizing P with
  | zero => exact ⟨0, P, by simp, fun i => by simp, fun i => rfl⟩
  | succ n ih =>
    obtain ⟨L, H, hP, hL, hH⟩ := ih P.divX
    refine ⟨C (P.coeff 0) + X * L, H, ?_, fun i => ?_, fun i => ?_⟩
    · conv_lhs => rw [← divX_mul_X_add P, hP]
      ring
    · rcases i with _ | i
      · simp
      · rw [coeff_add, coeff_C, ite_eq_right (Nat.succ_ne_zero i), zero_add, coeff_X_mul, hL,
          coeff_divX]
        by_cases hi : i < n
        · rw [ite_eq_left hi, ite_eq_left (by omega)]
        · rw [ite_eq_right hi, ite_eq_right (by omega)]
    · rw [hH, coeff_divX, show i + n + 1 = i + (n + 1) by omega]

theorem Bounded.low {c m n : ℕ} {P L : ℕ[X]} (h : Bounded c m P)
    (hL : ∀ i, L.coeff i = if i < n then P.coeff i else 0) (hc : 0 < c) : Bounded c n L :=
  ⟨fun i => by rw [hL]; split_ifs; exacts [h.coeff_lt i, hc],
    fun i hi => by rw [hL, ite_eq_right (by omega)]⟩

theorem Bounded.high {c m n : ℕ} {P H : ℕ[X]} (h : Bounded c m P)
    (hH : ∀ i, H.coeff i = P.coeff (i + n)) : Bounded c (m - n) H :=
  ⟨fun i => by rw [hH]; exact h.coeff_lt _,
    fun i hi => by rw [hH]; exact h.coeff_eq_zero _ (by omega)⟩

theorem Bounded.eval_split {β m n : ℕ} {P L H : ℕ[X]} (h : Bounded β m P) (hP : P = L + X ^ n * H)
    (hL : ∀ i, L.coeff i = if i < n then P.coeff i else 0) :
    P.eval β % β ^ n = L.eval β ∧ P.eval β / β ^ n = H.eval β := by
  have hβ : 0 < β := (Nat.zero_le _).trans_lt (h.coeff_lt 0)
  have hlt := (h.low hL hβ).eval_lt
  have he : P.eval β = L.eval β + β ^ n * H.eval β := by
    rw [hP, eval_add, eval_mul, eval_pow, eval_X]
  have hpos : 0 < β ^ n := pow_pos hβ n
  refine ⟨?_, ?_⟩
  · rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rw [he, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, zero_add]

/-- The digit of `P.eval β` at position `i` is `P.coeff i`. -/
theorem Bounded.digit {β m : ℕ} {P : ℕ[X]} (h : Bounded β m P) (i : ℕ) :
    P.eval β / β ^ i % β = P.coeff i := by
  obtain ⟨L, H, hP, hL, hH⟩ := exists_split i P
  rw [(h.eval_split hP hL).2, eval_eq_coeff_zero_add_mul_divX, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt ((h.high hH).coeff_lt 0), hH, zero_add]

theorem Bounded.add {a b m : ℕ} {A B : ℕ[X]} (hA : Bounded a m A) (hB : Bounded b m B) :
    Bounded (a + b - 1) m (A + B) :=
  ⟨fun i => by have := hA.coeff_lt i; have := hB.coeff_lt i; rw [coeff_add]; omega,
    fun i hi => by rw [coeff_add, hA.coeff_eq_zero i hi, hB.coeff_eq_zero i hi]⟩

/-- A product's coefficient is a sum of at most `m` nonzero terms when the left factor
vanishes from degree `m` on. -/
theorem Bounded.mul {a b m m' : ℕ} {A B : ℕ[X]} (hA : Bounded a m A) (hB : Bounded b m' B) :
    Bounded (m * ((a - 1) * (b - 1)) + 1) (m + m' - 1) (A * B) := by
  classical
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · rw [coeff_mul, Nat.lt_succ_iff]
    have hterm : ∀ x ∈ Finset.antidiagonal i, A.coeff x.1 * B.coeff x.2 ≤
        if x.1 < m then (a - 1) * (b - 1) else 0 := by
      intro x _
      split_ifs with hx
      · exact Nat.mul_le_mul (Nat.le_sub_one_of_lt (hA.coeff_lt _))
          (Nat.le_sub_one_of_lt (hB.coeff_lt _))
      · rw [hA.coeff_eq_zero _ (not_lt.mp hx), zero_mul]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    refine Nat.mul_le_mul_right _ ?_
    calc ((Finset.antidiagonal i).filter fun x : ℕ × ℕ => x.1 < m).card ≤ (Finset.range m).card :=
          Finset.card_le_card_of_injOn Prod.fst
            (fun x hx => by
              simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx
              simpa using hx.2)
            (fun x hx y hy hxy => by
              simp only [Finset.coe_filter, Finset.mem_antidiagonal, Set.mem_ofPred_eq] at hx hy
              exact Prod.ext hxy (by omega))
      _ = m := Finset.card_range m
  · rw [coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    by_cases h1 : x.1 < m
    · rw [hB.coeff_eq_zero x.2 (by omega), mul_zero]
    · rw [hA.coeff_eq_zero x.1 (not_lt.mp h1), zero_mul]

/-! ## Parities of all digits at once -/

/-- `ones k n = ∑_{i < n} 2 ^ (k * i)`: a one in the lowest bit of each of `n` digits
of `k` bits. -/
def _root_.Nat.ones (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 2 ^ k * Nat.ones k n

/-- The bitwise and of a digit and a higher part with `1` plus a higher mask. -/
theorem _root_.Nat.two_pow_mul_add_land {k c y m : ℕ} (hk : 0 < k) (hc : c < 2 ^ k) :
    (2 ^ k * y + c) &&& (2 ^ k * m + 1) = 2 ^ k * (y &&& m) + c % 2 := by
  have h1 : 1 < 2 ^ k := Nat.one_lt_two_pow hk.ne'
  have h2 : c % 2 < 2 ^ k := (Nat.mod_lt _ (by norm_num)).trans_le (by omega)
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add y hc, Nat.testBit_two_pow_mul_add m h1,
    Nat.testBit_two_pow_mul_add _ h2, ← Nat.and_one_is_mod]
  split_ifs
  · rw [Nat.testBit_and]
  · rw [Nat.testBit_and]

/-- At `β = 2 ^ k`, the bitwise and with `ones k n` keeps the parity of each digit. -/
theorem Bounded.land_ones {k n : ℕ} {P : ℕ[X]} (hk : 0 < k) (h : Bounded (2 ^ k) n P) :
    ∃ Q : ℕ[X], Bounded 2 n Q ∧ (∀ i, Q.coeff i % 2 = P.coeff i % 2) ∧
      P.eval (2 ^ k) &&& Nat.ones k n = Q.eval (2 ^ k) := by
  induction n generalizing P with
  | zero => exact ⟨0, ⟨fun i => by simp, fun i _ => by simp⟩, fun i => by simp [h.eq_zero],
      by rw [h.eq_zero]; simp [Nat.ones]⟩
  | succ n ih =>
    obtain ⟨Q, hQ, hQc, hQe⟩ := ih h.divX
    refine ⟨C (P.coeff 0 % 2) + X * Q, ⟨fun i => ?_, fun i hi => ?_⟩, fun i => ?_, ?_⟩
    · rcases i with _ | i
      · simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul, add_zero]
        exact Nat.mod_lt _ (by norm_num)
      · rw [coeff_add, coeff_C, ite_eq_right (Nat.succ_ne_zero i), zero_add, coeff_X_mul]
        exact hQ.coeff_lt i
    · rcases i with _ | i
      · omega
      · rw [coeff_add, coeff_C, ite_eq_right (Nat.succ_ne_zero i), zero_add, coeff_X_mul]
        exact hQ.coeff_eq_zero i (by omega)
    · rcases i with _ | i
      · simp
      · rw [coeff_add, coeff_C, ite_eq_right (Nat.succ_ne_zero i), zero_add, coeff_X_mul, hQc,
          coeff_divX]
    · rw [eval_eq_coeff_zero_add_mul_divX, Nat.ones, add_comm (P.coeff 0), add_comm 1,
        Nat.two_pow_mul_add_land hk (h.coeff_lt 0), hQe]
      simp only [eval_add, eval_C, eval_mul, eval_X]
      ring

end Polynomial
