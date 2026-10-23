-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Zify
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Column-query probabilities for the errata counterexamples

The Ligero tests of AHIV22 and of Longfellow (as analysed by CHVY25) draw a uniform challenge `r`
from a finite set, receive the prover's response, and then open a set `Q` of `t` distinct columns
chosen uniformly among the `t`-element subsets of the `n` columns. `queryProb` is the probability
of an event of `(r, Q)` under that distribution, as an exact rational: the number of pairs in the
event over the number of pairs. `queryProb_eq_sum` evaluates it for the shape every column test has
(a check on the response alone, and a per-column check at every opened column): the opened set
passes exactly when it lies inside the response's agreement set.

Used by `GordieHowe.Errata.AHIV22` and `GordieHowe.Errata.CHVY25`.
-/

namespace GordieHowe.Errata

open Finset

/-- The sample space of a column test: a challenge from `R` and an opened set of `t` distinct
columns among `n`. -/
def querySpace (R : Type*) [Fintype R] (n t : ℕ) : Finset (R × Finset (Fin n)) :=
  (univ : Finset R) ×ˢ (univ : Finset (Fin n)).powersetCard t

theorem card_querySpace (R : Type*) [Fintype R] (n t : ℕ) :
    #(querySpace R n t) = Fintype.card R * n.choose t := by
  simp [querySpace, card_powersetCard]

/-- The probability of the event `E r Q` when the challenge `r` is uniform on `R` and,
independently, the opened set `Q` is uniform among the `t`-element subsets of the `n` columns. -/
def queryProb (R : Type*) [Fintype R] (n t : ℕ) (E : R → Finset (Fin n) → Prop)
    [∀ r Q, Decidable (E r Q)] : ℚ :=
  #{x ∈ querySpace R n t | E x.1 x.2} / #(querySpace R n t)

/-- The `t`-subsets of `s` inside which `P` holds everywhere are the `t`-subsets of the set where
`P` holds. -/
theorem card_powersetCard_filter_forall {α : Type*} (s : Finset α) (P : α → Prop)
    [DecidablePred P] (t : ℕ) :
    #{Q ∈ s.powersetCard t | ∀ j ∈ Q, P j} = (#{j ∈ s | P j}).choose t := by
  rw [← card_powersetCard]
  congr 1
  ext Q
  simp only [mem_filter, mem_powersetCard, subset_iff]
  constructor
  · rintro ⟨⟨hs, hc⟩, hP⟩
    exact ⟨fun j hj => ⟨hs hj, hP j hj⟩, hc⟩
  · rintro ⟨hs, hc⟩
    exact ⟨⟨fun j hj => (hs hj).1, hc⟩, fun j hj => (hs hj).2⟩

/-- A column test that accepts when the response passes a check `A r` and the per-column check
`B r j` holds at every opened column: for each challenge the accepted opened sets are the
`t`-subsets of the agreement set `{j | B r j}`. -/
theorem card_filter_querySpace {R : Type*} [Fintype R] {n t : ℕ}
    {E : R → Finset (Fin n) → Prop} [∀ r Q, Decidable (E r Q)] (A : R → Prop) [DecidablePred A]
    (B : R → Fin n → Prop) [∀ r, DecidablePred (B r)]
    (hE : ∀ r Q, E r Q ↔ A r ∧ ∀ j ∈ Q, B r j) :
    #{x ∈ querySpace R n t | E x.1 x.2} = ∑ r, if A r then (#{j | B r j}).choose t else 0 := by
  rw [querySpace, card_filter, sum_product]
  refine sum_congr rfl fun r _ => ?_
  split_ifs with hA
  · rw [← card_powersetCard_filter_forall, card_filter]
    exact sum_congr rfl fun Q _ => by simp [hE, hA]
  · exact sum_eq_zero fun Q _ => by simp [hE, hA]

/-- `queryProb` of a column test, by `card_filter_querySpace`. -/
theorem queryProb_eq_sum {R : Type*} [Fintype R] {n t : ℕ} {E : R → Finset (Fin n) → Prop}
    [∀ r Q, Decidable (E r Q)] (A : R → Prop) [DecidablePred A] (B : R → Fin n → Prop)
    [∀ r, DecidablePred (B r)] (hE : ∀ r Q, E r Q ↔ A r ∧ ∀ j ∈ Q, B r j) :
    queryProb R n t E =
      ((∑ r, if A r then (#{j | B r j}).choose t else 0 : ℕ) : ℚ) /
        (Fintype.card R * n.choose t) := by
  rw [queryProb, card_querySpace, card_filter_querySpace A B hE]
  push_cast
  rfl

/-- A column test's acceptance probability is at most the density of a bad challenge set plus
`C(T, t)/C(n, t)`, when outside the bad set every challenge passing the response check has at
most `T` agreeing columns. -/
theorem queryProb_le_of_bad {R : Type*} [Fintype R] {n t : ℕ} {E : R → Finset (Fin n) → Prop}
    [∀ r Q, Decidable (E r Q)] (A : R → Prop) [DecidablePred A] (B : R → Fin n → Prop)
    [∀ r, DecidablePred (B r)] (hE : ∀ r Q, E r Q ↔ A r ∧ ∀ j ∈ Q, B r j)
    (Bad : Finset R) (T : ℕ) (hT : ∀ r, r ∉ Bad → A r → #{j | B r j} ≤ T) :
    queryProb R n t E ≤ (#Bad : ℚ) / Fintype.card R + (T.choose t : ℚ) / n.choose t := by
  classical
  rw [queryProb_eq_sum A B hE]
  have hnum : (∑ r, if A r then (#{j | B r j}).choose t else 0) ≤
      #Bad * n.choose t + Fintype.card R * T.choose t := by
    calc _ ≤ ∑ r, ((if r ∈ Bad then n.choose t else 0) + T.choose t) := by
          refine sum_le_sum fun r _ => ?_
          by_cases hA : A r
          · simp only [hA, ↓reduceIte]
            by_cases hBad : r ∈ Bad
            · simp only [hBad, ↓reduceIte]
              refine le_add_right (Nat.choose_le_choose t ?_)
              simpa using card_le_univ (univ.filter fun j => B r j)
            · simp only [hBad, ↓reduceIte, zero_add]
              exact Nat.choose_le_choose t (hT r hBad hA)
          · simp only [hA, ↓reduceIte]
            exact Nat.zero_le _
      _ = #Bad * n.choose t + Fintype.card R * T.choose t := by
          rw [sum_add_distrib, sum_ite_mem, univ_inter, sum_const, sum_const, card_univ]
          simp
  have hnum' : ((∑ r, if A r then (#{j | B r j}).choose t else 0 : ℕ) : ℚ) ≤
      (#Bad : ℚ) * n.choose t + Fintype.card R * T.choose t := by
    exact_mod_cast hnum
  rcases Nat.eq_zero_or_pos (Fintype.card R) with hR | hR
  · rw [hR]
    simp only [Nat.cast_zero, zero_mul, div_zero, zero_add]
    positivity
  rcases Nat.eq_zero_or_pos (n.choose t) with hn | hn
  · rw [hn]
    simp only [Nat.cast_zero, mul_zero, div_zero]
    positivity
  have hR' : (0 : ℚ) < Fintype.card R := by exact_mod_cast hR
  have hn' : (0 : ℚ) < n.choose t := by exact_mod_cast hn
  rw [div_add_div _ _ hR'.ne' hn'.ne', div_le_div_iff_of_pos_right (by positivity)]
  linarith

/-- `C(a, t) · n^t ≤ C(n, t) · a^t` for `a ≤ n`: the factors `(a − i)/(n − i) ≤ a/n`. -/
theorem choose_mul_pow_le_choose_mul_pow {a n : ℕ} (h : a ≤ n) (t : ℕ) :
    a.choose t * n ^ t ≤ n.choose t * a ^ t := by
  have hd : a.descFactorial t * n ^ t ≤ n.descFactorial t * a ^ t := by
    induction t with
    | zero => simp
    | succ t ih =>
      have hstep : (a - t) * n ≤ (n - t) * a := by
        rcases le_or_gt t a with hta | hta
        · zify [hta, hta.trans h]
          nlinarith
        · rw [Nat.sub_eq_zero_of_le hta.le, zero_mul]
          exact Nat.zero_le _
      calc a.descFactorial (t + 1) * n ^ (t + 1)
          = ((a - t) * n) * (a.descFactorial t * n ^ t) := by
            rw [Nat.descFactorial_succ, pow_succ]
            ring
        _ ≤ ((n - t) * a) * (n.descFactorial t * a ^ t) := Nat.mul_le_mul hstep ih
        _ = n.descFactorial (t + 1) * a ^ (t + 1) := by
            rw [Nat.descFactorial_succ, pow_succ]
            ring
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    mul_assoc, mul_assoc] at hd
  exact Nat.le_of_mul_le_mul_left hd (Nat.factorial_pos t)

/-- **The query ratio.** For `a ≤ n` and `a ≤ b`, `C(a, t)/C(n, t) ≤ (b/n)^t`. -/
theorem choose_div_choose_le_pow {a b n : ℕ} (han : a ≤ n) (hab : a ≤ b) (t : ℕ) :
    (a.choose t : ℚ) / n.choose t ≤ ((b : ℚ) / n) ^ t := by
  rcases Nat.eq_zero_or_pos (n.choose t) with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]
    positivity
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    obtain rfl : t = 0 := by
      by_contra ht
      exact (Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero ht)).not_gt hpos
    simp
  rw [div_pow, div_le_div_iff₀ (by exact_mod_cast hpos) (by positivity)]
  have hmain := (choose_mul_pow_le_choose_mul_pow han t).trans
    (Nat.mul_le_mul_left (n.choose t) (Nat.pow_le_pow_left hab t))
  rw [mul_comm ((b : ℚ) ^ t)]
  exact_mod_cast hmain

end GordieHowe.Errata
