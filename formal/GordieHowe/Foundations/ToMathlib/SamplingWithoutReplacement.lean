-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.Finset.Powerset

@[expose] public section

/-!
# Exponential moments of samples without replacement

Hoeffding (*Probability inequalities for sums of bounded random variables*, JASA 58(301), 1963,
Theorem 4, p. 28) compares a sample `X_1, …, X_τ` drawn without replacement from a finite
population with a sample `Y_1, …, Y_τ` drawn with replacement: `E f(∑ X_i) ≤ E f(∑ Y_i)` for
every continuous convex `f`. This file proves the case `f = exp(λ ·)`, which is all a Chernoff
bound needs. For `f = exp(λ ·)` the left side is the average over `τ`-subsets `T` of
`∏_{j ∈ T} e^{λ x_j}` and the right side is `(mean_j e^{λ x_j})^τ`, so the statement is the
endpoint of Maclaurin's inequality for nonnegative reals:

    subsetProdSum s a τ ≤ (#s).choose τ · ((∑_{j ∈ s} a_j) / #s) ^ τ,

where `subsetProdSum s a τ = ∑_{T ⊆ s, #T = τ} ∏_{j ∈ T} a_j` is the elementary symmetric
polynomial of degree `τ` in the `a_j` (`subsetProdSum_le`). The proof is by induction on `s`:
adding one element reduces it to the tangent-line bound `m^k ((k+1) t − k m) ≤ t^(k+1)` for
`m, t ≥ 0` (`Real.pow_mul_sub_le_pow_succ`, Bernoulli's inequality).

* `subsetProdSum_insert`: `e_{k+1}(s ∪ {x}) = e_{k+1}(s) + a_x · e_k(s)`;
* `subsetProdSum_le`: Maclaurin's endpoint inequality;
* `sum_powersetCard_exp_le`: Hoeffding's Theorem 4 for `f = exp(λ ·)`, as sums over subsets.

About Mathlib objects only; a candidate for upstreaming.
-/

open Finset
open scoped BigOperators

namespace Real

/-- **The tangent-line bound for `t ↦ t^(k+1)`** at `m`: for `m, t ≥ 0`,
`m^k ((k+1) t − k m) ≤ t^(k+1)` (the tangent at `m` lies below the convex power). -/
theorem pow_mul_sub_le_pow_succ {m t : ℝ} (hm : 0 ≤ m) (ht : 0 ≤ t) (k : ℕ) :
    m ^ k * ((k + 1) * t - k * m) ≤ t ^ (k + 1) := by
  rcases hm.eq_or_lt with rfl | hm
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [zero_pow hk.ne']
      simpa using pow_nonneg ht (k + 1)
  · have hB := one_add_mul_le_pow (a := t / m - 1) (by linarith [div_nonneg ht hm.le]) (k + 1)
    rw [add_sub_cancel, div_pow] at hB
    have hmk : 0 < m ^ (k + 1) := pow_pos hm _
    calc m ^ k * ((k + 1) * t - k * m)
        = m ^ (k + 1) * (1 + ((k + 1 : ℕ) : ℝ) * (t / m - 1)) := by
          push_cast
          field_simp
          ring
      _ ≤ m ^ (k + 1) * (t ^ (k + 1) / m ^ (k + 1)) := mul_le_mul_of_nonneg_left hB hmk.le
      _ = t ^ (k + 1) := by field_simp

end Real

namespace Finset

variable {ι : Type*} [DecidableEq ι]

/-- **The elementary symmetric sum** `∑_{T ⊆ s, #T = k} ∏_{j ∈ T} a_j`: `C(#s, k)` times the
expectation of `∏_{j ∈ T} a_j` for a uniform `k`-subset `T` of `s`. -/
noncomputable def subsetProdSum (s : Finset ι) (a : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ s.powersetCard k, ∏ j ∈ T, a j

omit [DecidableEq ι] in
/-- The empty set has one `0`-subset and no larger ones. -/
theorem subsetProdSum_empty (a : ι → ℝ) (k : ℕ) :
    subsetProdSum ∅ a k = if k = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [subsetProdSum]
  · have he : powersetCard k (∅ : Finset ι) = ∅ := powersetCard_eq_empty.2 (by simpa using hk)
    simp [subsetProdSum, he, hk.ne']

omit [DecidableEq ι] in
/-- Every set has exactly one `0`-subset. -/
@[simp] theorem subsetProdSum_zero (s : Finset ι) (a : ι → ℝ) : subsetProdSum s a 0 = 1 := by
  simp [subsetProdSum]

/-- **Adding one element**: `e_{k+1}(insert x s) = e_{k+1}(s) + a_x · e_k(s)` for `x ∉ s`. -/
theorem subsetProdSum_insert {s : Finset ι} {x : ι} (hx : x ∉ s) (a : ι → ℝ) (k : ℕ) :
    subsetProdSum (insert x s) a (k + 1) = subsetProdSum s a (k + 1) + a x * subsetProdSum s a k := by
  have hdisj : Disjoint (s.powersetCard (k + 1)) ((s.powersetCard k).image (insert x)) := by
    rw [disjoint_left]
    intro T hT hT'
    obtain ⟨U, -, rfl⟩ := mem_image.1 hT'
    exact hx ((mem_powersetCard.1 hT).1 (mem_insert_self x U))
  have hinj : Set.InjOn (insert x) (s.powersetCard k : Set (Finset ι)) := by
    intro U hU V hV hUV
    have hxU : x ∉ U := fun h => hx ((mem_powersetCard.1 hU).1 h)
    have hxV : x ∉ V := fun h => hx ((mem_powersetCard.1 hV).1 h)
    simpa [hxU, hxV] using congrArg (fun W => W.erase x) hUV
  rw [subsetProdSum, powersetCard_succ_insert hx, sum_union hdisj, sum_image hinj,
    subsetProdSum, subsetProdSum, mul_sum]
  congr 1
  refine sum_congr rfl fun U hU => ?_
  rw [prod_insert fun h => hx ((mem_powersetCard.1 hU).1 h)]

omit [DecidableEq ι] in
/-- `subsetProdSum` of nonnegative weights is nonnegative. -/
theorem subsetProdSum_nonneg {s : Finset ι} {a : ι → ℝ} (ha : ∀ j ∈ s, 0 ≤ a j) (k : ℕ) :
    0 ≤ subsetProdSum s a k :=
  sum_nonneg fun _ hT => prod_nonneg fun j hj => ha j ((mem_powersetCard.1 hT).1 hj)

/-- **Maclaurin's endpoint inequality**: for nonnegative `a_j`,
`e_k(a) ≤ C(#s, k) · ((∑_{j ∈ s} a_j) / #s)^k`: the average over `k`-subsets of
`∏_{j ∈ T} a_j` is at most the `k`-th power of the mean. -/
theorem subsetProdSum_le {s : Finset ι} {a : ι → ℝ} (ha : ∀ j ∈ s, 0 ≤ a j) (k : ℕ) :
    subsetProdSum s a k ≤ (s.card.choose k : ℝ) * ((∑ j ∈ s, a j) / s.card) ^ k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rw [subsetProdSum_empty]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simp [hk.ne', Nat.choose_eq_zero_of_lt hk]
  | @insert x s hx ih =>
    have has : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (mem_insert_of_mem hj)
    have hax : 0 ≤ a x := ha x (mem_insert_self x s)
    rcases k with _ | k
    · simp
    rw [subsetProdSum_insert hx, card_insert_of_notMem hx, sum_insert hx]
    set n := s.card
    set S := ∑ j ∈ s, a j
    have hS : 0 ≤ S := sum_nonneg has
    have h1 := ih has (k + 1)
    have h2 := mul_le_mul_of_nonneg_left (ih has k) hax
    refine (add_le_add h1 h2).trans ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn]
      rcases k with _ | k
      · simp [hS]
      · simp
        positivity
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    set m := S / n
    set t := (a x + S) / ((n + 1 : ℕ) : ℝ)
    have hm : 0 ≤ m := div_nonneg hS hnR.le
    have ht : 0 ≤ t := div_nonneg (add_nonneg hax hS) (by positivity)
    have hx' : a x = ((n + 1 : ℕ) : ℝ) * t - n * m := by
      simp only [t, m]
      push_cast
      field_simp
      ring
    have htan := Real.pow_mul_sub_le_pow_succ hm ht k
    by_cases hkn : k ≤ n
    · have hc1 : ((n.choose (k + 1) : ℕ) : ℝ) * (k + 1) = (n.choose k : ℝ) * (n - k) := by
        have := Nat.choose_succ_right_eq n k
        rw [← Nat.cast_sub hkn]
        exact_mod_cast this
      have hc2 : ((n + 1).choose (k + 1) : ℝ) * (k + 1) = (n + 1) * n.choose k := by
        have := Nat.add_one_mul_choose_eq n k
        exact_mod_cast this.symm
      have hk1 : (0 : ℝ) < k + 1 := by positivity
      rw [hx']
      have hck : (0 : ℝ) ≤ n.choose k := by positivity
      rw [← mul_le_mul_iff_of_pos_right hk1]
      have key : (n.choose k : ℝ) * (n + 1) * (m ^ k * ((k + 1) * t - k * m)) ≤
          (n.choose k : ℝ) * (n + 1) * t ^ (k + 1) :=
        mul_le_mul_of_nonneg_left htan (by positivity)
      calc ((n.choose (k + 1) : ℝ) * m ^ (k + 1) +
              (((n + 1 : ℕ) : ℝ) * t - n * m) * ((n.choose k : ℝ) * m ^ k)) * (k + 1)
          = (n.choose k : ℝ) * (n + 1) * (m ^ k * ((k + 1) * t - k * m)) := by
            have : ((n.choose (k + 1) : ℝ) * m ^ (k + 1)) * (k + 1) =
                (n.choose k : ℝ) * (n - k) * m ^ (k + 1) := by rw [← hc1]; ring
            push_cast
            linear_combination this
        _ ≤ (n.choose k : ℝ) * (n + 1) * t ^ (k + 1) := key
        _ = ((n + 1).choose (k + 1) : ℝ) * t ^ (k + 1) * (k + 1) := by
            linear_combination (-(t ^ (k + 1))) * hc2
    · push Not at hkn
      rw [Nat.choose_eq_zero_of_lt hkn, Nat.choose_eq_zero_of_lt (by omega : n < k + 1)]
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
      positivity

/-- **Hoeffding's comparison for `f = exp(λ ·)`** (Hoeffding 1963, Theorem 4, p. 28): the
exponential moment of the sum of a uniform `τ`-subset of the population `x` is at most that of
`τ` draws with replacement, `(mean_j e^{λ x_j})^τ`. Stated with the subset average written as a
sum over `τ`-subsets divided by their number. -/
theorem sum_powersetCard_exp_le (s : Finset ι) (x : ι → ℝ) (lam : ℝ) (τ : ℕ) :
    ∑ T ∈ s.powersetCard τ, Real.exp (lam * ∑ j ∈ T, x j) ≤
      (s.card.choose τ : ℝ) * ((∑ j ∈ s, Real.exp (lam * x j)) / s.card) ^ τ := by
  refine le_of_eq_of_le ?_ (subsetProdSum_le (a := fun j => Real.exp (lam * x j))
    (fun j _ => (Real.exp_pos _).le) τ)
  refine sum_congr rfl fun T _ => ?_
  rw [mul_sum, Real.exp_sum]

end Finset
