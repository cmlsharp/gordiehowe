-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.RademacherAbs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# Rademacher sums: the cosh chord and the convex comparison

For independent uniform signs `ε_i` (`ε : ι → Bool`, the sign `±a_i` is `a_i` if `ε i` and
`-a_i` otherwise):

* `Real.cosh_mul_le_one_add_mul_sq`: the chord bound `cosh(u a) ≤ 1 + (cosh u - 1) a²` for
  `|a| ≤ 1`, termwise on the power series `cosh y = ∑_k y^(2k)/(2k)!` (`a^(2k) ≤ a²` for
  `k ≥ 1`). It bounds the moment generating function of one Rademacher term `ε a` by an affine
  function of `a²`.
* `Real.add_map_add_le_of_abs_le`: for convex `g`, `g(x + a) + g(x - a) ≤ g(x + b) + g(x - b)`
  when `|a| ≤ |b|`: the even convex function `a ↦ g(x + a) + g(x - a)` is nondecreasing in `|a|`.
* `Real.two_mul_sum_bool_eq`: averaging over the flip of one sign.
* `Real.sum_bool_convex_le`: **the convex comparison** `∑_ε g(∑_i ±a_i) ≤ ∑_ε g(∑_i ±b_i)` for
  convex `g` and `|a_i| ≤ |b_i|`, by replacing one coordinate at a time. With `b` the indicator
  of a set `s` and `|a_i| ≤ 1` on `s`, the right side is the simple random walk with `#s` steps.
* `Real.expect_bool_sum_mask`: the law of that walk,
  `𝔼_ε g(x + ∑_{i ∈ s} ±1) = 2^(-#s) ∑_{k ≤ #s} C(#s, k) g(x + k - (#s - k))` (Pascal's rule,
  `Finset.sum_choose_succ_mul`).
* `Real.convexOn_hinge`: the hinge `y ↦ max(|y| - θ, 0)` is convex.

About Mathlib objects only; a candidate for upstreaming.
-/

open Finset
open scoped BigOperators

namespace Real

/-! ### The cosh chord -/

/-- **The chord bound for `cosh`**: for every `u` and `|a| ≤ 1`,
`cosh(u a) ≤ 1 + (cosh u - 1) a²`. Termwise on `cosh y = ∑_k y^(2k)/(2k)!`: the `k = 0` terms
agree and `(u a)^(2k) = u^(2k) (a²)^k ≤ u^(2k) a²` for `k ≥ 1`. -/
theorem cosh_mul_le_one_add_mul_sq (u : ℝ) {a : ℝ} (ha : |a| ≤ 1) :
    cosh (u * a) ≤ 1 + (cosh u - 1) * a ^ 2 := by
  have ha0 : 0 ≤ a ^ 2 := sq_nonneg a
  have ha1 : a ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg a]
  have h2 : HasSum (fun k : ℕ => (if k = 0 then 1 - a ^ 2 else 0) +
      a ^ 2 * (u ^ (2 * k) / ((2 * k).factorial : ℝ))) ((1 - a ^ 2) + a ^ 2 * cosh u) :=
    (hasSum_ite_eq 0 (1 - a ^ 2)).add ((hasSum_cosh u).mul_left (a ^ 2))
  have key := hasSum_le (fun k => ?_) (hasSum_cosh (u * a)) h2
  · linarith
  · rcases k with _ | k
    · simp
    · have hF : (0 : ℝ) < ((2 * (k + 1)).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hu : (u * a) ^ (2 * (k + 1)) = (a ^ 2) ^ (k + 1) * (u ^ 2) ^ (k + 1) := by ring
      have hu' : u ^ (2 * (k + 1)) = (u ^ 2) ^ (k + 1) := by ring
      simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
      rw [hu, hu', mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (pow_le_of_le_one ha0 ha1 (Nat.succ_ne_zero k))
        (div_nonneg (by positivity) hF.le)

/-! ### Two points of a convex function -/

/-- **An even convex function of the shift is monotone in its absolute value**: for convex `g`
and `|a| ≤ |b|`, `g(x + a) + g(x - a) ≤ g(x + b) + g(x - b)`. Both `x ± a` are convex
combinations of `x ± b`, with swapped weights. -/
theorem add_map_add_le_of_abs_le {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) (x : ℝ) {a b : ℝ}
    (hab : |a| ≤ |b|) : g (x + a) + g (x - a) ≤ g (x + b) + g (x - b) := by
  have hb : g (x + b) + g (x - b) = g (x + |b|) + g (x - |b|) := by
    rcases abs_choice b with h | h <;> rw [h]
    rw [sub_neg_eq_add, ← sub_eq_add_neg, add_comm]
  rw [hb]
  set c := |b| with hc
  have hc0 : 0 ≤ c := abs_nonneg b
  rcases hc0.eq_or_lt with h0 | hpos
  · have : a = 0 := abs_eq_zero.1 (le_antisymm (h0 ▸ hab) (abs_nonneg a))
    rw [this, ← h0]
  have ha := abs_le.1 hab
  set μ := (c + a) / (2 * c) with hμ
  have hμ0 : 0 ≤ μ := div_nonneg (by linarith) (by linarith)
  have hμ1 : 0 ≤ 1 - μ := by
    rw [hμ, sub_nonneg, div_le_one (by linarith)]
    linarith
  have h1 := hg.2 (Set.mem_univ (x + c)) (Set.mem_univ (x - c)) hμ0 hμ1 (by ring)
  have h2 := hg.2 (Set.mem_univ (x + c)) (Set.mem_univ (x - c)) hμ1 hμ0 (by ring)
  have e1 : μ • (x + c) + (1 - μ) • (x - c) = x + a := by
    simp only [smul_eq_mul, hμ]
    field_simp
    ring
  have e2 : (1 - μ) • (x + c) + μ • (x - c) = x - a := by
    simp only [smul_eq_mul, hμ]
    field_simp
    ring
  rw [e1] at h1
  rw [e2] at h2
  simp only [smul_eq_mul] at h1 h2
  linarith

/-! ### The convex comparison -/

section Signs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Averaging over the flip of one sign**: `2 ∑_ε F ε = ∑_ε (F ε + F ε')`, with `ε'` the sign
vector `ε` flipped at `j`. -/
theorem two_mul_sum_bool_eq (j : ι) (F : (ι → Bool) → ℝ) :
    2 * ∑ ε : ι → Bool, F ε = ∑ ε : ι → Bool, (F ε + F (Function.update ε j (!ε j))) := by
  rw [sum_add_distrib, two_mul]
  congr 1
  exact (Fintype.sum_equiv (Function.Involutive.toPerm _ (bool_update_not_involutive j)) _ _
    fun _ => rfl).symm

/-- A Rademacher sum split at one coordinate: `∑_i ±c_i = ±c_j + ∑_{i ≠ j} ±c_i`. -/
theorem sum_bool_sign_eq (c : ι → ℝ) (ε : ι → Bool) (j : ι) :
    (∑ i, if ε i then c i else -c i) =
      (if ε j then c j else -c j) + ∑ i ∈ univ.erase j, if ε i then c i else -c i :=
  (add_sum_erase _ _ (mem_univ j)).symm

/-- **Replacing one weight by a larger one**: for convex `g` and `|a| ≤ |b|`,
`∑_ε g(∑_i ±c_i) ≤ ∑_ε g(∑_i ±c'_i)` with `c = c[j ↦ a]` and `c' = c[j ↦ b]`. -/
theorem sum_bool_convex_le_update {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) (c : ι → ℝ) (j : ι)
    {a b : ℝ} (hab : |a| ≤ |b|) :
    ∑ ε : ι → Bool, g (∑ i, if ε i then Function.update c j a i else -Function.update c j a i) ≤
      ∑ ε : ι → Bool, g (∑ i, if ε i then Function.update c j b i else
        -Function.update c j b i) := by
  set X : (ι → Bool) → ℝ := fun ε => ∑ i ∈ univ.erase j, if ε i then c i else -c i with hX
  have hsplit : ∀ (v : ℝ) (ε : ι → Bool),
      (∑ i, if ε i then Function.update c j v i else -Function.update c j v i) =
        (if ε j then v else -v) + X ε := fun v ε => by
    rw [sum_bool_sign_eq _ ε j, Function.update_self]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hi)]
  have hXflip : ∀ ε : ι → Bool, X (Function.update ε j (!ε j)) = X ε := fun ε =>
    sum_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]
  have hpair : ∀ (v : ℝ) (ε : ι → Bool),
      g (∑ i, if ε i then Function.update c j v i else -Function.update c j v i) +
        g (∑ i, if Function.update ε j (!ε j) i then Function.update c j v i else
          -Function.update c j v i) =
        g (X ε + v) + g (X ε - v) := fun v ε => by
    rw [hsplit, hsplit, hXflip, Function.update_self]
    cases ε j
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [add_comm (g _) (g _)]
      congr 1 <;> ring_nf
    · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true]
      congr 1 <;> ring_nf
  have h := sum_le_sum fun ε (_ : ε ∈ (univ : Finset (ι → Bool))) =>
    add_map_add_le_of_abs_le hg (X ε) hab
  have ha := two_mul_sum_bool_eq j fun ε =>
    g (∑ i, if ε i then Function.update c j a i else -Function.update c j a i)
  have hb := two_mul_sum_bool_eq j fun ε =>
    g (∑ i, if ε i then Function.update c j b i else -Function.update c j b i)
  simp only [hpair] at ha hb
  linarith

/-- **The convex comparison for Rademacher sums**: for convex `g` and weights with
`|a_i| ≤ |b_i|`, `∑_ε g(∑_i ±a_i) ≤ ∑_ε g(∑_i ±b_i)`. -/
theorem sum_bool_convex_le {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) {a b : ι → ℝ}
    (hab : ∀ i, |a i| ≤ |b i|) :
    ∑ ε : ι → Bool, g (∑ i, if ε i then a i else -a i) ≤
      ∑ ε : ι → Bool, g (∑ i, if ε i then b i else -b i) := by
  set w : Finset ι → ι → ℝ := fun T i => if i ∈ T then b i else a i with hw
  have hstep : ∀ T : Finset ι, ∑ ε : ι → Bool, g (∑ i, if ε i then a i else -a i) ≤
      ∑ ε : ι → Bool, g (∑ i, if ε i then w T i else -w T i) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [hw]
    | @insert j T hj ih =>
      have hwj : w T j = a j := by simp [hw, hj]
      have h1 : w T = Function.update (w T) j (a j) := by
        rw [← hwj, Function.update_eq_self]
      have h2 : w (insert j T) = Function.update (w T) j (b j) := by
        funext i
        by_cases hij : i = j
        · subst hij; simp [hw]
        · rw [Function.update_of_ne hij]
          simp [hw, hij]
      refine ih.trans ?_
      rw [h2]
      conv_lhs => rw [h1]
      exact sum_bool_convex_le_update hg (w T) j (hab j)
  have := hstep univ
  simpa [hw] using this

/-- **The law of the simple random walk**: for every `g`, `x` and `s`,
`𝔼_ε g(x + ∑_{i ∈ s} ±1) = 2^(-#s) ∑_{k ≤ #s} C(#s, k) g(x + k - (#s - k))`. -/
theorem expect_bool_sum_mask (g : ℝ → ℝ) (s : Finset ι) (x : ℝ) :
    𝔼 ε : ι → Bool, g (x + ∑ i ∈ s, if ε i then (1 : ℝ) else -1) =
      (∑ k ∈ range (#s + 1), ((#s).choose k : ℝ) * g (x + k - ((#s - k : ℕ) : ℝ))) / 2 ^ #s := by
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | @insert j s hj ih =>
    rw [card_insert_of_notMem hj]
    set m := #s
    have hflip : ∀ ε : ι → Bool,
        g (x + ∑ i ∈ insert j s, if ε i then (1 : ℝ) else -1) +
          g (x + ∑ i ∈ insert j s, if Function.update ε j (!ε j) i then (1 : ℝ) else -1) =
        g (x + 1 + ∑ i ∈ s, if ε i then (1 : ℝ) else -1) +
          g (x - 1 + ∑ i ∈ s, if ε i then (1 : ℝ) else -1) := fun ε => by
      have hs : ∑ i ∈ s, (if Function.update ε j (!ε j) i then (1 : ℝ) else -1) =
          ∑ i ∈ s, if ε i then (1 : ℝ) else -1 :=
        sum_congr rfl fun i hi => by rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
      rw [sum_insert hj, sum_insert hj, hs, Function.update_self]
      cases ε j
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
        rw [add_comm (g _) (g _)]
        congr 2 <;> ring
      · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true]
        congr 2 <;> ring
    have h2 := two_mul_sum_bool_eq j fun ε =>
      g (x + ∑ i ∈ insert j s, if ε i then (1 : ℝ) else -1)
    simp only [hflip, sum_add_distrib] at h2
    have hcard : ((Fintype.card (ι → Bool) : ℕ) : ℝ) = 2 ^ Fintype.card ι := by
      simp [Fintype.card_bool]
    have hp := ih (x + 1)
    have hm := ih (x - 1)
    rw [Fintype.expect_eq_sum_div_card, hcard] at hp hm ⊢
    have hP : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
    have hpas := sum_choose_succ_mul (R := ℝ)
      (fun i j => g (x + (i : ℝ) - (j : ℝ))) m
    have hA : ∑ i ∈ range (m + 1), (m.choose i : ℝ) * g (x + (i : ℝ) - ((m + 1 - i : ℕ) : ℝ)) =
        ∑ k ∈ range (m + 1), (m.choose k : ℝ) * g (x - 1 + k - ((m - k : ℕ) : ℝ)) :=
      sum_congr rfl fun i hi => by
        have : i ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hi)
        rw [Nat.sub_add_comm this]
        push_cast
        ring_nf
    have hB : ∑ i ∈ range (m + 1),
        (m.choose i : ℝ) * g (x + ((i + 1 : ℕ) : ℝ) - ((m - i : ℕ) : ℝ)) =
        ∑ k ∈ range (m + 1), (m.choose k : ℝ) * g (x + 1 + k - ((m - k : ℕ) : ℝ)) :=
      sum_congr rfl fun i _ => by
        push_cast
        ring_nf
    rw [hA, hB] at hpas
    have hQ : (0 : ℝ) < 2 ^ m := by positivity
    rw [div_eq_div_iff hP.ne' hQ.ne'] at hp hm
    rw [div_eq_div_iff hP.ne' (by positivity), hpas, pow_succ]
    linear_combination (2 ^ m) * h2 + hp + hm

end Signs

/-! ### The hinge -/

/-- **The hinge `y ↦ max(|y| - θ, 0)` is convex**. -/
theorem convexOn_hinge (θ : ℝ) : ConvexOn ℝ Set.univ fun y : ℝ => max (|y| - θ) 0 := by
  have h := ((convexOn_norm convex_univ).add_const (-θ)).sup
    (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set ℝ)))
  refine h.congr fun y _ => ?_
  simp [Real.norm_eq_abs, sub_eq_add_neg]

end Real
