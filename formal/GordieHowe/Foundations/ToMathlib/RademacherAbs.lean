-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Fintype.Pi

@[expose] public section

/-!
# The first absolute moment of a Rademacher sum

For independent uniform signs `ε_i` and real weights `|a_i| ≤ 1`, the first absolute moment
`𝔼 |∑_i ε_i a_i|` is bounded by a concave function of the variance `u = ∑_i a_i²`, sharper than
`√u` (Cauchy–Schwarz) for `u` of order `1` to `10`.

* `Real.abs_le_majorant`: the majorant `|x| ≤ A + B x² - C cos(t x)` for every real `x`, with
  `A = 183/100`, `B = 104/1000`, `C = 77/100`, `t = 65/100`. Even in `x`; `cos ≤ 1` for
  `x ≤ 1` and `x ≥ 9`; on `[1, 4]` the bound `cos y = 1 - 2 sin²(y/2)` with
  `sin v ≥ v - v³/6`; on `[4, 9]` the bound `cos y = -cos(y - π)`, `cos z = 2 cos²(z/2) - 1` with
  `cos w ≥ 1 - w²/2`, and `3.1415 < π < 3.1416`. Each interval closes by a Bernstein-basis
  certificate (`linarith` over the products `(x - a)^k (b - x)^(n-k)`).
* `Real.exp_neg_le_cos`: `exp(-(11/20) y²) ≤ cos y` for `|y| ≤ 65/100`, that is
  `log cos y ≥ -g y²/2` with `g = 11/10`.
* `Real.sum_bool_cos_sum`: `∑_ε cos(∑_i f_i(ε_i)) = 2^|ι| ∏_i cos(f_i(true))` when
  `f_i(false) = -f_i(true)` (the characteristic function of independent signs).
* `Real.sum_bool_sq_sum`: `∑_ε (∑_i ±a_i)² = 2^|ι| ∑_i a_i²`.
* `Real.absMomentBound u = A + B u - C exp(-κ u)` with `κ = (11/20)(65/100)²`;
  `Real.concaveOn_absMomentBound`, `Real.monotone_absMomentBound`,
  `Real.expect_absMomentBound_le` (Jensen's inequality for a uniform average).
* `Real.expect_abs_le_absMomentBound`: for any random variable `X` with `𝔼 X² = u` and
  `𝔼 cos(t X) ≥ exp(-κ u)`, `𝔼 |X| ≤ absMomentBound u`.
* `Real.expect_abs_rademacher_le`: `𝔼_ε |∑_i ±a_i| ≤ absMomentBound (∑_i a_i²)` for `|a_i| ≤ 1`.
-/

open Finset
open scoped BigOperators

namespace Real

/-! ### Polynomial bounds for `cos` -/

/-- **The double-angle lower bound**: `2 (1 - y²/8)² - 1 ≤ cos y` for `y² ≤ 8`, from
`cos y = 2 cos²(y/2) - 1` and `cos(y/2) ≥ 1 - y²/8 ≥ 0`. -/
theorem two_mul_one_sub_sq_div_eight_sq_sub_one_le_cos {y : ℝ} (hy : y ^ 2 ≤ 8) :
    2 * (1 - y ^ 2 / 8) ^ 2 - 1 ≤ cos y := by
  have hc : 1 - y ^ 2 / 8 ≤ cos (y / 2) := by
    have := one_sub_sq_div_two_le_cos (x := y / 2)
    linarith [show (y / 2) ^ 2 / 2 = y ^ 2 / 8 by ring]
  have h0 : 0 ≤ 1 - y ^ 2 / 8 := by linarith
  have hsq : (1 - y ^ 2 / 8) ^ 2 ≤ cos (y / 2) ^ 2 := pow_le_pow_left₀ h0 hc 2
  have hd : cos y = 2 * cos (y / 2) ^ 2 - 1 := by
    rw [← cos_two_mul]; ring_nf
  linarith

/-- **The half-angle upper bound**: `cos y ≤ 1 - 2 (y/2 - (y/2)³/6)²` for `0 ≤ y ≤ 4`, from
`cos y = 1 - 2 sin²(y/2)` and `sin v ≥ v - v³/6 ≥ 0` for `0 ≤ v ≤ 2`. -/
theorem cos_le_one_sub_two_mul_sq_of_le_four {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 4) :
    cos y ≤ 1 - 2 * (y / 2 - (y / 2) ^ 3 / 6) ^ 2 := by
  have hs := sin_ge_sub_cube (x := y / 2) (by linarith)
  have hv0 : 0 ≤ y / 2 := by linarith
  have hv4 : (y / 2) ^ 2 ≤ 4 := by nlinarith
  have h0 : 0 ≤ y / 2 - (y / 2) ^ 3 / 6 := by
    have : y / 2 - (y / 2) ^ 3 / 6 = y / 2 * (1 - (y / 2) ^ 2 / 6) := by ring
    rw [this]
    exact mul_nonneg hv0 (by linarith)
  have hsq : (y / 2 - (y / 2) ^ 3 / 6) ^ 2 ≤ sin (y / 2) ^ 2 := pow_le_pow_left₀ h0 hs 2
  have hd : cos y = 1 - 2 * sin (y / 2) ^ 2 := by
    have := cos_sq' (y / 2)
    have h2 := cos_two_mul (y / 2)
    rw [show 2 * (y / 2) = y by ring] at h2
    linarith
  linarith

/-- **The upper bound near `π`**: if `(y - π)² ≤ W ≤ 8` then `cos y ≤ 1 - 2 (1 - W/8)²`, from
`cos y = -cos(y - π)` and `two_mul_one_sub_sq_div_eight_sq_sub_one_le_cos`. -/
theorem cos_le_of_sq_sub_pi_le {y W : ℝ} (hW : (y - π) ^ 2 ≤ W) (hW8 : W ≤ 8) :
    cos y ≤ 1 - 2 * (1 - W / 8) ^ 2 := by
  have h := two_mul_one_sub_sq_div_eight_sq_sub_one_le_cos (hW.trans hW8)
  rw [cos_sub_pi] at h
  have h0 : 0 ≤ 1 - W / 8 := by linarith
  have hsq : (1 - W / 8) ^ 2 ≤ (1 - (y - π) ^ 2 / 8) ^ 2 :=
    pow_le_pow_left₀ h0 (by linarith) 2
  linarith

/-- The majorant on `[0, 1]` and on `[9, ∞)`, where `cos ≤ 1` suffices. -/
private theorem majorant_of_cos_le_one {x : ℝ} (hx : x ≤ 1 ∨ 9 ≤ x) :
    x ≤ 183 / 100 + 104 / 1000 * x ^ 2 - 77 / 100 * cos (65 / 100 * x) := by
  have hc := cos_le_one (65 / 100 * x)
  rcases hx with hx | hx <;> nlinarith

/-- The polynomial majorant on `[1, 4]`, by Bernstein certificates on `[1, 5/2]` and `[5/2, 4]`. -/
private theorem majorant_poly_one_four {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 4) :
    x ≤ 183 / 100 + 104 / 1000 * x ^ 2 -
      77 / 100 * (1 - 2 * (13 * x / 40 - (13 * x / 40) ^ 3 / 6) ^ 2) := by
  rcases le_total x (5 / 2) with h | h
  · have ha : 0 ≤ x - 1 := by linarith
    have hb : 0 ≤ 5 / 2 - x := by linarith
    linarith [mul_nonneg (pow_nonneg ha 0) (pow_nonneg hb 6),
      mul_nonneg (pow_nonneg ha 1) (pow_nonneg hb 5),
      mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb 4),
      mul_nonneg (pow_nonneg ha 3) (pow_nonneg hb 3),
      mul_nonneg (pow_nonneg ha 4) (pow_nonneg hb 2),
      mul_nonneg (pow_nonneg ha 5) (pow_nonneg hb 1),
      mul_nonneg (pow_nonneg ha 6) (pow_nonneg hb 0)]
  · have ha : 0 ≤ x - 5 / 2 := by linarith
    have hb : 0 ≤ 4 - x := by linarith
    linarith [mul_nonneg (pow_nonneg ha 0) (pow_nonneg hb 6),
      mul_nonneg (pow_nonneg ha 1) (pow_nonneg hb 5),
      mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb 4),
      mul_nonneg (pow_nonneg ha 3) (pow_nonneg hb 3),
      mul_nonneg (pow_nonneg ha 4) (pow_nonneg hb 2),
      mul_nonneg (pow_nonneg ha 5) (pow_nonneg hb 1),
      mul_nonneg (pow_nonneg ha 6) (pow_nonneg hb 0)]

/-- The polynomial majorant of degree `4` on an interval `[a, b]`, from its Bernstein
certificate. -/
private theorem majorant_poly_four_nine_of {a b x : ℝ} (h1 : a ≤ x) (h2 : x ≤ b)
    (hcert : ∀ x, 0 ≤ x - a → 0 ≤ b - x →
      x ≤ 183 / 100 + 104 / 1000 * x ^ 2 -
        77 / 100 * (1 - 2 * (1 - ((13 * x / 20 - 314155 / 100000) ^ 2 + 3 / 10000) / 8) ^ 2)) :
    x ≤ 183 / 100 + 104 / 1000 * x ^ 2 -
      77 / 100 * (1 - 2 * (1 - ((13 * x / 20 - 314155 / 100000) ^ 2 + 3 / 10000) / 8) ^ 2) :=
  hcert x (by linarith) (by linarith)

/-- The polynomial majorant on `[4, 9]`, by Bernstein certificates on `[4, 13/2]`,
`[13/2, 57/8]`, `[57/8, 31/4]` and `[31/4, 9]`. -/
private theorem majorant_poly_four_nine {x : ℝ} (h1 : 4 ≤ x) (h2 : x ≤ 9) :
    x ≤ 183 / 100 + 104 / 1000 * x ^ 2 -
      77 / 100 * (1 - 2 * (1 - ((13 * x / 20 - 314155 / 100000) ^ 2 + 3 / 10000) / 8) ^ 2) := by
  rcases le_total x (13 / 2) with h | h
  · refine majorant_poly_four_nine_of h1 h fun x ha hb => ?_
    linarith [mul_nonneg (pow_nonneg ha 0) (pow_nonneg hb 4),
      mul_nonneg (pow_nonneg ha 1) (pow_nonneg hb 3),
      mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb 2),
      mul_nonneg (pow_nonneg ha 3) (pow_nonneg hb 1),
      mul_nonneg (pow_nonneg ha 4) (pow_nonneg hb 0)]
  rcases le_total x (57 / 8) with h' | h'
  · refine majorant_poly_four_nine_of h h' fun x ha hb => ?_
    linarith [mul_nonneg (pow_nonneg ha 0) (pow_nonneg hb 4),
      mul_nonneg (pow_nonneg ha 1) (pow_nonneg hb 3),
      mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb 2),
      mul_nonneg (pow_nonneg ha 3) (pow_nonneg hb 1),
      mul_nonneg (pow_nonneg ha 4) (pow_nonneg hb 0)]
  rcases le_total x (31 / 4) with h'' | h''
  · refine majorant_poly_four_nine_of h' h'' fun x ha hb => ?_
    linarith [mul_nonneg (pow_nonneg ha 0) (pow_nonneg hb 4),
      mul_nonneg (pow_nonneg ha 1) (pow_nonneg hb 3),
      mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb 2),
      mul_nonneg (pow_nonneg ha 3) (pow_nonneg hb 1),
      mul_nonneg (pow_nonneg ha 4) (pow_nonneg hb 0)]
  · refine majorant_poly_four_nine_of h'' h2 fun x ha hb => ?_
    linarith [mul_nonneg (pow_nonneg ha 0) (pow_nonneg hb 4),
      mul_nonneg (pow_nonneg ha 1) (pow_nonneg hb 3),
      mul_nonneg (pow_nonneg ha 2) (pow_nonneg hb 2),
      mul_nonneg (pow_nonneg ha 3) (pow_nonneg hb 1),
      mul_nonneg (pow_nonneg ha 4) (pow_nonneg hb 0)]

/-- The majorant with `x` in place of `|x|`. -/
private theorem majorant_self (x : ℝ) :
    x ≤ 183 / 100 + 104 / 1000 * x ^ 2 - 77 / 100 * cos (65 / 100 * x) := by
  rcases le_or_gt x 1 with h1 | h1
  · exact majorant_of_cos_le_one (Or.inl h1)
  rcases le_or_gt x 4 with h4 | h4
  · have hc := cos_le_one_sub_two_mul_sq_of_le_four (y := 65 / 100 * x) (by linarith)
      (by linarith)
    have hp := majorant_poly_one_four h1.le h4
    have he : 65 / 100 * x / 2 = 13 * x / 40 := by ring
    rw [he] at hc
    linarith
  rcases le_or_gt x 9 with h9 | h9
  · have hpi1 := pi_gt_d4
    have hpi2 := pi_lt_d4
    have hW : (65 / 100 * x - π) ^ 2 ≤ (13 * x / 20 - 314155 / 100000) ^ 2 + 3 / 10000 := by
      nlinarith [mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hpi2.le),
        mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hpi1.le),
        mul_nonneg (sub_nonneg.2 h4.le) (sub_nonneg.2 hpi2.le),
        mul_nonneg (sub_nonneg.2 h4.le) (sub_nonneg.2 hpi1.le)]
    have hW8 : (13 * x / 20 - 314155 / 100000) ^ 2 + 3 / 10000 ≤ 8 := by nlinarith
    have hc := cos_le_of_sq_sub_pi_le hW hW8
    have hp := majorant_poly_four_nine h4.le h9
    linarith
  · exact majorant_of_cos_le_one (Or.inr h9.le)

/-- **The majorant of `|x|`**: `|x| ≤ 183/100 + (104/1000) x² - (77/100) cos((65/100) x)` for
every real `x`. -/
theorem abs_le_majorant (x : ℝ) :
    |x| ≤ 183 / 100 + 104 / 1000 * x ^ 2 - 77 / 100 * cos (65 / 100 * x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact majorant_self x
  · rw [abs_of_nonpos hx]
    have h := majorant_self (-x)
    rwa [neg_sq, mul_neg, cos_neg] at h

/-- **A Gaussian lower bound for `cos`**: `exp(-(11/20) y²) ≤ cos y` for `|y| ≤ 65/100`, so
`log cos y ≥ -g y²/2` with `g = 11/10`. From `cos y ≥ 1 - y²/2 + y⁴/32`
(`two_mul_one_sub_sq_div_eight_sq_sub_one_le_cos`), `exp v ≥ 1 + v + v²/2 + v³/6`, and a Bernstein
certificate in `w = y²` on `[0, (65/100)²]`. -/
theorem exp_neg_le_cos {y : ℝ} (hy : |y| ≤ 65 / 100) : exp (-(11 / 20 * y ^ 2)) ≤ cos y := by
  set w := y ^ 2 with hw
  have hw0 : 0 ≤ w := sq_nonneg y
  have hw1 : w ≤ 169 / 400 := by
    have := sq_le_sq' (abs_le.1 hy).1 (abs_le.1 hy).2
    rw [hw]; nlinarith
  have hc := two_mul_one_sub_sq_div_eight_sq_sub_one_le_cos (y := y) (by linarith)
  set v := 11 / 20 * w with hv
  have hv0 : 0 ≤ v := by positivity
  have he : 1 + v + v ^ 2 / 2 + v ^ 3 / 6 ≤ exp v := by
    have := sum_le_exp_of_nonneg hv0 4
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at this
    norm_num at this
    linarith
  have hb : 0 ≤ 169 / 400 - w := by linarith
  have hpoly : 1 ≤ (2 * (1 - w / 8) ^ 2 - 1) * (1 + v + v ^ 2 / 2 + v ^ 3 / 6) := by
    rw [hv]
    linarith [mul_nonneg (pow_nonneg hw0 0) (pow_nonneg hb 5),
      mul_nonneg (pow_nonneg hw0 1) (pow_nonneg hb 4),
      mul_nonneg (pow_nonneg hw0 2) (pow_nonneg hb 3),
      mul_nonneg (pow_nonneg hw0 3) (pow_nonneg hb 2),
      mul_nonneg (pow_nonneg hw0 4) (pow_nonneg hb 1),
      mul_nonneg (pow_nonneg hw0 5) (pow_nonneg hb 0)]
  have hL0 : 0 ≤ 2 * (1 - w / 8) ^ 2 - 1 := by nlinarith
  have hP0 : 0 ≤ 1 + v + v ^ 2 / 2 + v ^ 3 / 6 := by positivity
  have h1 : 1 ≤ cos y * exp v :=
    hpoly.trans (mul_le_mul hc he hP0 (hL0.trans hc))
  rw [exp_neg, inv_eq_one_div, div_le_iff₀ (exp_pos v)]
  linarith

/-! ### Sums over independent signs -/

section Signs

/-- Flipping the sign at `i` is an involution of the sign vectors. -/
theorem bool_update_not_involutive {ι : Type*} [DecidableEq ι] (i : ι) :
    Function.Involutive fun ε : ι → Bool => Function.update ε i (!ε i) := fun ε => by
  funext j
  by_cases hji : j = i
  · subst hji; simp
  · simp [Function.update_of_ne hji]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The characteristic function of independent signs**: if `f i false = -f i true` for every
`i`, then `∑_ε cos(∑_i f i (ε i)) = 2^|ι| ∏_i cos(f i true)`. -/
theorem sum_bool_cos_sum (f : ι → Bool → ℝ) (hf : ∀ i, f i false = -f i true) :
    ∑ ε : ι → Bool, cos (∑ i, f i (ε i)) = 2 ^ Fintype.card ι * ∏ i, cos (f i true) := by
  have hre : ∀ ε : ι → Bool, cos (∑ i, f i (ε i)) =
      (∏ i, Complex.exp ((f i (ε i) : ℂ) * Complex.I)).re := fun ε => by
    rw [← Complex.exp_sum, ← Finset.sum_mul, ← Complex.ofReal_sum, Complex.exp_ofReal_mul_I_re]
  simp_rw [hre]
  rw [← Complex.re_sum, ← Fintype.prod_sum (fun i b => Complex.exp ((f i b : ℂ) * Complex.I))]
  have hi : ∀ i, ∑ b : Bool, Complex.exp ((f i b : ℂ) * Complex.I) =
      ((2 * cos (f i true) : ℝ) : ℂ) := fun i => by
    rw [Fintype.sum_bool, hf]
    push_cast
    rw [Complex.two_cos, neg_mul]
  simp_rw [hi]
  rw [← Complex.ofReal_prod, Complex.ofReal_re, prod_mul_distrib, prod_const, card_univ]

/-- **The variance of a Rademacher sum**: `∑_ε (∑_i ±a_i)² = 2^|ι| ∑_i a_i²`, with `±a_i = a_i`
if `ε i` and `-a_i` otherwise. -/
theorem sum_bool_sq_sum (a : ι → ℝ) :
    ∑ ε : ι → Bool, (∑ i, if ε i then a i else -a i) ^ 2 =
      2 ^ Fintype.card ι * ∑ i, a i ^ 2 := by
  set s : (ι → Bool) → ι → ℝ := fun ε i => if ε i then a i else -a i with hs
  change ∑ ε : ι → Bool, (∑ i, s ε i) ^ 2 = _
  have hmul : ∀ i j, ∑ ε : ι → Bool, s ε i * s ε j =
      if i = j then 2 ^ Fintype.card ι * a j ^ 2 else 0 := fun i j => by
    by_cases hij : i = j
    · subst hij
      have : ∀ ε, s ε i * s ε i = a i ^ 2 := fun ε => by
        simp only [hs]; split_ifs <;> ring
      simp only [this, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul,
        ↓reduceIte]
      push_cast; ring
    · simp only [hij, ↓reduceIte]
      have hflip := Fintype.sum_equiv
        (Function.Involutive.toPerm _ (bool_update_not_involutive i)) (fun ε => s ε i * s ε j)
        (fun ε => -(s ε i * s ε j)) fun ε => by
          simp only [Function.Involutive.coe_toPerm, hs, Function.update_self,
            Function.update_of_ne (Ne.symm hij)]
          cases ε i <;> cases ε j <;> simp
      rw [sum_neg_distrib] at hflip
      linarith
  have hexp : ∀ ε, (∑ i, s ε i) ^ 2 = ∑ i, ∑ j, s ε i * s ε j := fun ε => by
    rw [sq, sum_mul_sum]
  simp_rw [hexp]
  rw [sum_comm]
  have hcomm : ∀ i, ∑ ε : ι → Bool, ∑ j, s ε i * s ε j = ∑ j, ∑ ε : ι → Bool, s ε i * s ε j :=
    fun i => sum_comm
  rw [sum_congr rfl fun i _ => hcomm i, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp_rw [hmul]
  rw [sum_ite_eq]
  simp

end Signs

/-! ### The bound function -/

/-- **The first-moment bound** `h(u) = A + B u - C exp(-κ u)` with `A = 183/100`, `B = 104/1000`,
`C = 77/100` and `κ = g t²/2 = (11/20)(65/100)²` (`g = 11/10`, `t = 65/100`). -/
noncomputable def absMomentBound (u : ℝ) : ℝ :=
  183 / 100 + 104 / 1000 * u - 77 / 100 * exp (-(11 / 20 * (65 / 100) ^ 2 * u))

/-- The tangent-line bound for the exponential term: `exp(-κ m) (1 - κ (u - m)) ≤ exp(-κ u)`. -/
private theorem exp_neg_tangent_le (m u : ℝ) :
    exp (-(11 / 20 * (65 / 100) ^ 2 * m)) * (1 - 11 / 20 * (65 / 100) ^ 2 * (u - m)) ≤
      exp (-(11 / 20 * (65 / 100) ^ 2 * u)) := by
  have h1 := add_one_le_exp (-(11 / 20 * (65 / 100) ^ 2 * (u - m)))
  have h2 : exp (-(11 / 20 * (65 / 100) ^ 2 * m)) *
      exp (-(11 / 20 * (65 / 100) ^ 2 * (u - m))) = exp (-(11 / 20 * (65 / 100) ^ 2 * u)) := by
    rw [← exp_add]; ring_nf
  have hp := exp_pos (-(11 / 20 * (65 / 100) ^ 2 * m))
  nlinarith

/-- **`h` is concave** (on all of `ℝ`, in particular on `[0, ∞)`): an affine function minus a
positive multiple of a convex one. -/
theorem concaveOn_absMomentBound : ConcaveOn ℝ Set.univ absMomentBound := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [absMomentBound, smul_eq_mul]
  have hx := mul_le_mul_of_nonneg_left (exp_neg_tangent_le (a * x + b * y) x) ha
  have hy := mul_le_mul_of_nonneg_left (exp_neg_tangent_le (a * x + b * y) y) hb
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hz : a * (exp (-(11 / 20 * (65 / 100) ^ 2 * (a * x + (1 - a) * y))) *
      (1 - 11 / 20 * (65 / 100) ^ 2 * (x - (a * x + (1 - a) * y)))) +
      (1 - a) * (exp (-(11 / 20 * (65 / 100) ^ 2 * (a * x + (1 - a) * y))) *
      (1 - 11 / 20 * (65 / 100) ^ 2 * (y - (a * x + (1 - a) * y)))) =
      exp (-(11 / 20 * (65 / 100) ^ 2 * (a * x + (1 - a) * y))) := by ring
  linarith

/-- **`h` is increasing**: `h' = B + C κ exp(-κ u) > 0`. -/
theorem monotone_absMomentBound : Monotone absMomentBound := fun x y hxy => by
  unfold absMomentBound
  have : exp (-(11 / 20 * (65 / 100) ^ 2 * y)) ≤ exp (-(11 / 20 * (65 / 100) ^ 2 * x)) :=
    exp_le_exp.2 (by nlinarith)
  nlinarith

/-- **Jensen's inequality for `h`** under a uniform average: `𝔼 h(u) ≤ h(𝔼 u)`. -/
theorem expect_absMomentBound_le {α : Type*} [Fintype α] [Nonempty α] (u : α → ℝ) :
    𝔼 a, absMomentBound (u a) ≤ absMomentBound (𝔼 a, u a) := by
  set m := 𝔼 a, u a
  have h : ∀ a, absMomentBound (u a) ≤ absMomentBound m +
      (104 / 1000 + 77 / 100 * exp (-(11 / 20 * (65 / 100) ^ 2 * m)) *
        (11 / 20 * (65 / 100) ^ 2)) * (u a - m) := fun a => by
    have := exp_neg_tangent_le m (u a)
    unfold absMomentBound
    nlinarith
  refine (Finset.expect_le_expect fun a _ => h a).trans_eq ?_
  rw [Finset.expect_add_distrib, ← Finset.mul_expect, Finset.expect_sub_distrib,
    Finset.expect_const Finset.univ_nonempty, Finset.expect_const Finset.univ_nonempty]
  ring

/-! ### The first absolute moment -/

/-- **The first absolute moment from the second moment and the characteristic function**: for
a random variable `X` on a finite uniform space with `𝔼 X² = u` and
`exp(-κ u) ≤ 𝔼 cos((65/100) X)`, `𝔼 |X| ≤ h(u)` (`abs_le_majorant`). -/
theorem expect_abs_le_absMomentBound {Ω : Type*} [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) {u : ℝ}
    (hsq : 𝔼 ω, X ω ^ 2 = u)
    (hcos : exp (-(11 / 20 * (65 / 100) ^ 2 * u)) ≤ 𝔼 ω, cos (65 / 100 * X ω)) :
    𝔼 ω, |X ω| ≤ absMomentBound u := by
  calc 𝔼 ω, |X ω| ≤ 𝔼 ω, (183 / 100 + 104 / 1000 * X ω ^ 2 - 77 / 100 * cos (65 / 100 * X ω)) :=
        Finset.expect_le_expect fun ω _ => abs_le_majorant (X ω)
    _ = 183 / 100 + 104 / 1000 * (𝔼 ω, X ω ^ 2) - 77 / 100 * 𝔼 ω, cos (65 / 100 * X ω) := by
        rw [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
          ← Finset.mul_expect, Finset.expect_const Finset.univ_nonempty]
    _ ≤ absMomentBound u := by
        rw [hsq]
        unfold absMomentBound
        linarith

/-- **The Gaussian lower bound for a product of cosines**: for `|a_i| ≤ 1`,
`exp(-κ ∑_i a_i²) ≤ ∏_i cos((65/100) a_i)` (`exp_neg_le_cos`). -/
theorem exp_neg_le_prod_cos {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, |a i| ≤ 1) :
    exp (-(11 / 20 * (65 / 100) ^ 2 * ∑ i ∈ s, a i ^ 2)) ≤ ∏ i ∈ s, cos (65 / 100 * a i) := by
  rw [mul_sum, ← sum_neg_distrib, exp_sum]
  refine prod_le_prod₀ (fun i _ => (exp_pos _).le) fun i hi => ?_
  have hb : |65 / 100 * a i| ≤ 65 / 100 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 65 / 100)]
    nlinarith [ha i hi, abs_nonneg (a i)]
  refine le_of_eq_of_le ?_ (exp_neg_le_cos hb)
  congr 1
  ring

/-- **The first absolute moment of a Rademacher sum**: for independent uniform signs and
weights `|a_i| ≤ 1`, `𝔼_ε |∑_i ±a_i| ≤ h(∑_i a_i²)`. -/
theorem expect_abs_rademacher_le {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ)
    (ha : ∀ i, |a i| ≤ 1) :
    𝔼 ε : ι → Bool, |∑ i, if ε i then a i else -a i| ≤ absMomentBound (∑ i, a i ^ 2) := by
  have hcard : ((Fintype.card (ι → Bool) : ℕ) : ℝ) = 2 ^ Fintype.card ι := by
    simp [Fintype.card_bool]
  have h2 : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  refine expect_abs_le_absMomentBound _ ?_ ?_
  · rw [Fintype.expect_eq_sum_div_card, sum_bool_sq_sum, hcard]
    field_simp
  · rw [Fintype.expect_eq_sum_div_card, hcard]
    have hc := sum_bool_cos_sum (fun i b => 65 / 100 * (if b then a i else -a i)) fun i => by
      simp
    simp only [← mul_sum, ↓reduceIte] at hc
    rw [hc, mul_div_cancel_left₀ _ h2]
    exact exp_neg_le_prod_cos univ a fun i _ => ha i

end Real
