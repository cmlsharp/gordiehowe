-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

public section

/-!
# Fixed-point cosine and sine at the angles `π m / 2^e`

`cosFix e P m` and `sinFix e P m` are integers within `1` of `2^P cos (π m / 2^e)` and
`2^P sin (π m / 2^e)` (`abs_cosFix_sub_le`, `abs_sinFix_sub_le`), for every `e`, `P` and `m`.
They are computed with integer arithmetic only, at the scale `2^S`, `S = P + e + 8`:

* `sqrtSeriesFix T k`: `2^T · sqrtTwoAddSeries 0 k` within `2`, by the recursion
  `a (k + 1) = ⌊√(2^(2T+1) + 2^T a k)⌋` (`abs_sqrtSeriesFix_sub_le`);
* `baseCosFix S e`, `baseSinFix S e`: `2^S cos (π / 2^e)` and `2^S sin (π / 2^e)` within `3`,
  from `cos (π / 2^(k+1)) = sqrtTwoAddSeries 0 k / 2` and
  `sin (π / 2^(k+2)) = √(2 − sqrtTwoAddSeries 0 k) / 2`;
* `powFix S e m`: `m` rotations of `(2^S, 0)` by the base point, each rounded down, within `9 m`
  of `2^S exp (i π m / 2^e)` for `m ≤ 2^(e+1)` (`norm_powFix_sub_le`);
* `cosFix`, `sinFix`: the rotation at `m mod 2^(e+1)` rounded to the nearest multiple of
  `2^(e+8)`.
-/

namespace FixedPoint

open Real

/-! ### Rounding -/

/-- The integer square root is within `1` of the real one. -/
theorem abs_natSqrt_sub_sqrt_le (a : ℕ) : |(Nat.sqrt a : ℝ) - √(a : ℝ)| ≤ 1 := by
  rw [abs_sub_comm, abs_le]
  constructor
  · linarith [Real.nat_sqrt_le_real_sqrt (a := a)]
  · linarith [Real.real_sqrt_le_nat_sqrt_succ (a := a)]

/-- Above `c² > 0` the square root is Lipschitz with constant `1 / (2c)`. -/
theorem abs_sqrt_sub_sqrt_le_of_sq_le {x y c : ℝ} (hc : 0 < c) (hx : c ^ 2 ≤ x)
    (hy : c ^ 2 ≤ y) : |√x - √y| ≤ |x - y| / (2 * c) := by
  have hx0 : 0 ≤ x := (sq_nonneg c).trans hx
  have hy0 : 0 ≤ y := (sq_nonneg c).trans hy
  have hcx : c ≤ √x := (Real.le_sqrt' hc).2 hx
  have hcy : c ≤ √y := (Real.le_sqrt' hc).2 hy
  have hsum : 0 < √x + √y := by linarith
  have hm : (√x - √y) * (√x + √y) = x - y := by
    linear_combination Real.sq_sqrt hx0 - Real.sq_sqrt hy0
  rw [le_div_iff₀ (by positivity), ← hm, abs_mul, abs_of_pos hsum]
  exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

/-- The square root is `1/2`-Hölder: `|√x − √y| ≤ √|x − y|`. -/
theorem abs_sqrt_sub_sqrt_le_sqrt_abs {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |√x - √y| ≤ √|x - y| := by
  wlog h : y ≤ x generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]
    exact this hy hx (not_le.1 h).le
  have hs : √y ≤ √x := Real.sqrt_le_sqrt h
  rw [abs_of_nonneg (sub_nonneg.2 hs), abs_of_nonneg (sub_nonneg.2 h), sub_le_iff_le_add]
  have hxy : 0 ≤ x - y := sub_nonneg.2 h
  calc √x ≤ √((√(x - y) + √y) ^ 2) := Real.sqrt_le_sqrt (by
          nlinarith [Real.sq_sqrt hxy, Real.sq_sqrt hy,
            mul_nonneg (Real.sqrt_nonneg (x - y)) (Real.sqrt_nonneg y)])
    _ = √(x - y) + √y := Real.sqrt_sq (by positivity)

/-- Natural division rounds down by less than `1`. -/
theorem natCast_div_bounds (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ n / d ∧ (n : ℝ) / d - 1 < ((n / d : ℕ) : ℝ) := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have h := Nat.lt_mul_div_succ n hd
  have h' : (n : ℝ) < d * ((n / d : ℕ) + 1) := by exact_mod_cast h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hd']
  linarith

/-- Integer division by a positive natural rounds down by less than `1`. -/
theorem intCast_div_bounds (a : ℤ) (d : ℕ) (hd : 0 < d) :
    ((a / (d : ℤ) : ℤ) : ℝ) ≤ a / d ∧ (a : ℝ) / d - 1 < ((a / (d : ℤ) : ℤ) : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdz : (0 : ℤ) < d := by exact_mod_cast hd
  have e := Int.mul_ediv_add_emod a d
  have h0 := Int.emod_nonneg a hdz.ne'
  have h1 := Int.emod_lt_of_pos a hdz
  have e' : (d : ℝ) * ((a / (d : ℤ) : ℤ) : ℝ) + ((a % (d : ℤ) : ℤ) : ℝ) = a := by
    exact_mod_cast e
  have h0' : (0 : ℝ) ≤ ((a % (d : ℤ) : ℤ) : ℝ) := by exact_mod_cast h0
  have h1' : ((a % (d : ℤ) : ℤ) : ℝ) < d := by exact_mod_cast h1
  constructor
  · rw [le_div_iff₀ hd']; linarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hd']; linarith

/-! ### The series `sqrtTwoAddSeries 0 k` in fixed point -/

/-- `2^T · sqrtTwoAddSeries 0 k`, rounded down at every square root. -/
def sqrtSeriesFix (T : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => Nat.sqrt (2 ^ (2 * T + 1) + 2 ^ T * sqrtSeriesFix T k)

/-- `sqrtSeriesFix T k` is within `2` of `2^T · sqrtTwoAddSeries 0 k`. -/
theorem abs_sqrtSeriesFix_sub_le (T : ℕ) :
    ∀ k, |(sqrtSeriesFix T k : ℝ) - 2 ^ T * sqrtTwoAddSeries 0 k| ≤ 2
  | 0 => by simp [sqrtSeriesFix]
  | k + 1 => by
    have ih := abs_sqrtSeriesFix_sub_le T k
    set a := sqrtSeriesFix T k
    set s := sqrtTwoAddSeries 0 k
    have hs0 : 0 ≤ s := sqrtTwoAddSeries_zero_nonneg k
    have hc : (0 : ℝ) < 2 ^ T := by positivity
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hA : ((2 ^ (2 * T + 1) + 2 ^ T * a : ℕ) : ℝ) = 2 * (2 ^ T) ^ 2 + 2 ^ T * a := by
      push_cast; ring
    have hB : 2 ^ T * sqrtTwoAddSeries 0 (k + 1) = √((2 ^ T) ^ 2 * (2 + s)) := by
      rw [sqrtTwoAddSeries, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
    have h1 := abs_natSqrt_sub_sqrt_le (2 ^ (2 * T + 1) + 2 ^ T * a)
    have h2 := abs_sqrt_sub_sqrt_le_of_sq_le hc
      (x := ((2 ^ (2 * T + 1) + 2 ^ T * a : ℕ) : ℝ)) (y := (2 ^ T) ^ 2 * (2 + s))
      (by rw [hA]; nlinarith [mul_nonneg hc.le ha0])
      (by nlinarith [mul_nonneg (sq_nonneg (2 ^ T : ℝ)) hs0])
    have h3 : |((2 ^ (2 * T + 1) + 2 ^ T * a : ℕ) : ℝ) - (2 ^ T) ^ 2 * (2 + s)| ≤ 2 * 2 ^ T := by
      rw [hA, show 2 * (2 ^ T : ℝ) ^ 2 + 2 ^ T * a - (2 ^ T) ^ 2 * (2 + s) =
        2 ^ T * (a - 2 ^ T * s) by ring, abs_mul, abs_of_pos hc]
      nlinarith
    have h4 : |((2 ^ (2 * T + 1) + 2 ^ T * a : ℕ) : ℝ) - (2 ^ T) ^ 2 * (2 + s)| / (2 * 2 ^ T)
        ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    rw [sqrtSeriesFix, hB]
    calc _ ≤ |(Nat.sqrt (2 ^ (2 * T + 1) + 2 ^ T * a) : ℝ) -
            √((2 ^ (2 * T + 1) + 2 ^ T * a : ℕ) : ℝ)| +
          |√((2 ^ (2 * T + 1) + 2 ^ T * a : ℕ) : ℝ) - √((2 ^ T) ^ 2 * (2 + s))| :=
          abs_sub_le _ _ _
      _ ≤ 1 + 1 := add_le_add h1 (h2.trans h4)
      _ = 2 := by norm_num

/-! ### The base point `2^S exp (i π / 2^e)` -/

/-- `2^S cos (π / 2^e)` in fixed point. -/
def baseCosFix (S : ℕ) : ℕ → ℤ
  | 0 => -2 ^ S
  | 1 => 0
  | k + 2 => ((sqrtSeriesFix (2 * S + 1) (k + 1) / 2 ^ (S + 2) : ℕ) : ℤ)

/-- `2^S sin (π / 2^e)` in fixed point. -/
def baseSinFix (S : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => 2 ^ S
  | k + 2 => (Nat.sqrt ((2 ^ (2 * S + 2) - sqrtSeriesFix (2 * S + 1) k) / 8) : ℤ)

/-- `baseCosFix S e` is within `3` of `2^S cos (π / 2^e)`. -/
theorem abs_baseCosFix_sub_le (S : ℕ) :
    ∀ e, |(baseCosFix S e : ℝ) - 2 ^ S * cos (π / 2 ^ e)| ≤ 3
  | 0 => by simp [baseCosFix]
  | 1 => by simp [baseCosFix]
  | k + 2 => by
    have h := abs_sqrtSeriesFix_sub_le (2 * S + 1) (k + 1)
    set a := sqrtSeriesFix (2 * S + 1) (k + 1)
    have hd : (0 : ℝ) < 2 ^ (S + 2) := by positivity
    have hc : 2 ^ S * cos (π / 2 ^ (k + 2)) =
        2 ^ (2 * S + 1) * sqrtTwoAddSeries 0 (k + 1) / 2 ^ (S + 2) := by
      rw [show k + 2 = (k + 1) + 1 from rfl, cos_pi_over_two_pow]
      field_simp
      ring
    obtain ⟨h1, h2⟩ := natCast_div_bounds a (2 ^ (S + 2)) (by positivity)
    push_cast at h1 h2
    simp only [baseCosFix, Int.cast_natCast]
    rw [hc]
    have h3 : |(a : ℝ) / 2 ^ (S + 2) - 2 ^ (2 * S + 1) * sqrtTwoAddSeries 0 (k + 1) /
        2 ^ (S + 2)| ≤ 1 := by
      rw [← sub_div, abs_div, abs_of_pos hd, div_le_one hd]
      refine h.trans ?_
      calc (2 : ℝ) ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (S + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [abs_le] at h3 ⊢
    constructor <;> linarith [h3.1, h3.2]

/-- `baseSinFix S e` is within `3` of `2^S sin (π / 2^e)`. -/
theorem abs_baseSinFix_sub_le (S : ℕ) :
    ∀ e, |(baseSinFix S e : ℝ) - 2 ^ S * sin (π / 2 ^ e)| ≤ 3
  | 0 => by simp [baseSinFix]
  | 1 => by simp [baseSinFix]
  | k + 2 => by
    have h := abs_sqrtSeriesFix_sub_le (2 * S + 1) k
    set a := sqrtSeriesFix (2 * S + 1) k
    set s := sqrtTwoAddSeries 0 k
    have hs2 : s < 2 := sqrtTwoAddSeries_lt_two k
    have hc : (0 : ℝ) < 2 ^ S := by positivity
    set Z : ℝ := (2 ^ S / 2) ^ 2 * (2 - s) with hZ
    have hZ0 : 0 ≤ Z := mul_nonneg (sq_nonneg _) (by linarith)
    have hsin : 2 ^ S * sin (π / 2 ^ (k + 2)) = √Z := by
      rw [sin_pi_over_two_pow_succ, hZ, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      ring
    have hpow : (2 : ℝ) ^ (2 * S + 2) = 2 * 2 ^ (2 * S + 1) := by ring
    -- the truncated difference `2^(2S+2) − a` is within `2` of `8 Z`
    have h8 : |((2 ^ (2 * S + 2) - a : ℕ) : ℝ) - 8 * Z| ≤ 2 := by
      have e8 : 8 * Z = 2 ^ (2 * S + 2) - 2 ^ (2 * S + 1) * s := by
        rw [hZ]; ring
      rw [e8]
      rcases le_or_gt a (2 ^ (2 * S + 2)) with hle | hlt
      · rw [Nat.cast_sub hle]
        push_cast
        rw [show (2 : ℝ) ^ (2 * S + 2) - a - (2 ^ (2 * S + 2) - 2 ^ (2 * S + 1) * s) =
          -(a - 2 ^ (2 * S + 1) * s) by ring, abs_neg]
        exact h
      · rw [Nat.sub_eq_zero_of_le hlt.le]
        have hlt' : (2 : ℝ) ^ (2 * S + 2) < a := by exact_mod_cast hlt
        have hpos : 0 ≤ (2 : ℝ) ^ (2 * S + 2) - 2 ^ (2 * S + 1) * s := by
          rw [hpow]; nlinarith [pow_pos (two_pos (α := ℝ)) (2 * S + 1)]
        rw [abs_le] at h
        rw [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hpos]
        linarith [h.2]
    obtain ⟨h1, h2⟩ := natCast_div_bounds (2 ^ (2 * S + 2) - a) 8 (by norm_num)
    set M := 2 ^ (2 * S + 2) - a
    set N := M / 8
    have hNZ : |(N : ℝ) - Z| ≤ 4 := by
      rw [abs_le] at h8 ⊢
      push_cast at h1 h2
      constructor <;> linarith [h8.1, h8.2]
    have hN := abs_natSqrt_sub_sqrt_le N
    have hsq := abs_sqrt_sub_sqrt_le_sqrt_abs (Nat.cast_nonneg (α := ℝ) N) hZ0
    have h4 : √|(N : ℝ) - Z| ≤ 2 := by
      calc √|(N : ℝ) - Z| ≤ √(2 ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ = 2 := Real.sqrt_sq (by norm_num)
    simp only [baseSinFix, Int.cast_natCast]
    rw [hsin]
    calc _ ≤ |(Nat.sqrt N : ℝ) - √(N : ℝ)| + |√(N : ℝ) - √Z| := abs_sub_le _ _ _
      _ ≤ 1 + 2 := add_le_add hN (hsq.trans h4)
      _ = 3 := by norm_num

/-! ### Rotations -/

/-- A pair of integers read as the complex number `z.1 + z.2 i`. -/
def toComplex (z : ℤ × ℤ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

/-- The product `z w / 2^S`, each coordinate rounded down. -/
def rotFix (S : ℕ) (w z : ℤ × ℤ) : ℤ × ℤ :=
  ((z.1 * w.1 - z.2 * w.2) / ((2 ^ S : ℕ) : ℤ), (z.1 * w.2 + z.2 * w.1) / ((2 ^ S : ℕ) : ℤ))

/-- `2^S exp (i π m / 2^e)` in fixed point: `m` rotations of `(2^S, 0)` by the base point. -/
def powFix (S e : ℕ) : ℕ → ℤ × ℤ
  | 0 => (2 ^ S, 0)
  | m + 1 => rotFix S (baseCosFix S e, baseSinFix S e) (powFix S e m)

/-- The rounding of `rotFix` moves `z w / 2^S` by at most `2`. -/
theorem norm_rotFix_sub_le (S : ℕ) (w z : ℤ × ℤ) :
    ‖toComplex (rotFix S w z) - toComplex z * toComplex w / ((2 ^ S : ℝ) : ℂ)‖ ≤ 2 := by
  obtain ⟨a1, a2⟩ := intCast_div_bounds (z.1 * w.1 - z.2 * w.2) (2 ^ S) (by positivity)
  obtain ⟨b1, b2⟩ := intCast_div_bounds (z.1 * w.2 + z.2 * w.1) (2 ^ S) (by positivity)
  push_cast at a1 a2 b1 b2
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (toComplex (rotFix S w z) - toComplex z * toComplex w / ((2 ^ S : ℝ) : ℂ)).re =
      (((z.1 * w.1 - z.2 * w.2) / ((2 ^ S : ℕ) : ℤ) : ℤ) : ℝ) -
        ((z.1 : ℝ) * w.1 - z.2 * w.2) / 2 ^ S := by
    unfold toComplex rotFix
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
      Complex.div_ofReal_re, 
      ]
    push_cast
    ring
  have him : (toComplex (rotFix S w z) - toComplex z * toComplex w / ((2 ^ S : ℝ) : ℂ)).im =
      (((z.1 * w.2 + z.2 * w.1) / ((2 ^ S : ℕ) : ℤ) : ℤ) : ℝ) -
        ((z.1 : ℝ) * w.2 + z.2 * w.1) / 2 ^ S := by
    unfold toComplex rotFix
    simp only [Complex.add_re, Complex.mul_re, Complex.sub_im, Complex.add_im,
      Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
      Complex.div_ofReal_im,
      ]
    push_cast
    ring
  rw [hre, him]
  push_cast
  have hr : |(((z.1 * w.1 - z.2 * w.2) / 2 ^ S : ℤ) : ℝ) -
      ((z.1 : ℝ) * w.1 - z.2 * w.2) / 2 ^ S| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hi : |(((z.1 * w.2 + z.2 * w.1) / 2 ^ S : ℤ) : ℝ) -
      ((z.1 : ℝ) * w.2 + z.2 * w.1) / 2 ^ S| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  linarith

/-- The unit `exp (i π / 2^e)`. -/
noncomputable def unitRoot (e : ℕ) : ℂ := Complex.exp (((π / 2 ^ e : ℝ) : ℂ) * Complex.I)

/-- The unit `exp (i π / 2^e)` as an exponential. -/
theorem unitRoot_eq (e : ℕ) :
    unitRoot e = Complex.exp (((π / 2 ^ e : ℝ) : ℂ) * Complex.I) := by
  rw [unitRoot]

/-- `exp (i π / 2^e)` has norm `1`. -/
theorem norm_unitRoot (e : ℕ) : ‖unitRoot e‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- The base point is within `6` of `2^S exp (i π / 2^e)`. -/
theorem norm_base_sub_le (S e : ℕ) :
    ‖toComplex (baseCosFix S e, baseSinFix S e) - ((2 ^ S : ℝ) : ℂ) * unitRoot e‖ ≤ 6 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (toComplex (baseCosFix S e, baseSinFix S e) - ((2 ^ S : ℝ) : ℂ) * unitRoot e).re =
      (baseCosFix S e : ℝ) - 2 ^ S * cos (π / 2 ^ e) := by
    unfold toComplex unitRoot
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, 
      Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, 
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  have him : (toComplex (baseCosFix S e, baseSinFix S e) - ((2 ^ S : ℝ) : ℂ) * unitRoot e).im =
      (baseSinFix S e : ℝ) - 2 ^ S * sin (π / 2 ^ e) := by
    unfold toComplex unitRoot
    simp only [Complex.sub_im, Complex.add_im,
      Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, 
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  rw [hre, him]
  linarith [abs_baseCosFix_sub_le S e, abs_baseSinFix_sub_le S e]

/-- **The rotation error grows linearly**: for `e + 8 ≤ S` and `m ≤ 2^(e+1)`, `powFix S e m` is
within `9 m` of `2^S exp (i π m / 2^e)`. -/
theorem norm_powFix_sub_le {S e : ℕ} (hS : e + 8 ≤ S) :
    ∀ m, m ≤ 2 ^ (e + 1) →
      ‖toComplex (powFix S e m) - ((2 ^ S : ℝ) : ℂ) * unitRoot e ^ m‖ ≤ 9 * m
  | 0, _ => by simp [powFix, toComplex]
  | m + 1, hm => by
    have ih := norm_powFix_sub_le hS m (by omega)
    set z := toComplex (powFix S e m)
    set w := toComplex (baseCosFix S e, baseSinFix S e)
    set c : ℂ := ((2 ^ S : ℝ) : ℂ)
    set ψ := unitRoot e
    have hc : (0 : ℝ) < 2 ^ S := by positivity
    have hc0 : c ≠ 0 := by simp [c]
    have hcn : ‖c‖ = 2 ^ S := by simp [c]
    have hw := norm_base_sub_le S e
    have hψ := norm_unitRoot e
    have hr := norm_rotFix_sub_le S (baseCosFix S e, baseSinFix S e) (powFix S e m)
    -- `54 m ≤ 2^S`
    have hm54 : (54 : ℝ) * m ≤ 2 ^ S := by
      have h1 : 2 ^ (e + 8) ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) hS
      have h2 : 2 ^ (e + 8) = 128 * 2 ^ (e + 1) := by ring
      have h3 : 54 * m ≤ 2 ^ S := by omega
      exact_mod_cast h3
    have hwn : ‖w‖ ≤ 2 ^ S + 6 := by
      calc ‖w‖ = ‖c * ψ + (w - c * ψ)‖ := by ring_nf
        _ ≤ ‖c * ψ‖ + ‖w - c * ψ‖ := norm_add_le _ _
        _ ≤ 2 ^ S + 6 := by rw [norm_mul, hcn, hψ, mul_one]; linarith
    have hprod : ‖z * w - c * ψ ^ m * (c * ψ)‖ ≤ 9 * m * (2 ^ S + 6) + 2 ^ S * 6 := by
      calc ‖z * w - c * ψ ^ m * (c * ψ)‖ = ‖(z - c * ψ ^ m) * w + c * ψ ^ m * (w - c * ψ)‖ := by
            congr 1; ring
        _ ≤ ‖z - c * ψ ^ m‖ * ‖w‖ + ‖c * ψ ^ m‖ * ‖w - c * ψ‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ 9 * m * (2 ^ S + 6) + 2 ^ S * 6 := by
            rw [norm_mul, norm_pow, hψ, one_pow, mul_one, hcn]
            gcongr
    have hsplit : toComplex (powFix S e (m + 1)) - c * ψ ^ (m + 1) =
        (toComplex (powFix S e (m + 1)) - z * w / c) + (z * w - c * ψ ^ m * (c * ψ)) / c := by
      field_simp
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, hcn]
    have hq : ‖z * w - c * ψ ^ m * (c * ψ)‖ / 2 ^ S ≤ 9 * m + 7 := by
      rw [div_le_iff₀ hc]
      nlinarith
    have hr' : ‖toComplex (powFix S e (m + 1)) - z * w / c‖ ≤ 2 := hr
    push_cast
    linarith

/-! ### Cosine and sine -/

/-- **Fixed-point cosine**: an integer within `1` of `2^P cos (π m / 2^e)`. -/
def cosFix (e P m : ℕ) : ℤ :=
  ((powFix (P + (e + 8)) e (m % 2 ^ (e + 1))).1 + 2 ^ (e + 7)) / ((2 ^ (e + 8) : ℕ) : ℤ)

/-- **Fixed-point sine**: an integer within `1` of `2^P sin (π m / 2^e)`. -/
def sinFix (e P m : ℕ) : ℤ :=
  ((powFix (P + (e + 8)) e (m % 2 ^ (e + 1))).2 + 2 ^ (e + 7)) / ((2 ^ (e + 8) : ℕ) : ℤ)

/-- Rounding `x / 2^(e+8)` to the nearest integer, for `x` within `18 · 2^e` of `2^(P+e+8) v`,
lands within `1` of `2^P v`. -/
theorem abs_round_sub_le (e P : ℕ) (x : ℤ) (v : ℝ)
    (hx : |(x : ℝ) - 2 ^ (P + (e + 8)) * v| ≤ 9 * 2 ^ (e + 1)) :
    |(((x + 2 ^ (e + 7)) / ((2 ^ (e + 8) : ℕ) : ℤ) : ℤ) : ℝ) - 2 ^ P * v| ≤ 1 := by
  obtain ⟨h1, h2⟩ := intCast_div_bounds (x + 2 ^ (e + 7)) (2 ^ (e + 8)) (by positivity)
  set q := (((x + 2 ^ (e + 7)) / ((2 ^ (e + 8) : ℕ) : ℤ) : ℤ) : ℝ)
  have hu : (0 : ℝ) < 2 ^ e := by positivity
  have hv : (0 : ℝ) < 2 ^ P := by positivity
  have e1 : ((2 ^ (e + 8) : ℕ) : ℝ) = 256 * 2 ^ e := by push_cast; ring
  have e2 : ((x + 2 ^ (e + 7) : ℤ) : ℝ) = x + 128 * 2 ^ e := by push_cast; ring
  have e3 : (2 : ℝ) ^ (P + (e + 8)) * v = 256 * 2 ^ e * (2 ^ P * v) := by ring
  have e4 : (9 : ℝ) * 2 ^ (e + 1) = 18 * 2 ^ e := by ring
  rw [e1, e2, le_div_iff₀ (by positivity)] at h1
  rw [e1, e2, sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)] at h2
  rw [e3, e4, abs_le] at hx
  rw [abs_le]
  constructor <;> nlinarith [hx.1, hx.2]

/-- `Re (exp (i π / 2^e) ^ m) = cos (π m / 2^e)` and `Im (…) = sin (π m / 2^e)`. -/
theorem re_im_unitRoot_pow (e m : ℕ) :
    (unitRoot e ^ m).re = cos (π * m / 2 ^ e) ∧ (unitRoot e ^ m).im = sin (π * m / 2 ^ e) := by
  have hpow : unitRoot e ^ m = Complex.exp (((π * m / 2 ^ e : ℝ) : ℂ) * Complex.I) := by
    rw [unitRoot, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [hpow, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  exact ⟨rfl, rfl⟩

/-- `cos (π m / 2^e) = Re (exp (i π / 2^e) ^ (m mod 2^(e+1)))`, and the same for `sin`. -/
theorem cos_eq_re_unitRoot_pow (e m : ℕ) :
    cos (π * m / 2 ^ e) = (unitRoot e ^ (m % 2 ^ (e + 1))).re ∧
      sin (π * m / 2 ^ e) = (unitRoot e ^ (m % 2 ^ (e + 1))).im := by
  have hang : π * m / 2 ^ e =
      π * ((m % 2 ^ (e + 1) : ℕ) : ℝ) / 2 ^ e + ((m / 2 ^ (e + 1) : ℕ) : ℝ) * (2 * π) := by
    have hm := Nat.mod_add_div m (2 ^ (e + 1))
    have hm' : (m : ℝ) = ((m % 2 ^ (e + 1) : ℕ) : ℝ) + 2 ^ (e + 1) * ((m / 2 ^ (e + 1) : ℕ) : ℝ) :=
      by exact_mod_cast hm.symm
    rw [hm']
    field_simp
    ring
  rw [(re_im_unitRoot_pow e _).1, (re_im_unitRoot_pow e _).2, hang]
  exact ⟨cos_add_nat_mul_two_pi _ _, sin_add_nat_mul_two_pi _ _⟩

/-- **The fixed-point cosine is within `1`**: `|cosFix e P m − 2^P cos (π m / 2^e)| ≤ 1`. -/
theorem abs_cosFix_sub_le (e P m : ℕ) :
    |(cosFix e P m : ℝ) - 2 ^ P * cos (π * m / 2 ^ e)| ≤ 1 := by
  have hr : m % 2 ^ (e + 1) ≤ 2 ^ (e + 1) := (Nat.mod_lt _ (by positivity)).le
  have h := norm_powFix_sub_le (S := P + (e + 8)) (e := e) (by omega) _ hr
  refine abs_round_sub_le e P _ _ ?_
  rw [(cos_eq_re_unitRoot_pow e m).1]
  refine le_trans ?_ (h.trans ?_)
  · refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
    rw [Complex.sub_re, Complex.re_ofReal_mul]
    simp [toComplex]
  · have : ((m % 2 ^ (e + 1) : ℕ) : ℝ) ≤ 2 ^ (e + 1) := by exact_mod_cast hr
    linarith

/-- **The fixed-point sine is within `1`**: `|sinFix e P m − 2^P sin (π m / 2^e)| ≤ 1`. -/
theorem abs_sinFix_sub_le (e P m : ℕ) :
    |(sinFix e P m : ℝ) - 2 ^ P * sin (π * m / 2 ^ e)| ≤ 1 := by
  have hr : m % 2 ^ (e + 1) ≤ 2 ^ (e + 1) := (Nat.mod_lt _ (by positivity)).le
  have h := norm_powFix_sub_le (S := P + (e + 8)) (e := e) (by omega) _ hr
  refine abs_round_sub_le e P _ _ ?_
  rw [(cos_eq_re_unitRoot_pow e m).2]
  refine le_trans ?_ (h.trans ?_)
  · refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
    rw [Complex.sub_im, Complex.im_ofReal_mul]
    simp [toComplex]
  · have : ((m % 2 ^ (e + 1) : ℕ) : ℝ) ≤ 2 ^ (e + 1) := by exact_mod_cast hr
    linarith

-- At `e = 2`, `P = 4`: `16 cos (π / 4) ≈ 11.3` and `16 sin (6π / 4) = -16`.
example : cosFix 2 4 1 = 11 ∧ sinFix 2 4 1 = 11 ∧ cosFix 2 4 3 = -11 ∧ sinFix 2 4 6 = -16 := by
  decide +kernel

end FixedPoint
