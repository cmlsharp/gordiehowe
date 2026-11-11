-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.BinomialFloor

public section

/-!
# The binomial CDF at a dyadic probability

At `x = u / 2^r` with `u ≤ 2^r`, every term of the binomial CDF has the denominator `2^(r N)`, so
`binomialCdf (u / 2^r) N ω = binomialCdfNum u r N ω / 2^(r N)` with a natural-number numerator
(`binomialCdf_dyadic`). The numerator is `v^(N - ω)` times a Horner sum in `v = 2^r - u` that a
structural recursion carries along with the binomial coefficient and the power of `u`
(`binomialCdfNumLoop`, `binomialCdfNum_eq_loop`), so a floor `2^-e ≤ binomialCdf (u / 2^r) N ω` at
concrete constants is a kernel comparison of natural numbers
(`one_div_two_pow_le_binomialCdf_of_loop`).

* `two_pow_neg_le_binomialCdf_1536_55`: `2^-14 ≤ Pr[Bin(1536, 233/4096) ≤ 55]` (ML-DSA-65:
  `N = 6 · 256`, `ω = 55`).
* `two_pow_neg_le_binomialCdf_2048_75`: `2^-18 ≤ Pr[Bin(2048, 15/256) ≤ 75]` (ML-DSA-87:
  `N = 8 · 256`, `ω = 75`).
-/

namespace GordieHowe.MLDSA

open Finset

/-- The numerator of the binomial CDF at `u / 2^r` over the denominator `2^(r N)`:
`∑_{j ≤ ω} C(N, j) u^j (2^r - u)^(N - j)`. -/
def binomialCdfNum (u r N ω : ℕ) : ℕ :=
  ∑ j ∈ range (ω + 1), N.choose j * u ^ j * (2 ^ r - u) ^ (N - j)

/-- **The binomial CDF at a dyadic probability**: for `u ≤ 2^r`,
`binomialCdf (u / 2^r) N ω = binomialCdfNum u r N ω / 2^(r N)`. -/
theorem binomialCdf_dyadic {u r : ℕ} (hu : u ≤ 2 ^ r) (N ω : ℕ) :
    binomialCdf ((u : ℝ) / 2 ^ r) N ω = (binomialCdfNum u r N ω : ℝ) / 2 ^ (r * N) := by
  rw [binomialCdf, binomialCdfNum, Nat.cast_sum, sum_div]
  refine sum_congr rfl fun j _ => ?_
  rcases le_or_gt j N with hj | hj
  · have hv : (1 : ℝ) - u / 2 ^ r = ((2 ^ r - u : ℕ) : ℝ) / 2 ^ r := by
      rw [Nat.cast_sub hu]
      field_simp
      push_cast
      ring
    have h2 : (2 : ℝ) ^ (r * N) = (2 ^ r) ^ j * (2 ^ r) ^ (N - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hj, ← pow_mul]
    rw [hv, h2, div_pow, div_pow]
    push_cast
    field_simp
  · simp [Nat.choose_eq_zero_of_lt hj]

/-- A Horner evaluation of `∑ i < k, C(N, j + i) u^(j + i) v^(k - 1 - i)`, carrying the binomial
coefficient `c = C(N, j)` and the power `p = u^j` along (`binomialCdfNumLoop_eq`). -/
@[expose] def binomialCdfNumLoop (N u v : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _, acc => acc
  | k + 1, j, c, p, acc =>
    binomialCdfNumLoop N u v k (j + 1) (c * (N - j) / (j + 1)) (p * u) (acc * v + c * p)

/-- The loop computes the Horner sum. -/
theorem binomialCdfNumLoop_eq (N u v : ℕ) (k : ℕ) : ∀ j acc,
    binomialCdfNumLoop N u v k j (N.choose j) (u ^ j) acc =
      acc * v ^ k + ∑ i ∈ range k, N.choose (j + i) * u ^ (j + i) * v ^ (k - 1 - i) := by
  induction k with
  | zero => intro j acc; simp [binomialCdfNumLoop]
  | succ k ih =>
    intro j acc
    have hc : N.choose j * (N - j) / (j + 1) = N.choose (j + 1) := by
      rw [← Nat.choose_succ_right_eq, Nat.mul_div_cancel _ (Nat.succ_pos j)]
    rw [binomialCdfNumLoop, hc, ← pow_succ, ih, sum_range_succ']
    simp only [Nat.add_zero, Nat.add_sub_cancel, Nat.sub_zero, add_assoc, Nat.add_comm 1]
    have hk : ∀ x, k - (x + 1) = k - 1 - x := fun x => by omega
    rw [sum_congr rfl fun x _ => by rw [← hk x]]
    ring

/-- The numerator through the loop: for `ω ≤ N`,
`binomialCdfNum u r N ω = v^(N - ω) · binomialCdfNumLoop N u v (ω + 1) 0 1 1 0`, `v = 2^r - u`. -/
theorem binomialCdfNum_eq_loop (u r : ℕ) {N ω : ℕ} (hω : ω ≤ N) :
    binomialCdfNum u r N ω =
      (2 ^ r - u) ^ (N - ω) * binomialCdfNumLoop N u (2 ^ r - u) (ω + 1) 0 1 1 0 := by
  have h := binomialCdfNumLoop_eq N u (2 ^ r - u) (ω + 1) 0 0
  simp only [Nat.choose_zero_right, pow_zero, zero_mul, zero_add] at h
  rw [h, binomialCdfNum, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi := mem_range.1 hi
  rw [show N - i = (N - ω) + (ω + 1 - 1 - i) by omega, pow_add]
  ring

/-- **A floor on the binomial CDF at a dyadic probability by a natural-number comparison**: for
`u ≤ 2^r`, `ω ≤ N` and `2^(r N) ≤ 2^e · v^(N - ω) · binomialCdfNumLoop N u v (ω + 1) 0 1 1 0`
with `v = 2^r - u`, `2^-e ≤ binomialCdf (u / 2^r) N ω`. -/
theorem one_div_two_pow_le_binomialCdf_of_loop {u r N ω : ℕ} (e : ℕ) (hu : u ≤ 2 ^ r)
    (hω : ω ≤ N)
    (h : 2 ^ (r * N) ≤
      2 ^ e * ((2 ^ r - u) ^ (N - ω) * binomialCdfNumLoop N u (2 ^ r - u) (ω + 1) 0 1 1 0)) :
    (1 : ℝ) / 2 ^ e ≤ binomialCdf ((u : ℝ) / 2 ^ r) N ω := by
  rw [binomialCdf_dyadic hu, ← binomialCdfNum_eq_loop u r hω] at *
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h' : ((2 ^ (r * N) : ℕ) : ℝ) ≤ ((2 ^ e * binomialCdfNum u r N ω : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  linarith

/-- **ML-DSA-65**: `2^-14 ≤ Pr[Bin(1536, 233/4096) ≤ 55]`. -/
theorem two_pow_neg_le_binomialCdf_1536_55 :
    (1 : ℝ) / 2 ^ 14 ≤ binomialCdf (233 / 4096) 1536 55 := by
  have h := one_div_two_pow_le_binomialCdf_of_loop (u := 233) (r := 12) (N := 1536) (ω := 55) 14
    (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h ⊢
  exact h

/-- **ML-DSA-87**: `2^-18 ≤ Pr[Bin(2048, 15/256) ≤ 75]`. -/
theorem two_pow_neg_le_binomialCdf_2048_75 :
    (1 : ℝ) / 2 ^ 18 ≤ binomialCdf (15 / 256) 2048 75 := by
  have h := one_div_two_pow_le_binomialCdf_of_loop (u := 15) (r := 8) (N := 2048) (ω := 75) 18
    (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h ⊢
  exact h

end GordieHowe.MLDSA
