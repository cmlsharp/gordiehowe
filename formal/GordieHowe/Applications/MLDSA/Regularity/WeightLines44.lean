-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Flatten

@[expose] public section

/-!
# Lines below the binomial CDF at ML-DSA-44

At ML-DSA-44 (FIPS 204, Table 1: `ω = 80`) the hint fraction bounds are taken in `[0, x₀]` with
`x₀ = 21/25`. This file proves four lines `α - σ N x₀` below the binomial CDF
`B_N = Pr[Bin(N, 21/25) ≤ 80]` at every `N`, so the vertex reduction
`sub_sum_le_poissonBinomialCdf` turns each into `α - σ ∑_i p_i ≤ Pr_p[X ≤ 80]` for
`p_i ∈ [0, 21/25]`.

* `sub_le_binomialCdf_line_zero_mldsa44`: `(α, σ) = (1, 1/90)`, from upper-tail checks at
  `N = 81..107` (`B_N = 1` for `N ≤ 80`, and the line is negative for `N ≥ 108`).
* `sub_le_binomialCdf_line_one_mldsa44`, `_two_mldsa44`, `_three_mldsa44`: three lines with
  small intercepts for large hint means, from `α ≤ B_{N_a}` and the checks at `N_a < N < N_z`
  (`N_a = 156, 174, 257`, `N_z = 162, 180, 263`), each with the single term
  `C(N, 80) x₀^80 (1 - x₀)^(N - 80)` of `B_N`, and `α - σ N_z x₀ ≤ 0`
  (`sub_le_binomialCdf_of_checks`).

The binomial coefficients are evaluated as `descFactorial N j / j!`
(`Nat.choose_eq_descFactorial_div_factorial`) by `norm_num`.
-/

open Finset

namespace GordieHowe.MLDSA.Regularity

open GordieHowe.MLDSA

/-- **The slope line** `1 - N x₀ / 90` at `x₀ = 21/25`, `ω = 80`: below `Pr[Bin(N, 21/25) ≤ 80]`
for every `N`. The checks at `N = 81..107` bound the upper tail
`∑_{80 < j ≤ N} C(N, j) (21/25)^j (4/25)^(N - j)` (`binomialCdf_add_tail`) by `N x₀ / 90`. -/
theorem sub_le_binomialCdf_line_zero_mldsa44 (N : ℕ) :
    1 - 1 / 90 * N * (21 / 25) ≤ binomialCdf (21 / 25) N 80 := by
  refine sub_le_binomialCdf_of_checks (Na := 80) (Nz := 108) (by norm_num) (by norm_num)
    (by norm_num) (binomialCdf_self _ _).ge (fun N h1 h2 => ?_) (by norm_num) N
  have ht := binomialCdf_add_tail (21 / 25 : ℝ) (le_of_lt h1)
  interval_cases N <;>
  · simp only [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.choose_eq_descFactorial_div_factorial] at ht
    norm_num at ht ⊢
    linarith

/-- **The line `α - σ N x₀` with `α = 11675311 / 10 ^ 28` and `σ = 8608199 / 10 ^ 30`** at
`x₀ = 21/25`, `ω = 80`: below `Pr[Bin(N, 21/25) ≤ 80]` for every `N`. The checks at
`N = 156..161` use the single term `j = 80` of the CDF
(`choose_mul_pow_mul_pow_le_binomialCdf`); the line is negative from `N = 162`. -/
theorem sub_le_binomialCdf_line_one_mldsa44 (N : ℕ) :
    11675311 / 10 ^ 28 - 8608199 / 10 ^ 30 * N * (21 / 25) ≤
      binomialCdf (21 / 25) N 80 := by
  have hterm := fun N => choose_mul_pow_mul_pow_le_binomialCdf (x := 21 / 25) (by norm_num)
    (by norm_num) (le_refl 80) N
  refine sub_le_binomialCdf_of_checks (Na := 156) (Nz := 162) (by norm_num) (by norm_num)
    (by norm_num) (le_trans ?_ (hterm 156)) (fun N h1 h2 => ?_) (by norm_num) N
  · rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num
  · interval_cases N <;>
    · refine le_trans ?_ (hterm _)
      rw [Nat.choose_eq_descFactorial_div_factorial]
      norm_num

/-- **The line `α - σ N x₀` with `α = 6150879 / 10 ^ 37` and `σ = 40815103 / 10 ^ 40`** at
`x₀ = 21/25`, `ω = 80`: below `Pr[Bin(N, 21/25) ≤ 80]` for every `N`. The checks at
`N = 174..179` use the single term `j = 80` of the CDF
(`choose_mul_pow_mul_pow_le_binomialCdf`); the line is negative from `N = 180`. -/
theorem sub_le_binomialCdf_line_two_mldsa44 (N : ℕ) :
    6150879 / 10 ^ 37 - 40815103 / 10 ^ 40 * N * (21 / 25) ≤
      binomialCdf (21 / 25) N 80 := by
  have hterm := fun N => choose_mul_pow_mul_pow_le_binomialCdf (x := 21 / 25) (by norm_num)
    (by norm_num) (le_refl 80) N
  refine sub_le_binomialCdf_of_checks (Na := 174) (Nz := 180) (by norm_num) (by norm_num)
    (by norm_num) (le_trans ?_ (hterm 174)) (fun N h1 h2 => ?_) (by norm_num) N
  · rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num
  · interval_cases N <;>
    · refine le_trans ?_ (hterm _)
      rw [Nat.choose_eq_descFactorial_div_factorial]
      norm_num

/-- **The line `α - σ N x₀` with `α = 32703147 / 10 ^ 87` and `σ = 14842721 / 10 ^ 89`** at
`x₀ = 21/25`, `ω = 80`: below `Pr[Bin(N, 21/25) ≤ 80]` for every `N`. The checks at
`N = 257..262` use the single term `j = 80` of the CDF
(`choose_mul_pow_mul_pow_le_binomialCdf`); the line is negative from `N = 263`. -/
theorem sub_le_binomialCdf_line_three_mldsa44 (N : ℕ) :
    32703147 / 10 ^ 87 - 14842721 / 10 ^ 89 * N * (21 / 25) ≤
      binomialCdf (21 / 25) N 80 := by
  have hterm := fun N => choose_mul_pow_mul_pow_le_binomialCdf (x := 21 / 25) (by norm_num)
    (by norm_num) (le_refl 80) N
  refine sub_le_binomialCdf_of_checks (Na := 257) (Nz := 263) (by norm_num) (by norm_num)
    (by norm_num) (le_trans ?_ (hterm 257)) (fun N h1 h2 => ?_) (by norm_num) N
  · rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num
  · interval_cases N <;>
    · refine le_trans ?_ (hterm _)
      rw [Nat.choose_eq_descFactorial_div_factorial]
      norm_num

end GordieHowe.MLDSA.Regularity
