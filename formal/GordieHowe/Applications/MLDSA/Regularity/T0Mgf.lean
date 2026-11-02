-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Floor
public import GordieHowe.Foundations.ToMathlib.ChordInterpolation

@[expose] public section

/-!
# Exponential moments of the squared `t₀` coefficient

Let `x` be the low part of Power2Round (FIPS 204 Algorithm 35) of a uniform element of `Z_q`
(`power2RoundLowCoeff`) and `y = x² / 4096² ∈ [0, 1]`. For every real `λ`,
`E exp (λ y) ≤ ∑_{m ≤ n} μ_m exp (λ m / n)` with `μ_m = E nodeHat n m y` (`expect_exp_t0_sq_le`):
the expectation of the chord interpolant of `y ↦ exp (λ y)` at the nodes `m / n`.

At `n = 8` the masses `μ_m` are explicit rationals (`t0NodeMass_eight_*`), computed in closed form:
the hat at `m / 8` is a second difference of ramps `max 0 (x² − T)` (`max_zero_one_sub_abs`), and
a ramp summed over `0 ≤ x < 4096` is a difference of Faulhaber sums `∑ x²`
(`sum_range_max_zero_sq_sub`). `expect_exp_t0_sq_le_eight` is the resulting bound with literal
masses.
-/

open Finset Real
open scoped BigOperators

namespace GordieHowe.MLDSA

/-! ### Ramp sums -/

/-- **Faulhaber's formula for squares**: `∑_{k < N} k² = (N − 1) N (2N − 1) / 6`. -/
theorem sum_range_sq_real (N : ℕ) :
    ∑ k ∈ range N, ((k : ℝ)) ^ 2 = ((N : ℝ) - 1) * N * (2 * N - 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- **A ramp summed over `k < N`**: if `c < N` and `c² ≤ T < (c + 1)²`, then
`∑_{k < N} max 0 (k² − T) = ∑_{c < k < N} (k² − T)`, in closed form. -/
theorem sum_range_max_zero_sq_sub {N c : ℕ} {T : ℝ} (hcN : c < N) (h1 : (c : ℝ) ^ 2 ≤ T)
    (h2 : T < ((c : ℝ) + 1) ^ 2) :
    ∑ k ∈ range N, max 0 ((k : ℝ) ^ 2 - T) =
      (((N : ℝ) - 1) * N * (2 * N - 1) - c * (c + 1) * (2 * c + 1)) / 6 - ((N : ℝ) - c - 1) * T := by
  rw [← sum_range_add_sum_Ico _ (show c + 1 ≤ N by omega)]
  have hlo : ∑ k ∈ range (c + 1), max 0 ((k : ℝ) ^ 2 - T) = 0 := by
    refine sum_eq_zero fun k hk => max_eq_left ?_
    have hk : (k : ℝ) ≤ c := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hk)
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hhi : ∑ k ∈ Ico (c + 1) N, max 0 ((k : ℝ) ^ 2 - T) =
      ∑ k ∈ Ico (c + 1) N, ((k : ℝ) ^ 2 - T) := by
    refine sum_congr rfl fun k hk => max_eq_right ?_
    have hk : (c : ℝ) + 1 ≤ k := by exact_mod_cast (mem_Ico.1 hk).1
    nlinarith [Nat.cast_nonneg (α := ℝ) c]
  rw [hlo, hhi, zero_add, sum_sub_distrib, sum_Ico_eq_sub _ (show c + 1 ≤ N by omega),
    sum_range_sq_real, sum_range_sq_real, sum_const, Nat.card_Ico, nsmul_eq_mul,
    Nat.cast_sub (show c + 1 ≤ N by omega)]
  push_cast
  ring

/-- A ramp with `T ≤ 0` is `k² − T` everywhere. -/
theorem sum_range_max_zero_sq_sub_of_nonpos (N : ℕ) {T : ℝ} (hT : T ≤ 0) :
    ∑ k ∈ range N, max 0 ((k : ℝ) ^ 2 - T) = ((N : ℝ) - 1) * N * (2 * N - 1) / 6 - N * T := by
  rw [sum_congr rfl fun k _ => max_eq_right (by nlinarith [sq_nonneg (k : ℝ)]),
    sum_sub_distrib, sum_range_sq_real, sum_const, card_range, nsmul_eq_mul]

/-- A ramp with `N² ≤ T` vanishes on `k < N`. -/
theorem sum_range_max_zero_sq_sub_of_le (N : ℕ) {T : ℝ} (hT : (N : ℝ) ^ 2 ≤ T) :
    ∑ k ∈ range N, max 0 ((k : ℝ) ^ 2 - T) = 0 := by
  refine sum_eq_zero fun k hk => max_eq_left ?_
  have hk : (k : ℝ) ≤ N := by exact_mod_cast (mem_range.1 hk).le
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- The ramp `max 0 (k² − T)` summed over `0 ≤ k < 4096`. -/
noncomputable def t0RampSum (T : ℝ) : ℝ := ∑ k ∈ range 4096, max 0 ((k : ℝ) ^ 2 - T)

/-! The ramp sums at `T = j · 2^21`, `j = −1, …, 9` (cut points `c_j = ⌊√(j · 2^21)⌋`). -/

/-- The ramp sum at `T = -2097152`. -/
theorem t0RampSum_neg_one : t0RampSum (-2097152) = 31488038912 := by
  rw [t0RampSum, sum_range_max_zero_sq_sub_of_nonpos _ (by norm_num)]; norm_num
/-- The ramp sum at `T = 0`. -/
theorem t0RampSum_zero : t0RampSum 0 = 22898104320 := by
  rw [t0RampSum, sum_range_max_zero_sq_sub_of_nonpos _ le_rfl]; norm_num
/-- The ramp sum at `T = 2097152`. -/
theorem t0RampSum_one : t0RampSum 2097152 = 16333885252 := by
  rw [t0RampSum, sum_range_max_zero_sq_sub (c := 1448) (by norm_num) (by norm_num) (by norm_num)]
  norm_num
/-- The ramp sum at `T = 4194304`. -/
theorem t0RampSum_two : t0RampSum 4194304 = 11446955008 := by
  rw [t0RampSum, sum_range_max_zero_sq_sub (c := 2048) (by norm_num) (by norm_num) (by norm_num)]
  norm_num
/-- The ramp sum at `T = 6291456`. -/
theorem t0RampSum_three : t0RampSum 6291456 = 7651924694 := by
  rw [t0RampSum, sum_range_max_zero_sq_sub (c := 2508) (by norm_num) (by norm_num) (by norm_num)]
  norm_num
/-- The ramp sum at `T = 8388608`. -/
theorem t0RampSum_four : t0RampSum 8388608 = 4739896392 := by
  rw [t0RampSum, sum_range_max_zero_sq_sub (c := 2896) (by norm_num) (by norm_num) (by norm_num)]
  norm_num
/-- The ramp sum at `T = 10485760`. -/
theorem t0RampSum_five : t0RampSum 10485760 = 2590139381 := by
  rw [t0RampSum, sum_range_max_zero_sq_sub (c := 3238) (by norm_num) (by norm_num) (by norm_num)]
  norm_num
/-- The ramp sum at `T = 12582912`. -/
theorem t0RampSum_six : t0RampSum 12582912 = 1121194574 := by
  rw [t0RampSum, sum_range_max_zero_sq_sub (c := 3547) (by norm_num) (by norm_num) (by norm_num)]
  norm_num
/-- The ramp sum at `T = 14680064`. -/
theorem t0RampSum_seven : t0RampSum 14680064 = 273260108 := by
  rw [t0RampSum, sum_range_max_zero_sq_sub (c := 3831) (by norm_num) (by norm_num) (by norm_num)]
  norm_num
/-- The ramp sum at `T = 16777216`. -/
theorem t0RampSum_eight : t0RampSum 16777216 = 0 := by
  rw [t0RampSum, sum_range_max_zero_sq_sub_of_le _ (by norm_num)]
/-- The ramp sum at `T = 18874368`. -/
theorem t0RampSum_nine : t0RampSum 18874368 = 0 := by
  rw [t0RampSum, sum_range_max_zero_sq_sub_of_le _ (by norm_num)]

section UniformT

open _root_.MLDSA _root_.MLDSA.Concrete LatticeCrypto

/-- `y = x² / 4096²` lies in `[0, 1]` for `x` the low part of Power2Round. -/
theorem power2RoundLowCoeff_sq_div_mem (r : Coeff) :
    0 ≤ (power2RoundLowCoeff r : ℝ) ^ 2 / 4096 ^ 2 ∧ (power2RoundLowCoeff r : ℝ) ^ 2 / 4096 ^ 2 ≤ 1 := by
  have h : |(power2RoundLowCoeff r : ℝ)| ≤ 4096 := by
    exact_mod_cast abs_power2RoundLowCoeff_le r
  refine ⟨by positivity, (div_le_one (by norm_num)).2 ?_⟩
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- **The mass of the hat at `m / n`**: `μ_m = E nodeHat n m (x² / 4096²)` for `x` the low part of
Power2Round (FIPS 204 Algorithm 35) of a uniform element of `Z_q`. -/
noncomputable def t0NodeMass (n m : ℕ) : ℝ :=
  (∑ r : Coeff, nodeHat n m ((power2RoundLowCoeff r : ℝ) ^ 2 / 4096 ^ 2)) / Fintype.card Coeff

/-- **The chord bound on `E exp (λ x² / 4096²)`**: for `x` the low part of Power2Round (FIPS 204
Algorithm 35) of a uniform element of `Z_q`, every real `λ` and `n > 0`, the expectation is at most
that of the chord interpolant of `y ↦ exp (λ y)` at the nodes `m / n`. -/
theorem expect_exp_t0_sq_le {n : ℕ} (hn : 0 < n) (lam : ℝ) :
    (∑ r : Coeff, exp (lam * ((power2RoundLowCoeff r : ℝ) ^ 2 / 4096 ^ 2))) / Fintype.card Coeff ≤
      ∑ m ∈ range (n + 1), t0NodeMass n m * exp (lam * m / n) := by
  have hle : ∑ r : Coeff, exp (lam * ((power2RoundLowCoeff r : ℝ) ^ 2 / 4096 ^ 2)) ≤
      ∑ r : Coeff, ∑ m ∈ range (n + 1),
        nodeHat n m ((power2RoundLowCoeff r : ℝ) ^ 2 / 4096 ^ 2) * exp (lam * m / n) :=
    sum_le_sum fun r _ => exp_le_sum_nodeHat_mul_exp hn (power2RoundLowCoeff_sq_div_mem r).1
      (power2RoundLowCoeff_sq_div_mem r).2 lam
  refine (div_le_div_of_nonneg_right hle (Nat.cast_nonneg _)).trans_eq ?_
  rw [sum_comm, Finset.sum_div]
  refine sum_congr rfl fun m _ => ?_
  rw [t0NodeMass, ← sum_mul, div_mul_eq_mul_div]

/-- **A sum over `Z_q` of a function of `|x|`**, `x` the low part of Power2Round: `|x| = k` for
`1 ≤ k ≤ 4095` is hit `2 · 1023` times, `k = 4096` `1023` times and `k = 0` `1024` times. -/
theorem sum_power2RoundLowCoeff_natAbs (H : ℕ → ℝ) :
    ∑ r : Coeff, H (power2RoundLowCoeff r).natAbs =
      1023 * (2 * ∑ k ∈ range 4096, H k - H 0 + H 4096) + H 0 := by
  rw [sum_power2RoundLowCoeff (fun z => H z.natAbs), Int.natAbs_zero]
  suffices key : ∑ x : Fin 8192, H (t0Coord x).natAbs = 2 * ∑ k ∈ range 4096, H k - H 0 + H 4096 by
    rw [key]
  have e : ∑ x : Fin 8192, H (t0Coord x).natAbs = ∑ i ∈ range 8192, H ((i : ℤ) - 4095).natAbs :=
    Fin.sum_univ_eq_sum_range (fun i => H ((i : ℤ) - 4095).natAbs) 8192
  rw [e, ← show 4095 + 4097 = 8192 by norm_num, sum_range_add]
  have hA : ∑ i ∈ range 4095, H ((i : ℤ) - 4095).natAbs = ∑ k ∈ range 4096, H k - H 0 := by
    rw [← sum_range_reflect, sum_range_succ' (fun k => H k), add_sub_cancel_right]
    refine sum_congr rfl fun j hj => ?_
    have hj := mem_range.1 hj
    have h : ((4095 - 1 - j : ℕ) : ℤ) - 4095 = -((j + 1 : ℕ) : ℤ) := by omega
    rw [h, Int.natAbs_neg, Int.natAbs_natCast]
  have hB : ∑ j ∈ range 4097, H (((4095 + j : ℕ) : ℤ) - 4095).natAbs =
      ∑ k ∈ range 4096, H k + H 4096 := by
    rw [sum_range_succ]
    refine congrArg₂ (· + ·) (sum_congr rfl fun j _ => ?_) ?_
    · have h : ((4095 + j : ℕ) : ℤ) - 4095 = (j : ℤ) := by omega
      rw [h, Int.natAbs_natCast]
    · have h : ((4095 + 4096 : ℕ) : ℤ) - 4095 = ((4096 : ℕ) : ℤ) := by omega
      rw [h, Int.natAbs_natCast]
  rw [hA, hB]
  ring

/-- **The hat masses at `n = 8` as ramp sums**: with `K = 2^21`, `μ_m = (1023 (2 S_m − h_m(0) +
h_m(4096)) + h_m(0)) / q`, where `h_m(k) = nodeHat 8 m (k² / 4096²)` and
`S_m = ∑_{k < 4096} h_m(k) = (R((m − 1) K) − 2 R(m K) + R((m + 1) K)) / K` for the ramp sums `R`. -/
theorem t0NodeMass_eight_eq (m : ℕ) :
    t0NodeMass 8 m = (1023 * (2 * ((t0RampSum (((m : ℝ) - 1) * 2097152) -
        2 * t0RampSum ((m : ℝ) * 2097152) + t0RampSum (((m : ℝ) + 1) * 2097152)) / 2097152) -
        nodeHat 8 m 0 + nodeHat 8 m 1) + nodeHat 8 m 0) / 8380417 := by
  have hc : (Fintype.card Coeff : ℝ) = 8380417 := by
    rw [ZMod.card]; norm_num [modulus]
  have habs : ∀ r : Coeff, (power2RoundLowCoeff r : ℝ) ^ 2 =
      (((power2RoundLowCoeff r).natAbs : ℕ) : ℝ) ^ 2 := fun r => by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have hr : ∀ a T : ℝ, max 0 ((a - T) / 2097152) = max 0 (a - T) / 2097152 := fun a T => by
    rw [← max_div_div_right (by norm_num), zero_div]
  have hterm : ∀ k : ℕ, nodeHat 8 m ((k : ℝ) ^ 2 / 4096 ^ 2) =
      (max 0 ((k : ℝ) ^ 2 - ((m : ℝ) - 1) * 2097152) - 2 * max 0 ((k : ℝ) ^ 2 - (m : ℝ) * 2097152) +
        max 0 ((k : ℝ) ^ 2 - ((m : ℝ) + 1) * 2097152)) / 2097152 := fun k => by
    rw [nodeHat, max_zero_one_sub_abs]
    have e1 : ((8 : ℕ) : ℝ) * ((k : ℝ) ^ 2 / 4096 ^ 2) - m + 1 =
        ((k : ℝ) ^ 2 - ((m : ℝ) - 1) * 2097152) / 2097152 := by push_cast; ring
    have e2 : ((8 : ℕ) : ℝ) * ((k : ℝ) ^ 2 / 4096 ^ 2) - m =
        ((k : ℝ) ^ 2 - (m : ℝ) * 2097152) / 2097152 := by push_cast; ring
    have e3 : ((8 : ℕ) : ℝ) * ((k : ℝ) ^ 2 / 4096 ^ 2) - m - 1 =
        ((k : ℝ) ^ 2 - ((m : ℝ) + 1) * 2097152) / 2097152 := by push_cast; ring
    rw [e1, e3, e2, hr, hr, hr]
    ring
  have hS : ∑ k ∈ range 4096, nodeHat 8 m ((k : ℝ) ^ 2 / 4096 ^ 2) =
      (t0RampSum (((m : ℝ) - 1) * 2097152) - 2 * t0RampSum ((m : ℝ) * 2097152) +
        t0RampSum (((m : ℝ) + 1) * 2097152)) / 2097152 := by
    rw [t0RampSum, t0RampSum, t0RampSum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib,
      Finset.sum_div]
    exact sum_congr rfl fun k _ => hterm k
  rw [t0NodeMass, hc]
  simp_rw [habs]
  rw [sum_power2RoundLowCoeff_natAbs (fun k => nodeHat 8 m ((k : ℝ) ^ 2 / 4096 ^ 2)), hS]
  norm_num

/-- The mass of the hat at `0/8`. -/
theorem t0NodeMass_eight_zero : t0NodeMass 8 0 = 517808834095/2196876034048 := by
  rw [t0NodeMass_eight_eq]
  norm_num [nodeHat, t0RampSum_neg_one, t0RampSum_zero, t0RampSum_one, t0RampSum_two, t0RampSum_three, t0RampSum_four, t0RampSum_five, t0RampSum_six, t0RampSum_seven, t0RampSum_eight, t0RampSum_nine]

/-- The mass of the hat at `1/8`. -/
theorem t0NodeMass_eight_one : t0NodeMass 8 1 = 214483308369/1098438017024 := by
  rw [t0NodeMass_eight_eq]
  norm_num [nodeHat, t0RampSum_neg_one, t0RampSum_zero, t0RampSum_one, t0RampSum_two, t0RampSum_three, t0RampSum_four, t0RampSum_five, t0RampSum_six, t0RampSum_seven, t0RampSum_eight, t0RampSum_nine]

/-- The mass of the hat at `2/8`. -/
theorem t0NodeMass_eight_two : t0NodeMass 8 2 = 558506814195/4393752068096 := by
  rw [t0NodeMass_eight_eq]
  norm_num [nodeHat, t0RampSum_neg_one, t0RampSum_zero, t0RampSum_one, t0RampSum_two, t0RampSum_three, t0RampSum_four, t0RampSum_five, t0RampSum_six, t0RampSum_seven, t0RampSum_eight, t0RampSum_nine]

/-- The mass of the hat at `3/8`. -/
theorem t0NodeMass_eight_three : t0NodeMass 8 3 = 225827764569/2196876034048 := by
  rw [t0NodeMass_eight_eq]
  norm_num [nodeHat, t0RampSum_neg_one, t0RampSum_zero, t0RampSum_one, t0RampSum_two, t0RampSum_three, t0RampSum_four, t0RampSum_five, t0RampSum_six, t0RampSum_seven, t0RampSum_eight, t0RampSum_nine]

/-- The mass of the hat at `4/8`. -/
theorem t0NodeMass_eight_four : t0NodeMass 8 4 = 779803530693/8787504136192 := by
  rw [t0NodeMass_eight_eq]
  norm_num [nodeHat, t0RampSum_neg_one, t0RampSum_zero, t0RampSum_one, t0RampSum_two, t0RampSum_three, t0RampSum_four, t0RampSum_five, t0RampSum_six, t0RampSum_seven, t0RampSum_eight, t0RampSum_nine]

/-- The mass of the hat at `5/8`. -/
theorem t0NodeMass_eight_five : t0NodeMass 8 5 = 174117721173/2196876034048 := by
  rw [t0NodeMass_eight_eq]
  norm_num [nodeHat, t0RampSum_neg_one, t0RampSum_zero, t0RampSum_one, t0RampSum_two, t0RampSum_three, t0RampSum_four, t0RampSum_five, t0RampSum_six, t0RampSum_seven, t0RampSum_eight, t0RampSum_nine]

/-- The mass of the hat at `6/8`. -/
theorem t0NodeMass_eight_six : t0NodeMass 8 6 = 635293578843/8787504136192 := by
  rw [t0NodeMass_eight_eq]
  norm_num [nodeHat, t0RampSum_neg_one, t0RampSum_zero, t0RampSum_one, t0RampSum_two, t0RampSum_three, t0RampSum_four, t0RampSum_five, t0RampSum_six, t0RampSum_seven, t0RampSum_eight, t0RampSum_nine]

/-- The mass of the hat at `7/8`. -/
theorem t0NodeMass_eight_seven : t0NodeMass 8 7 = 293945934117/4393752068096 := by
  rw [t0NodeMass_eight_eq]
  norm_num [nodeHat, t0RampSum_neg_one, t0RampSum_zero, t0RampSum_one, t0RampSum_two, t0RampSum_three, t0RampSum_four, t0RampSum_five, t0RampSum_six, t0RampSum_seven, t0RampSum_eight, t0RampSum_nine]

/-- The mass of the hat at `8/8`. -/
theorem t0NodeMass_eight_eight : t0NodeMass 8 8 = 70154445933/2196876034048 := by
  rw [t0NodeMass_eight_eq]
  norm_num [nodeHat, t0RampSum_neg_one, t0RampSum_zero, t0RampSum_one, t0RampSum_two, t0RampSum_three, t0RampSum_four, t0RampSum_five, t0RampSum_six, t0RampSum_seven, t0RampSum_eight, t0RampSum_nine]

/-- **The chord bound at the nine nodes `m / 8`**: for `x` the low part of Power2Round (FIPS 204
Algorithm 35) of a uniform element of `Z_q` and every real `λ`, `E exp (λ x² / 4096²)` is at most the
expectation of the chord interpolant of `y ↦ exp (λ y)` at the nine nodes `m / 8`, with the
explicit masses `μ_m = t0NodeMass 8 m`. -/
theorem expect_exp_t0_sq_le_eight (lam : ℝ) :
    (∑ r : Coeff, exp (lam * ((power2RoundLowCoeff r : ℝ) ^ 2 / 4096 ^ 2))) / Fintype.card Coeff ≤
      517808834095/2196876034048 * exp (0) +
      214483308369/1098438017024 * exp (lam / 8) +
      558506814195/4393752068096 * exp (lam / 4) +
      225827764569/2196876034048 * exp (3 * lam / 8) +
      779803530693/8787504136192 * exp (lam / 2) +
      174117721173/2196876034048 * exp (5 * lam / 8) +
      635293578843/8787504136192 * exp (3 * lam / 4) +
      293945934117/4393752068096 * exp (7 * lam / 8) +
      70154445933/2196876034048 * exp (lam) := by
  refine (expect_exp_t0_sq_le (n := 8) (by norm_num) lam).trans_eq ?_
  simp only [sum_range_succ, sum_range_zero, zero_add, t0NodeMass_eight_zero, t0NodeMass_eight_one,
    t0NodeMass_eight_two, t0NodeMass_eight_three, t0NodeMass_eight_four, t0NodeMass_eight_five,
    t0NodeMass_eight_six, t0NodeMass_eight_seven, t0NodeMass_eight_eight]
  push_cast
  ring_nf

end UniformT

end GordieHowe.MLDSA
