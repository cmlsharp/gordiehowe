-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime
public import GordieHowe.Foundations.Algebra.PowModLucas

@[expose] public section

/-!
# The P-256 base field

The base field `F_p` of the NIST curve P-256 (SEC 2 v2.0, §2.4.2, `secp256r1`;
`third_party/longfellow/lib/ec/p256.h`), `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, as Mathlib's
`ZMod p`.

Primality of `p` is a Pratt certificate: a Lucas certificate (`prime_of_lucasCheckB`) of `p` with
witness `6` over the factorization
`p − 1 = 2 · 3 · 5² · 17 · 257 · 641 · 1531 · 65537 · 490463 · 6700417 · q₁`, and Lucas
certificates of the factors above `10^7` in turn:

* `q₁ = 835945042244614951780389953367877943453916927241`, witness `11`, `q₁ − 1 = 2³ · 3³ · 5 · q₂`;
* `q₂ = 774023187263532362759620327192479577272145303`, witness `3`,
  `q₂ − 1 = 2 · 3² · 2411 · q₃ · q₄ · q₅`;
* `q₃ = 34282281433`, witness `17`, `q₃ − 1 = 2³ · 3 · 7 · q₆`, with
  `q₆ = 204061199`, witness `11`, `q₆ − 1 = 2 · 11 · 23 · 107 · 3769`;
* `q₄ = 11290956913871`, witness `13`, `q₄ − 1 = 2 · 5 · 17 · q₇`, with
  `q₇ = 66417393611`, witness `6`, `q₇ − 1 = 2 · 5 · 53 · 173 · 197 · 3677`;
* `q₅ = 46076956964474543`, witness `5`, `q₅ − 1 = 2 · 23 · 18169 · 78283 · 704251`.

The factors below `10^7` are prime by `norm_num`.
-/

namespace GordieHowe.P256

/-- **The P-256 base-field prime** `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`. -/
def p : ℕ := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

theorem p_eq :
    p = 115792089210356248762697446949407573530086143415290314195533631308867097853951 := by
  unfold p
  norm_num

private theorem q6_prime : Nat.Prime 204061199 :=
  prime_of_lucasCheckB (a := 11) (fs := [2, 11, 23, 107, 3769]) (by norm_num)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro q (rfl | rfl | rfl | rfl | rfl) <;> norm_num)
    (by decide +kernel)

private theorem q3_prime : Nat.Prime 34282281433 :=
  prime_of_lucasCheckB (a := 17) (fs := [2, 2, 2, 3, 7, 204061199]) (by norm_num)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact q6_prime)
    (by decide +kernel)

private theorem q7_prime : Nat.Prime 66417393611 :=
  prime_of_lucasCheckB (a := 6) (fs := [2, 5, 53, 173, 197, 3677]) (by norm_num)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro q (rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num)
    (by decide +kernel)

private theorem q4_prime : Nat.Prime 11290956913871 :=
  prime_of_lucasCheckB (a := 13) (fs := [2, 5, 17, 66417393611]) (by norm_num)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · exact q7_prime)
    (by decide +kernel)

private theorem q5_prime : Nat.Prime 46076956964474543 :=
  prime_of_lucasCheckB (a := 5) (fs := [2, 23, 18169, 78283, 704251]) (by norm_num)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro q (rfl | rfl | rfl | rfl | rfl) <;> norm_num)
    (by decide +kernel)

private theorem q2_prime : Nat.Prime 774023187263532362759620327192479577272145303 :=
  prime_of_lucasCheckB (a := 3)
    (fs := [2, 3, 3, 2411, 34282281433, 11290956913871, 46076956964474543]) (by norm_num)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact q3_prime
      · exact q4_prime
      · exact q5_prime)
    (by decide +kernel)

private theorem q1_prime : Nat.Prime 835945042244614951780389953367877943453916927241 :=
  prime_of_lucasCheckB (a := 11)
    (fs := [2, 2, 2, 3, 3, 3, 5, 774023187263532362759620327192479577272145303]) (by norm_num)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact q2_prime)
    (by decide +kernel)

/-- **`p` is prime**: a Lucas certificate with witness `6` (see the module docstring). -/
theorem p_prime : Nat.Prime p := by
  rw [p_eq]
  refine prime_of_lucasCheckB (a := 6)
    (fs := [2, 3, 5, 5, 17, 257, 641, 1531, 65537, 490463, 6700417,
      835945042244614951780389953367877943453916927241]) (by norm_num) ?_ (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro q (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact q1_prime

instance instFactPrimeP : Fact (Nat.Prime p) := ⟨p_prime⟩

instance instNeZeroP : NeZero p := ⟨p_prime.ne_zero⟩

/-- `p` is above `2`. -/
theorem two_lt_p : 2 < p := by
  rw [p_eq]
  norm_num

end GordieHowe.P256
