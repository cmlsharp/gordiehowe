-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.RingTheory.Norm.Basic

@[expose] public section

/-!
# Irreducibility of `X^n − C a` at a composite `n`

Mathlib's Kummer-extension file proves `X^n − C a` irreducible for any odd `n`
(`X_pow_sub_C_irreducible_iff_forall_prime_of_odd`) and at any prime exponent
(`X_pow_sub_C_irreducible_of_prime`, `2` included), leaving even composite `n` as a TODO.

This file proves the sufficiency direction of Capelli's theorem at every `n`, over any field, in the
slightly stronger form that needs no `-4 K^4` term (`X_pow_sub_C_irreducible_of_forall_prime`):
`X^n − C a` is irreducible when `a` is not an `r`-th power for any prime `r ∣ n`, and, if `4 ∣ n`,
`-a` is not a square. The induction peels one prime `r` at a time
(`X_pow_mul_prime_sub_C_irreducible`): in `K⟮x⟯` with `x ^ m = a`, an `r`-th root `b` of `x` has
norm `N b` with `(N b) ^ r = N x = (-1) ^ m * -a`.

Over a finite field of order `q` the hypotheses become modular exponentiations
(`FiniteField.X_pow_sub_C_irreducible_of_pow_ne_one`): every prime `r ∣ n` divides `q − 1` with
`a ^ ((q − 1) / r) ≠ 1`, and `q ≡ 1 (mod 4)` when `4 ∣ n`. The same statement in terms of the order
of `a` (Serret's criterion, sufficiency) is `FiniteField.X_pow_sub_C_irreducible_of_orderOf`. A
`powMod` certificate (`GordieHowe/Foundations/Algebra/PowMod.lean`) checks each exponentiation by `decide +kernel`.

The two special shapes `n = 2 * p` (`p` an odd prime) and `n = 4` are corollaries, kept by name
for their users. Candidate for upstreaming next to `Mathlib.FieldTheory.KummerExtension`'s
`X_pow_sub_C_irreducible_of_odd`.
-/

open Polynomial

section General

variable {K : Type*} [Field K]

/-- One prime step of the Capelli induction: if `X ^ m − C a` is irreducible and no `b : K`
has `b ^ r = (-1) ^ m * -a` (the norm of a root of `X ^ m − C a`), then `X ^ (r * m) − C a` is
irreducible. In `K⟮x⟯`, `x ^ m = a`, an `r`-th root `b` of `x` would give
`(N b) ^ r = N x = (-1) ^ m * -a` (`Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`). -/
theorem X_pow_mul_prime_sub_C_irreducible {m r : ℕ} (hr : r.Prime) {a : K}
    (hm : Irreducible (X ^ m - C a)) (h : ∀ b : K, b ^ r ≠ (-1) ^ m * -a) :
    Irreducible (X ^ (r * m) - C a) := by
  have hm0 : m ≠ 0 := fun e => not_irreducible_C (1 - a)
    (by simpa only [e, pow_zero, ← C.map_one, ← map_sub] using hm)
  refine X_pow_mul_sub_C_irreducible hm ?_
  intro E _ _ x hx
  have hint : IsIntegral K x := by
    by_contra hni
    exact X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hm0) a (hx.symm.trans (minpoly.eq_zero hni))
  refine X_pow_sub_C_irreducible_of_prime hr ?_
  intro b hb
  apply h (Algebra.norm K b)
  have hpb := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
    (IntermediateField.adjoin.powerBasis hint)
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
    IntermediateField.minpoly_gen, hx, natDegree_X_pow_sub_C] at hpb
  rw [← map_pow, hb, hpb]
  simp [coeff_sub, coeff_X_pow, coeff_C, Ne.symm hm0]

/-- **Capelli's theorem, sufficiency** (in the form without the `-4 K^4` term): over any field,
`X ^ n − C a` with `n ≠ 0` is irreducible if `a` is not an `r`-th power for any prime `r ∣ n`
and, when `4 ∣ n`, `-a` is not a square. -/
theorem X_pow_sub_C_irreducible_of_forall_prime {n : ℕ} (hn : n ≠ 0) {a : K}
    (hp : ∀ r : ℕ, r.Prime → r ∣ n → ∀ b : K, b ^ r ≠ a)
    (h4 : 4 ∣ n → ∀ b : K, b ^ 2 ≠ -a) : Irreducible (X ^ n - C a) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases eq_or_ne n 1 with rfl | hn1
  · rw [pow_one]
    exact irreducible_X_sub_C a
  obtain ⟨r, hr, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
  have hm0 : m ≠ 0 := right_ne_zero_of_mul hn
  have hlt : m < r * m := lt_mul_left (Nat.pos_of_ne_zero hm0) hr.one_lt
  have hm := ih m hlt hm0 (fun s hs hsm => hp s hs (Dvd.dvd.mul_left hsm r))
    (fun h => h4 (Dvd.dvd.mul_left h r))
  refine X_pow_mul_prime_sub_C_irreducible hr hm ?_
  intro b hb
  rcases Nat.even_or_odd m with hme | hmo
  · rw [hme.neg_one_pow, one_mul] at hb
    rcases hr.eq_two_or_odd' with rfl | hro
    · obtain ⟨k, rfl⟩ := hme
      exact h4 ⟨k, by ring⟩ b hb
    · exact hp r hr (dvd_mul_right r m) (-b) (by rw [hro.neg_pow, hb, neg_neg])
  · rw [hmo.neg_one_pow, neg_one_mul, neg_neg] at hb
    exact hp r hr (dvd_mul_right r m) b hb

/-- `X ^ (2 * p) − C a` is irreducible over a field `K` where `p` is an odd prime, `a` is not a
square and not a `p`-th power in `K` (`X_pow_sub_C_irreducible_of_forall_prime`: the primes of
`2 * p` are `2` and `p`, and `4 ∤ 2 * p`). -/
theorem irreducible_X_pow_two_mul_sub_C_of_not_sq_not_pow {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) {a : K} (ha2 : ∀ b : K, b ^ 2 ≠ a) (hap : ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ (2 * p) - C a) := by
  refine X_pow_sub_C_irreducible_of_forall_prime (mul_ne_zero two_ne_zero hp.ne_zero) ?_ ?_
  · intro r hr hrd
    rcases (Nat.Prime.dvd_mul hr).mp hrd with h | h
    · rwa [(Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h]
    · rwa [(Nat.prime_dvd_prime_iff_eq hr hp).mp h]
  · rintro ⟨k, hk⟩
    obtain ⟨j, rfl⟩ := hpodd
    omega

/-- `X ^ 4 − C a` is irreducible over a field `K` where neither `a` nor `-a` is a square
(`X_pow_sub_C_irreducible_of_forall_prime` at `n = 4`, whose only prime is `2`). -/
theorem irreducible_X_pow_four_sub_C_of_not_sq {a : K}
    (ha : ∀ b : K, b ^ 2 ≠ a) (hna : ∀ b : K, b ^ 2 ≠ -a) : Irreducible (X ^ 4 - C a) := by
  refine X_pow_sub_C_irreducible_of_forall_prime (by norm_num) ?_ fun _ => hna
  intro r hr hrd
  have h2 : r ∣ 2 := hr.dvd_of_dvd_pow (n := 2) (by norm_num at hrd ⊢; exact hrd)
  rwa [(Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2]

end General

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F]

/-- In a finite field of order `q`: if `r ∣ q − 1` and `a ≠ 0` has `a ^ ((q − 1) / r) ≠ 1`,
then `a` is not an `r`-th power. An `r`-th root `b` would give
`a ^ ((q − 1) / r) = b ^ (q − 1) = 1` (`FiniteField.pow_card_sub_one_eq_one`). -/
theorem pow_ne_of_pow_card_sub_one_div_ne_one {r : ℕ} (hr : r ∣ Fintype.card F - 1) {a : F}
    (ha0 : a ≠ 0) (ha : a ^ ((Fintype.card F - 1) / r) ≠ 1) (b : F) : b ^ r ≠ a := by
  intro hb
  apply ha
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact ha (by rw [Nat.div_zero, pow_zero])
  have hb0 : b ≠ 0 := fun h => ha0 (by rw [← hb, h, zero_pow hr0])
  rw [← hb, ← pow_mul, Nat.mul_div_cancel' hr]
  exact pow_card_sub_one_eq_one b hb0

/-- In a finite field of order `q`: if `r ∣ orderOf a` and `r ∤ (q − 1) / orderOf a`, then
`r ∣ q − 1` and `a ^ ((q − 1) / r) ≠ 1`. -/
theorem pow_card_sub_one_div_ne_one_of_orderOf {r : ℕ} {a : F} (hro : r ∣ orderOf a)
    (hrq : ¬ r ∣ (Fintype.card F - 1) / orderOf a) :
    a ≠ 0 ∧ r ∣ Fintype.card F - 1 ∧ a ^ ((Fintype.card F - 1) / r) ≠ 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [orderOf_zero, Nat.div_zero] at hrq
    exact hrq (dvd_zero r)
  have hoq : orderOf a ∣ Fintype.card F - 1 :=
    orderOf_dvd_of_pow_eq_one (pow_card_sub_one_eq_one a ha0)
  refine ⟨ha0, hro.trans hoq, fun h => hrq ?_⟩
  exact Nat.dvd_div_of_mul_dvd (by
    rw [mul_comm]
    exact Nat.mul_dvd_of_dvd_div (hro.trans hoq) (orderOf_dvd_of_pow_eq_one h))

/-- **Binomial irreducibility over a finite field of order `q`**, certificate form: `X ^ n − C a`
with `n ≠ 0`, `a ≠ 0` is irreducible if every prime `r ∣ n` divides `q − 1` with
`a ^ ((q − 1) / r) ≠ 1`, and `q ≡ 1 (mod 4)` when `4 ∣ n`. -/
theorem X_pow_sub_C_irreducible_of_pow_ne_one {n : ℕ} (hn : n ≠ 0) {a : F} (ha0 : a ≠ 0)
    (hp : ∀ r : ℕ, r.Prime → r ∣ n →
      r ∣ Fintype.card F - 1 ∧ a ^ ((Fintype.card F - 1) / r) ≠ 1)
    (h4 : 4 ∣ n → Fintype.card F % 4 = 1) : Irreducible (X ^ n - C a) := by
  have hsq : 2 ∣ n → ∀ b : F, b ^ 2 ≠ a := fun h2 =>
    pow_ne_of_pow_card_sub_one_div_ne_one (hp 2 Nat.prime_two h2).1 ha0 (hp 2 Nat.prime_two h2).2
  refine X_pow_sub_C_irreducible_of_forall_prime hn
    (fun r hr hrn => pow_ne_of_pow_card_sub_one_div_ne_one (hp r hr hrn).1 ha0 (hp r hr hrn).2) ?_
  intro h4n b hb
  obtain ⟨c, hc⟩ := (isSquare_neg_one_iff (F := F)).mpr (by rw [h4 h4n]; decide)
  apply hsq ((Nat.dvd_of_mod_eq_zero (by norm_num)).trans h4n) (b * c)
  rw [mul_pow, hb, sq, ← hc]
  ring

/-- **Serret's criterion over a finite field of order `q`, sufficiency**: `X ^ n − C a` with
`n ≠ 0` is irreducible if every prime `r ∣ n` divides `orderOf a` and does not divide
`(q − 1) / orderOf a`, and `q ≡ 1 (mod 4)` when `4 ∣ n`. -/
theorem X_pow_sub_C_irreducible_of_orderOf {n : ℕ} (hn : n ≠ 0) {a : F}
    (hp : ∀ r : ℕ, r.Prime → r ∣ n → r ∣ orderOf a ∧ ¬ r ∣ (Fintype.card F - 1) / orderOf a)
    (h4 : 4 ∣ n → Fintype.card F % 4 = 1) : Irreducible (X ^ n - C a) := by
  refine X_pow_sub_C_irreducible_of_forall_prime hn (fun r hr hrn => ?_) ?_
  · obtain ⟨ha0, hrq, ha⟩ := pow_card_sub_one_div_ne_one_of_orderOf (hp r hr hrn).1 (hp r hr hrn).2
    exact pow_ne_of_pow_card_sub_one_div_ne_one hrq ha0 ha
  · intro h4n b hb
    have h2 : 2 ∣ n := (Nat.dvd_of_mod_eq_zero (by norm_num)).trans h4n
    obtain ⟨ha0, hrq, ha⟩ := pow_card_sub_one_div_ne_one_of_orderOf (hp 2 Nat.prime_two h2).1
      (hp 2 Nat.prime_two h2).2
    obtain ⟨c, hc⟩ := (isSquare_neg_one_iff (F := F)).mpr (by rw [h4 h4n]; decide)
    apply pow_ne_of_pow_card_sub_one_div_ne_one hrq ha0 ha (b * c)
    rw [mul_pow, hb, sq, ← hc]
    ring

end FiniteField

/-- Over `ZMod q` for `q` prime: if `p ∣ q − 1` and `a` is a nonzero element whose
`((q − 1) / p)`-th power is not `1`, then `a` is not a `p`-th power
(`FiniteField.pow_ne_of_pow_card_sub_one_div_ne_one` at `Fintype.card (ZMod q) = q`). -/
theorem not_isNthPow_of_pow_ne_one {q p : ℕ} [Fact q.Prime] (hpq : p ∣ q - 1) {a : ZMod q}
    (ha0 : a ≠ 0) (ha : a ^ ((q - 1) / p) ≠ 1) : ∀ b : ZMod q, b ^ p ≠ a :=
  FiniteField.pow_ne_of_pow_card_sub_one_div_ne_one (by rwa [ZMod.card]) ha0 (by rwa [ZMod.card])
