-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import LatticeCrypto.MLDSA.Concrete.NTT
import all LatticeCrypto.MLDSA.Concrete.NTT

@[expose] public section

/-!
# Bit reversal on `Fin (2^m)`

`host_ntt::NegacyclicPlan` returns frequencies in bit-reversed order, so an NTT-form public
input to `native_linear::Relation` (`PublicForm::kNtt`, `lib/circuits/ntt/native_linear.h`) holds
the evaluations at `ψ^(2·brv(k) + 1)`. The relation's reversal trick reads the spectrum of
`a(x⁻¹)` as `d[n - 1 - k]`: inversion sends the point `ψ^(2·brv(k) + 1)` to
`ψ^(2·brv(n - 1 - k) + 1)`, because `brv(n - 1 - k) = n - 1 - brv(k)` (`bitRev_rev`) and so
`(2·brv(k) + 1) + (2·brv(n - 1 - k) + 1) = 2n` (`two_mul_bitRev_rev_add`).

`bitRev 8` is the vendored FIPS 204 `brv` on eight bits (`bitRev_eight`).
-/

namespace GordieHowe

/-- Reverse the low `m` bits of `k`: the lowest bit becomes bit `m - 1`. -/
def bitRevNat : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, k => k % 2 * 2 ^ m + bitRevNat m (k / 2)

theorem bitRevNat_lt (m k : ℕ) : bitRevNat m k < 2 ^ m := by
  induction m generalizing k with
  | zero => simp [bitRevNat]
  | succ m ih =>
    have h := ih (k / 2)
    have hk := Nat.mod_lt k (show 0 < 2 by norm_num)
    have : k % 2 * 2 ^ m ≤ 2 ^ m := by
      calc k % 2 * 2 ^ m ≤ 1 * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ m := one_mul _
    simp only [bitRevNat, pow_succ]
    omega

theorem bitRevNat_injOn {m k₁ k₂ : ℕ} (h₁ : k₁ < 2 ^ m) (h₂ : k₂ < 2 ^ m)
    (h : bitRevNat m k₁ = bitRevNat m k₂) : k₁ = k₂ := by
  induction m generalizing k₁ k₂ with
  | zero => simp at h₁ h₂; omega
  | succ m ih =>
    simp only [bitRevNat] at h
    have l₁ := bitRevNat_lt m (k₁ / 2)
    have l₂ := bitRevNat_lt m (k₂ / 2)
    have hmod : k₁ % 2 = k₂ % 2 := by
      rcases Nat.mod_two_eq_zero_or_one k₁ with a | a <;>
        rcases Nat.mod_two_eq_zero_or_one k₂ with b | b <;> rw [a, b] at h ⊢ <;> omega
    have hdiv : k₁ / 2 = k₂ / 2 := by
      rw [pow_succ] at h₁ h₂
      exact ih (by omega) (by omega) (by rw [hmod] at h; omega)
    omega

/-- Complementing the bits commutes with reversing them. -/
theorem bitRevNat_compl {m k : ℕ} (hk : k < 2 ^ m) :
    bitRevNat m (2 ^ m - 1 - k) = 2 ^ m - 1 - bitRevNat m k := by
  induction m generalizing k with
  | zero => simp [bitRevNat]
  | succ m ih =>
    have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
    have hk' : k / 2 < 2 ^ m := by rw [pow_succ] at hk; omega
    have hmod : (2 ^ (m + 1) - 1 - k) % 2 = 1 - k % 2 := by rw [pow_succ]; omega
    have hdiv : (2 ^ (m + 1) - 1 - k) / 2 = 2 ^ m - 1 - k / 2 := by rw [pow_succ]; omega
    have hlt := bitRevNat_lt m (k / 2)
    rw [bitRevNat, bitRevNat, hmod, hdiv, ih hk', pow_succ]
    rw [pow_succ] at hk
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;> omega

/-- Bit reversal as a permutation of `Fin (2^m)`. -/
noncomputable def bitRev (m : ℕ) : Equiv.Perm (Fin (2 ^ m)) :=
  Equiv.ofBijective (fun k => ⟨bitRevNat m k, bitRevNat_lt m k⟩)
    (Finite.injective_iff_bijective.mp fun a b h =>
      Fin.ext (bitRevNat_injOn a.isLt b.isLt (Fin.mk.inj_iff.mp h)))

@[simp] theorem bitRev_val (m : ℕ) (k : Fin (2 ^ m)) : (bitRev m k : ℕ) = bitRevNat m k := rfl

/-- `brv(n - 1 - k) = n - 1 - brv(k)`. -/
theorem bitRev_rev (m : ℕ) (k : Fin (2 ^ m)) : bitRev m k.rev = (bitRev m k).rev := by
  apply Fin.ext
  have hk := k.isLt
  have hr := bitRevNat_lt m k
  rw [bitRev_val, Fin.val_rev, Fin.val_rev, bitRev_val,
    show 2 ^ m - (k.val + 1) = 2 ^ m - 1 - k.val by omega, bitRevNat_compl hk]
  omega

/-- The odd exponents of `k` and `n - 1 - k` sum to `2n`, so their points are inverse to each
other: `-(2·brv(k) + 1) ≡ 2·brv(n - 1 - k) + 1 (mod 2n)`. -/
theorem two_mul_bitRev_rev_add (m : ℕ) (k : Fin (2 ^ m)) :
    (2 * (bitRev m k.rev : ℕ) + 1) + (2 * (bitRev m k : ℕ) + 1) = 2 * 2 ^ m := by
  rw [bitRev_rev, Fin.val_rev]
  have := (bitRev m k).isLt
  omega

/-- `bitRev 8` is the vendored FIPS 204 eight-bit reversal `brv`. -/
theorem bitRev_eight (k : Fin 256) : (bitRev 8 k : ℕ) = _root_.MLDSA.Concrete.bitRev8 k := by
  rw [bitRev_val]
  revert k
  decide +kernel

end GordieHowe
