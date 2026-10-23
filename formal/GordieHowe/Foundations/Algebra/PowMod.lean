-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# Kernel-reducible modular exponentiation

`(a : ZMod m) ^ e` unfolds through `Monoid.npow`, which recurses unary in
`e`; the kernel cannot check `a ^ e = 1` this way for a multi-hundred-bit
exponent. This file defines modular exponentiation on `ℕ` by binary
recursion, structural on a fuel parameter so the kernel never has to unfold
`WellFounded.fix` or `Acc.rec`, and proves it agrees with `ZMod`
exponentiation. `decide` on a `powMod` value then discharges an order
hypothesis at a depth linear in the bit length of the exponent, with every
step's multiplication and reduction done by the kernel's native `Nat`
arithmetic.

This is reused by every Lucas-type primality or root-of-unity order certificate in the project;
state new order facts against `powMod`, not against `ZMod` exponentiation directly.
-/

/-- Binary modular exponentiation, with a fuel parameter consumed one
halving step at a time regardless of its own size. `powModAux b m fuel e`
computes `b ^ e % m` whenever `fuel` is large enough (`powModAux_eq_mod`);
`powMod` below always supplies enough fuel by taking `fuel := e`. -/
def GordieHowe.powModAux (b m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % m
  | _ + 1, 0 => 1 % m
  | fuel + 1, e + 1 =>
    let half := GordieHowe.powModAux b m fuel ((e + 1) / 2)
    let sq := half * half % m
    if (e + 1) % 2 = 0 then sq else sq * b % m

theorem GordieHowe.powModAux_eq_mod (b m : ℕ) : ∀ fuel e, e ≤ fuel → GordieHowe.powModAux b m fuel e = b ^ e % m
  | 0, e, he => by
    have he0 : e = 0 := Nat.le_zero.mp he
    subst he0
    simp [GordieHowe.powModAux]
  | _ + 1, 0, _ => by simp [GordieHowe.powModAux]
  | fuel + 1, e + 1, he => by
    have hfuel : (e + 1) / 2 ≤ fuel := by omega
    have hstep := GordieHowe.powModAux_eq_mod b m fuel ((e + 1) / 2) hfuel
    show
        (let half := GordieHowe.powModAux b m fuel ((e + 1) / 2)
          let sq := half * half % m
          if (e + 1) % 2 = 0 then sq else sq * b % m) =
        b ^ (e + 1) % m
    simp only [hstep]
    set k := (e + 1) / 2 with hk
    have hsq : b ^ k % m * (b ^ k % m) % m = b ^ (2 * k) % m := by
      rw [← Nat.mul_mod, two_mul, pow_add]
    have hodd : b ^ (2 * k) % m * b % m = b ^ (2 * k + 1) % m := by
      rw [pow_succ, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    have hmod : (e + 1) % 2 = 0 ∨ (e + 1) % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · have he1 : e + 1 = 2 * k := by omega
      simp only [h0, ite_true, hsq]
      rw [he1]
    · have he1 : e + 1 = 2 * k + 1 := by omega
      simp only [h1, one_ne_zero, ite_false, hsq]
      rw [he1]
      exact hodd

/-- Modular exponentiation on `ℕ`, computed by binary recursion so the
kernel checks it in a number of steps linear in the bit length of `e`. -/
def GordieHowe.powMod (b e m : ℕ) : ℕ := GordieHowe.powModAux b m e e

theorem GordieHowe.powMod_eq_mod (b e m : ℕ) : GordieHowe.powMod b e m = b ^ e % m :=
  GordieHowe.powModAux_eq_mod b m e e le_rfl

/-- `powMod` computes `ZMod` exponentiation: a `decide` on `powMod` values
transports to a fact about `(b : ZMod m) ^ e`. -/
theorem GordieHowe.powMod_eq_pow (b e m : ℕ) : (GordieHowe.powMod b e m : ZMod m) = (b : ZMod m) ^ e := by
  rw [GordieHowe.powMod_eq_mod, ZMod.natCast_mod, Nat.cast_pow]

/-- A `powMod` value of exactly `1` transports to a `ZMod` order-one fact;
this is the direction a Lucas certificate's `a ^ (p - 1) = 1` uses. -/
theorem GordieHowe.powMod_eq_one_of_eq {b e m : ℕ} (h : GordieHowe.powMod b e m = 1) : (b : ZMod m) ^ e = 1 := by
  rw [← GordieHowe.powMod_eq_pow, h, Nat.cast_one]

/-- A `powMod` value other than `1` transports to a `ZMod` disequality; this
is the direction a Lucas certificate's `a ^ ((p - 1) / q) ≠ 1` uses. Needs
`1 < m` so that `1` and the (already reduced) `powMod` value are equal as
naturals whenever their images in `ZMod m` agree. -/
theorem GordieHowe.powMod_ne_one_of_ne {b e m : ℕ} (h1 : 1 < m) (h : GordieHowe.powMod b e m ≠ 1) :
    (b : ZMod m) ^ e ≠ 1 := by
  rw [← GordieHowe.powMod_eq_pow]
  intro hcontra
  apply h
  have hc : (GordieHowe.powMod b e m : ZMod m) = ((1 : ℕ) : ZMod m) := by rw [hcontra, Nat.cast_one]
  have heq := (ZMod.natCast_eq_natCast_iff' (GordieHowe.powMod b e m) 1 m).mp hc
  have hlt : GordieHowe.powMod b e m < m := by rw [GordieHowe.powMod_eq_mod]; exact Nat.mod_lt _ (by omega)
  rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt h1] at heq
