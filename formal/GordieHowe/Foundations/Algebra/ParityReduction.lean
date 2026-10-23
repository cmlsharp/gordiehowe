-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Tactic.LinearCombination
public import GordieHowe.Foundations.Algebra.IntLift

@[expose] public section

/-! Bounded parity reduction in a prime-characteristic field. This is the
scalar arithmetic used by grouped MACs: subtract twice a bounded quotient,
then constrain the result to be a bit. No signature scheme is involved. -/
namespace GordieHowe.ParityReduction
variable {F : Type*} [Field F]

/-- Derived remainder after subtracting twice the quotient. -/
def remainder (acc quotient : F) : F := acc - 2 * quotient

/-- The arithmetic bit constraint checked by the circuit. -/
def Holds (acc quotient : F) : Prop :=
  remainder acc quotient * (remainder acc quotient - 1) = 0

/-- The field bit constraint has exactly the two intended roots. -/
theorem holds_iff (acc quotient : F) :
    Holds acc quotient ↔ remainder acc quotient = 0 ∨ remainder acc quotient = 1 := by
  simp only [Holds, mul_eq_zero, sub_eq_zero]

/-- Bounded quotient reconstruction prevents modular wraparound. The accumulator
bound is supplied by the preceding arithmetic computation; the quotient range
comes from the lookup proof. Both bounds below the characteristic are fixed
parameter checks. -/
theorem sound {p Q n : ℕ} [CharP F p] (hn : n < p)
    (htail : 2 * (Q-1) + 1 < p) {quotient : F}
    (hq : Range.IsNatBelow Q quotient) (h : Holds (n : F) quotient) :
    remainder (n : F) quotient = (n % 2 : ℕ) := by
  rcases hq with ⟨q, hq, rfl⟩
  rcases (holds_iff (n : F) (q : F)).mp h with hzero | hone
  · have hq' : q ≤ Q - 1 := by omega
    have hbound : 2 * q + 1 < p := by omega
    have hcast : (n : F) = (2 * q : ℕ) := by
      change (n : F) - 2 * (q : F) = 0 at hzero
      rw [sub_eq_zero.mp hzero]
      norm_num
    have hnq : n = 2 * q :=
      IntLift.natCast_inj_of_lt (K := F) hn (by omega) hcast
    rw [hnq]
    simp [remainder]
  · have hq' : q ≤ Q - 1 := by omega
    have hbound : 2 * q + 1 < p := by omega
    have hcast : (n : F) = (2 * q + 1 : ℕ) := by
      change (n : F) - 2 * (q : F) = 1 at hone
      calc
        (n : F) = 2 * (q : F) + 1 := (sub_eq_iff_eq_add'.mp hone)
        _ = ((2 * q + 1 : ℕ) : F) := by push_cast; ring
    have hnq : n = 2 * q + 1 :=
      IntLift.natCast_inj_of_lt (K := F) hn (by omega) hcast
    rw [hnq]
    simp [remainder]

/-- The honest quotient leaves the integer parity as the derived remainder. -/
theorem remainder_div_two (n : ℕ) :
    remainder (n : F) (n / 2 : ℕ) = (n % 2 : ℕ) := by
  change (n : F) - 2 * ((n / 2 : ℕ) : F) = ((n % 2 : ℕ) : F)
  have h := congrArg (fun k : ℕ => (k : F)) (Nat.mod_add_div n 2)
  push_cast at h
  rw [add_comm] at h
  exact (sub_eq_iff_eq_add').mpr h.symm

/-- The honest quotient always satisfies the bit constraint; a separate bound
ensures its digits fit the lookup table. -/
theorem complete (n : ℕ) : Holds (n : F) (n / 2 : ℕ) := by
  rw [Holds, remainder_div_two]
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hmod with hmod | hmod <;> simp [hmod]

/-- The honest quotient fits the fixed reconstruction interval. -/
theorem quotient_below {n Q : ℕ} (hn : n < 2 * Q) :
    Range.IsNatBelow Q ((n / 2 : ℕ) : F) := by
  refine ⟨n / 2, ?_, rfl⟩
  omega

/-- A final quotient requested directly as a division, rather than
reconstructed from limbs and asserted Boolean: if `(x - y) * 2⁻¹` is the cast
of a natural below `Q`, and `x`, `y` are casts of naturals `a`, `b` with `a`
and `b + 2 * (Q - 1)` below the characteristic, the difference is exactly
twice that natural, on the naturals. `h2` is a `field` fact: `2` embeds below
the characteristic. -/
theorem eq_two_mul_of_needle_div {p Q a b : ℕ} [CharP F p] (ha : a < p)
    (h2 : 2 < p) (hbound : b + 2 * (Q - 1) < p) {m : F}
    (hm : Range.IsNatBelow Q m) (h : ((a : F) - b) * (2 : F)⁻¹ = m) :
    ∃ c, c < Q ∧ a = b + 2 * c := by
  obtain ⟨c, hc, rfl⟩ := hm
  refine ⟨c, hc, ?_⟩
  have h2ne : (2 : F) ≠ 0 := by
    intro hz
    have hz' : ((2 : ℕ) : F) = ((0 : ℕ) : F) := by simpa using hz
    have := IntLift.natCast_inj_of_lt (K := F) (p := p) h2 (by omega) hz'
    omega
  rw [← div_eq_mul_inv] at h
  have hx : (a : F) - b = (c : F) * 2 := (div_eq_iff h2ne).mp h
  have hcast : (a : F) = ((b + 2 * c : ℕ) : F) := by
    push_cast
    linear_combination hx
  exact IntLift.natCast_inj_of_lt (K := F) ha (by omega) hcast

end GordieHowe.ParityReduction
