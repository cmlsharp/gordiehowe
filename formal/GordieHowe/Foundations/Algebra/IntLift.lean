-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Foundations.ToMathlib.IntCast

@[expose] public section

/-!
# From field identities to identities on the naturals

Every integer bound in the circuits' soundness proofs is used the same way: two sides of a field
equation are casts of naturals known to lie below the characteristic, so the equation holds on the
naturals. These are the lemmas that make that step, stated on `IsNatBelow` so the range gadgets can
chain them without unpacking witnesses.
-/

namespace GordieHowe.IntLift

variable {K : Type*} [Field K] {p : ℕ} [CharP K p]

/-- Casts of naturals below the characteristic are equal only if the naturals are. -/
theorem natCast_inj_of_lt {a b : ℕ} (ha : a < p) (hb : b < p) (h : (a : K) = b) : a = b := by
  exact CharP.natCast_injOn_Iio K p ha hb h

/-- A table no larger than the characteristic embeds into the field. -/
theorem finCast_injective {T : ℕ} (hT : T ≤ p) : Function.Injective (fun j : Fin T => (j : K)) :=
  fun i j h => Fin.ext (natCast_inj_of_lt (i.isLt.trans_le hT) (j.isLt.trans_le hT) h)

/-- A field equation `x + y = z` between casts of naturals whose sum stays below
the characteristic is an equation on the naturals. -/
theorem add_eq_of_natCast {a b c : ℕ} (hab : a + b < p) (hc : c < p)
    (h : (a : K) + b = c) : a + b = c := by
  apply natCast_inj_of_lt (K := K) hab hc
  simpa only [Nat.cast_add] using h

/-- Casts of integers less than the characteristic apart are equal only if the integers are. -/
theorem intCast_inj_of_natAbs_sub_lt {a b : ℤ} (hab : (a - b).natAbs < p) (h : (a : K) = b) :
    a = b := by
  have hdvd : (p : ℤ) ∣ a - b := ((CharP.intCast_eq_intCast K p).mp h).symm.dvd
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by simpa using hab)
  omega

end GordieHowe.IntLift
