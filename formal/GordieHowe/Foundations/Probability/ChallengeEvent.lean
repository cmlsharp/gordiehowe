-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

@[expose] public section

/-!
# Challenge events

Every randomized check in the constructions has the same shape: a polynomial,
determined by values fixed before the challenge is drawn, that must be nonzero
and must vanish at the challenge for a false claim to pass.  A `ChallengeEvent`
is such a polynomial with a degree bound, `BadAt` is the root condition, and
`card_roots_le` is the one fact the round-by-round layer needs: a uniform
challenge lands in the event with probability at most the degree over the
field size.

Gadget soundness theorems conclude `Spec ∨ BadAt event challenge`. Naming the event keeps the
statements readable and makes the error accounting a sum of `deg` fields.
-/

namespace GordieHowe

open Polynomial

/-- A polynomial in the challenge with a degree bound. -/
structure ChallengeEvent (K : Type*) [Field K] where
  poly : K[X]
  deg : ℕ
  natDegree_le : poly.natDegree ≤ deg

namespace ChallengeEvent

variable {K : Type*} [Field K] [DecidableEq K]

/-- The challenge is a root of the nonzero polynomial. -/
def BadAt (ev : ChallengeEvent K) (δ : K) : Prop := ev.poly ≠ 0 ∧ ev.poly.eval δ = 0

/-- A nonzero polynomial of degree at most `deg` has at most `deg` roots. -/
theorem card_roots_le (ev : ChallengeEvent K) :
    ev.poly.roots.toFinset.card ≤ ev.deg :=
  (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ev.natDegree_le)

open Classical in
/-- The set of bad challenges, as a finset. -/
noncomputable def badSet (ev : ChallengeEvent K) : Finset K :=
  if ev.poly = 0 then ∅ else ev.poly.roots.toFinset

theorem mem_badSet_iff {ev : ChallengeEvent K} {δ : K} : δ ∈ ev.badSet ↔ ev.BadAt δ := by
  unfold badSet BadAt
  by_cases h : ev.poly = 0
  · simp [h]
  · simp [h, Multiset.mem_toFinset, Polynomial.mem_roots', Polynomial.IsRoot.def]

theorem badSet_card_le (ev : ChallengeEvent K) : ev.badSet.card ≤ ev.deg := by
  unfold badSet
  split_ifs
  · exact Nat.zero_le _
  · exact ev.card_roots_le

/-- Two events at the same challenge: the union bound. -/
theorem badSet_union_card_le (a b : ChallengeEvent K) :
    (a.badSet ∪ b.badSet).card ≤ a.deg + b.deg :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add a.badSet_card_le b.badSet_card_le)

end ChallengeEvent

/-- A polynomial in two challenges with a total-degree bound. The memory check of the ML-DSA
`SampleInBall` shuffle packs records with `δ_enc` and fingerprints with `δ_mem`, and its bound is
Schwartz–Zippel in both variables at once. -/
structure TwoChallengeEvent (K : Type*) [Field K] where
  poly : MvPolynomial (Fin 2) K
  deg : ℕ
  totalDegree_le : poly.totalDegree ≤ deg

namespace TwoChallengeEvent

variable {K : Type*} [Field K]

/-- The pair of challenges is a zero of the nonzero polynomial. -/
def BadAt (ev : TwoChallengeEvent K) (δ₁ δ₂ : K) : Prop :=
  ev.poly ≠ 0 ∧ MvPolynomial.eval ![δ₁, δ₂] ev.poly = 0

/-- Zeros on a product of two copies of a finite set number at most
`deg · |S|`: `MvPolynomial.schwartz_zippel_totalDegree`. -/
theorem card_zeros_le [Fintype K] [DecidableEq K] (ev : TwoChallengeEvent K) (hne : ev.poly ≠ 0) :
    (Finset.univ.filter fun δ : Fin 2 → K => MvPolynomial.eval δ ev.poly = 0).card
      ≤ ev.deg * Fintype.card K := by
  have hcard : 0 < Fintype.card K := Fintype.card_pos
  have hK : (0 : ℚ≥0) < (Fintype.card K : ℚ≥0) := by exact_mod_cast hcard
  have h := MvPolynomial.schwartz_zippel_totalDegree (n := 2) hne (Finset.univ : Finset K)
  rw [Fintype.piFinset_univ, Finset.card_univ] at h
  rw [div_le_div_iff₀ (by positivity) hK] at h
  have hnat : (Finset.univ.filter fun δ : Fin 2 → K => MvPolynomial.eval δ ev.poly = 0).card
      * Fintype.card K ≤ ev.poly.totalDegree * Fintype.card K ^ 2 := by
    exact_mod_cast h
  have hcancel :
      (Finset.univ.filter fun δ : Fin 2 → K => MvPolynomial.eval δ ev.poly = 0).card
        ≤ ev.poly.totalDegree * Fintype.card K := by
    have hpow : ev.poly.totalDegree * Fintype.card K ^ 2
        = (ev.poly.totalDegree * Fintype.card K) * Fintype.card K := by ring
    rw [hpow] at hnat
    exact Nat.le_of_mul_le_mul_right hnat hcard
  exact hcancel.trans (Nat.mul_le_mul_right _ ev.totalDegree_le)

end TwoChallengeEvent

end GordieHowe
