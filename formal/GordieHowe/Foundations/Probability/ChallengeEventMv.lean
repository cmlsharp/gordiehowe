-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.ChallengeEvent
public import Mathlib.Basic.NNReal.Basic

@[expose] public section

/-!
# Challenge events for vector challenges

A challenge drawn as a vector `δ : Fin k → K` with no prover message between
its coordinates (the zerocheck point `ρ`, the three batching scalars `u` of the
univariate skip) is charged as one event: a polynomial in `k` variables with a
total-degree bound, fixed before the vector is drawn. Schwartz–Zippel bounds
the bad vectors by `deg · |K|^(k-1)`, that is, probability `deg / |K|`.
`TwoChallengeEvent` is the case `k = 2` with its own counting lemma.
-/

namespace GordieHowe

open scoped NNReal

/-- A polynomial in the `k` coordinates of a vector challenge with a
total-degree bound. -/
structure ChallengeEventMv (K : Type*) [Field K] (k : ℕ) where
  poly : MvPolynomial (Fin k) K
  deg : ℕ
  totalDegree_le : poly.totalDegree ≤ deg

namespace ChallengeEventMv

variable {K : Type*} [Field K] {k : ℕ}

/-- The challenge vector is a zero of the nonzero polynomial. -/
def BadAt (ev : ChallengeEventMv K k) (δ : Fin k → K) : Prop :=
  ev.poly ≠ 0 ∧ MvPolynomial.eval δ ev.poly = 0

open Classical in
/-- Schwartz–Zippel: at most `deg · |K|^(k-1)` bad vectors, stated without
division as `#bad · |K| ≤ deg · |K|^k`. -/
theorem card_badAt_le [Fintype K] (ev : ChallengeEventMv K k) :
    (Finset.univ.filter ev.BadAt).card * Fintype.card K ≤ ev.deg * Fintype.card K ^ k := by
  by_cases hne : ev.poly = 0
  · have he : Finset.univ.filter ev.BadAt = ∅ := by
      ext δ
      simp [BadAt, hne]
    simp [he]
  have hF : (0 : ℚ≥0) < (Fintype.card K : ℚ≥0) := by exact_mod_cast Fintype.card_pos (α := K)
  have h := MvPolynomial.schwartz_zippel_totalDegree hne (Finset.univ : Finset K)
  rw [Fintype.piFinset_univ, Finset.card_univ] at h
  rw [div_le_div_iff₀ (by positivity) hF] at h
  have hz : (Finset.univ.filter fun δ : Fin k → K => MvPolynomial.eval δ ev.poly = 0).card *
      Fintype.card K ≤ ev.poly.totalDegree * Fintype.card K ^ k := by exact_mod_cast h
  have hf : Finset.univ.filter ev.BadAt =
      Finset.univ.filter fun δ : Fin k → K => MvPolynomial.eval δ ev.poly = 0 := by
    ext δ
    simp [BadAt, hne]
  rw [hf]
  exact hz.trans (Nat.mul_le_mul_right _ ev.totalDegree_le)

open Classical in
/-- The same bound in the round-by-round error convention: probability at
most `deg / |K|` over the `|K|^k` challenge vectors. -/
theorem card_badAt_le_nnreal [Fintype K] (ev : ChallengeEventMv K k) :
    ((Finset.univ.filter ev.BadAt).card : ℝ≥0) ≤
      (ev.deg / Fintype.card K : ℝ≥0) * Fintype.card (Fin k → K) := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := K))]
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
    (show ((Finset.univ.filter ev.BadAt).card : ℝ≥0) * Fintype.card K ≤
      ev.deg * (Fintype.card K : ℝ≥0) ^ k by exact_mod_cast ev.card_badAt_le)

end ChallengeEventMv

end GordieHowe
