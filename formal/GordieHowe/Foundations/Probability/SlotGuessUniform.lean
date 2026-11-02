-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.SlotGuess
public import GordieHowe.Foundations.Probability.InteractionGuess

@[expose] public section

/-!
# Guessing one of several slots' values

`PMF.tsum_mul_toOuterMeasure_guess_le` (`GordieHowe/Foundations/Probability/SlotGuess.lean`) bounds
the probability of guessing a value computed from one coin read after its request. Here the coins
are a uniform tuple `sc : Fin Q → C`, one coin per slot: the probability that the guess is the
value of some slot `j` at its request is at most `Q` times the one-coin bound, when every slot `j`
satisfies the one-coin hypotheses with the other slots' coins fixed.

- `tsum_uniform_slots_guess_le`: the bound.
-/

open scoped ENNReal BigOperators

namespace PMF

variable {C R Pb Z Ω : Type*} [Fintype C] [Nonempty C] [Fintype R] [Fintype Pb]
  [DecidableEq Pb] [Fintype Z] [DecidableEq Z]

/-- **Guessing the value of one of `Q` slots**: for uniform coins `sc : Fin Q → C`, laws `L sc` of
the run, the request `rq j` of slot `j`, a guess `F`, and the value `g r c` of the coin `c` at the
request `r`, the probability that the guess is the value of some slot at its request is at most
`Q · ⨆ r, Σ_y ⨆ z, Pr_c[φ r c = y ∧ g r c = some z]`. Hypotheses, at every slot `j` with the other
slots' coins `sc` fixed (`Function.update sc j c`): the request's law does not depend on the slot's
coin (`h1`), and the joint law of the request and the guess depends on it only through the public
value `φ r c` (`h2`). -/
theorem tsum_uniform_slots_guess_le {Q : ℕ} (L : (Fin Q → C) → PMF Ω)
    (rq : Fin Q → Ω → Option R) (F : Ω → Option Z) (φ : R → C → Pb) (g : R → C → Option Z)
    (h1 : ∀ j sc r c c', (L (Function.update sc j c)).toOuterMeasure {ω | rq j ω = some r} =
      (L (Function.update sc j c')).toOuterMeasure {ω | rq j ω = some r})
    (h2 : ∀ j sc r z c c', φ r c = φ r c' →
      (L (Function.update sc j c)).toOuterMeasure {ω | rq j ω = some r ∧ F ω = some z} =
        (L (Function.update sc j c')).toOuterMeasure {ω | rq j ω = some r ∧ F ω = some z}) :
    ∑' sc, PMF.uniformOfFintype (Fin Q → C) sc * (L sc).toOuterMeasure
        {ω | ∃ j r z, rq j ω = some r ∧ g r (sc j) = some z ∧ F ω = some z} ≤
      Q * ⨆ r, ∑ y, ⨆ z,
        (PMF.uniformOfFintype C).toOuterMeasure {c | φ r c = y ∧ g r c = some z} := by
  classical
  set γ := ⨆ r, ∑ y, ⨆ z,
    (PMF.uniformOfFintype C).toOuterMeasure {c | φ r c = y ∧ g r c = some z}
  set E : Fin Q → (Fin Q → C) → Set Ω := fun j sc =>
    {ω | ∃ r z, rq j ω = some r ∧ g r (sc j) = some z ∧ F ω = some z}
  -- the union over the slots
  have hunion : ∀ sc, (L sc).toOuterMeasure
      {ω | ∃ j r z, rq j ω = some r ∧ g r (sc j) = some z ∧ F ω = some z} ≤
      ∑ j, (L sc).toOuterMeasure (E j sc) := fun sc => by
    have hset : {ω | ∃ j r z, rq j ω = some r ∧ g r (sc j) = some z ∧ F ω = some z} =
        ⋃ j, E j sc := by
      ext ω
      simp [E]
    rw [hset]
    exact MeasureTheory.measure_iUnion_fintype_le _ _
  -- one slot, by the one-coin bound at the other slots' coins
  have hslot : ∀ j, ∑' sc, PMF.uniformOfFintype (Fin Q → C) sc * (L sc).toOuterMeasure (E j sc) ≤
      γ := fun j => by
    rw [tsum_fintype, GordieHowe.Interaction.sum_uniform_update j]
    calc ∑ sc, PMF.uniformOfFintype (Fin Q → C) sc * ∑ c, PMF.uniformOfFintype C c *
          (L (Function.update sc j c)).toOuterMeasure (E j (Function.update sc j c))
        ≤ ∑ sc, PMF.uniformOfFintype (Fin Q → C) sc * γ := by
          refine Finset.sum_le_sum fun sc _ => mul_le_mul_of_nonneg_left ?_ zero_le
          have h := tsum_mul_toOuterMeasure_guess_le (PMF.uniformOfFintype C)
            (fun c => L (Function.update sc j c)) (rq j) F φ g (h1 j sc) (h2 j sc)
          rw [tsum_fintype] at h
          refine le_of_eq_of_le (Finset.sum_congr rfl fun c _ => ?_) h
          simp only [E, Function.update_self]
      _ = γ := by
          have h1 : ∑ sc, PMF.uniformOfFintype (Fin Q → C) sc = 1 := by
            simpa [tsum_fintype] using PMF.tsum_coe (PMF.uniformOfFintype (Fin Q → C))
          rw [← Finset.sum_mul, h1, one_mul]
  calc ∑' sc, PMF.uniformOfFintype (Fin Q → C) sc * (L sc).toOuterMeasure
        {ω | ∃ j r z, rq j ω = some r ∧ g r (sc j) = some z ∧ F ω = some z}
      ≤ ∑' sc, PMF.uniformOfFintype (Fin Q → C) sc * ∑ j, (L sc).toOuterMeasure (E j sc) :=
        ENNReal.tsum_le_tsum fun sc => mul_le_mul_of_nonneg_left (hunion sc) zero_le
    _ = ∑ j, ∑' sc, PMF.uniformOfFintype (Fin Q → C) sc * (L sc).toOuterMeasure (E j sc) := by
        simp_rw [Finset.mul_sum]
        exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ _j : Fin Q, γ := Finset.sum_le_sum fun j _ => hslot j
    _ = Q * γ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end PMF
