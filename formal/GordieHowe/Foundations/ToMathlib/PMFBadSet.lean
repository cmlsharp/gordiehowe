-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-!
# Splitting off a bad set from an average

For a law `μ` and a function `f` with values in `[0, 1]`, the average of `f` is at most its
average off a set `B` plus the probability of `B`.

- `PMF.tsum_mul_le_add_toOuterMeasure`: the bound.
-/

open scoped ENNReal

namespace PMF

variable {α : Type*}

/-- **An average of a `[0, 1]`-valued function is at most its average off a set plus the set's
probability.** -/
theorem tsum_mul_le_add_toOuterMeasure (μ : PMF α) (f : α → ℝ≥0∞) (hf : ∀ a, f a ≤ 1)
    (B : Set α) :
    ∑' a, μ a * f a ≤ ∑' a, μ a * Bᶜ.indicator f a + μ.toOuterMeasure B := by
  classical
  rw [toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases h : a ∈ B
  · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 h), mul_zero, zero_add,
      Set.indicator_of_mem h]
    calc μ a * f a ≤ μ a * 1 := mul_le_mul_of_nonneg_left (hf a) zero_le
      _ = μ a := mul_one _
  · rw [Set.indicator_of_mem (Set.mem_compl h), Set.indicator_of_notMem h, add_zero]

end PMF
