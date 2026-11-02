-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-!
# The masses of a finite law as real numbers

`PMF.sum_toReal_eq_one`: the masses of a law on a finite type sum to `1` as real numbers.
-/

namespace PMF

variable {K : Type*} [Fintype K]

/-- The masses of a law on a finite type sum to `1` as real numbers. -/
theorem sum_toReal_eq_one (μ : PMF K) : ∑ k, (μ k).toReal = 1 := by
  have h := μ.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum fun k _ => μ.apply_ne_top k, h, ENNReal.toReal_one]

end PMF
