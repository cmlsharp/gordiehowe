-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

/-!
# The union bound for PMFs, in `ℝ`

`PMF.toReal_toOuterMeasure_iUnion_le`: the probability of a finite union of events is at most
the sum of their probabilities, with the probabilities read in `ℝ`. About Mathlib objects only;
a candidate for upstreaming.
-/

open Finset
open scoped BigOperators

namespace PMF

variable {α ι : Type*} [Fintype ι]

/-- The union bound over a finite index type, in `ℝ`. -/
theorem toReal_toOuterMeasure_iUnion_le (p : PMF α) (s : ι → Set α) :
    (p.toOuterMeasure (⋃ j, s j)).toReal ≤ ∑ j, (p.toOuterMeasure (s j)).toReal := by
  have hfin : ∀ t, p.toOuterMeasure t ≠ ⊤ := fun t => by
    rw [toOuterMeasure_apply]
    exact p.tsum_coe_indicator_ne_top t
  rw [← ENNReal.toReal_sum fun j _ => hfin (s j)]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun j _ => hfin (s j))
    (MeasureTheory.measure_iUnion_fintype_le _ s)

end PMF
