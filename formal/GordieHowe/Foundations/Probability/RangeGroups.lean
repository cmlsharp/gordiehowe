-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Language.Realizations.Range

@[expose] public section

/-!
# The union bound over a finite family of events

The union bound at a uniform challenge (`GordieHowe.IOP.probUniform_exists_le_sum`): for a finite family
of events `p i` with `Pr[p i] ≤ a i`, `Pr[∃ i, p i] ≤ Σ_i a i`. The realization step of the
realized program charges the events of a phase's challenges this way
(`GordieHowe.RealizedProgram.eventBound_realizeLowering_of_derivable`), one term `realError` per challenge.
-/

namespace GordieHowe
open IOP RealizedProgram.ProofSystem.PhaseLayout Range
open scoped NNReal ENNReal

/-! ### The union bound -/

namespace IOP

variable {C : Type} [Fintype C] [Nonempty C]

/-- **The union bound over a finite family**: `Pr[∃ i, p i] ≤ Σ_i a i` when `Pr[p i] ≤ a i`. -/
theorem probUniform_exists_le_sum {ι : Type} [Fintype ι] {p : ι → C → Prop} {a : ι → ℝ≥0}
    (h : ∀ i, Pr[c ← C : p i c] ≤ a i) :
    Pr[c ← C : ∃ i, p i c] ≤ ((∑ i, a i : ℝ≥0) : ℝ≥0∞) := by
  rw [ENNReal.ofNNReal_finsetSum]
  have hU : {c | ∃ i, p i c} = ⋃ i, {c | p i c} := by
    ext c
    simp
  change (PMF.uniformOfFintype C).toOuterMeasure {c | ∃ i, p i c} ≤ _
  rw [hU]
  exact (MeasureTheory.measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => h i)

end IOP

end GordieHowe
