-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Compressed

@[expose] public section

/-!
# The outcome of `Sim*(A)` as a distribution

`simLaw e A` (`GordieHowe/Model/QROM/Compressed.lean`) is the outer measure of the Born weights of
`|Sim*(A)⟩`, read as the output and the database. Since `|Sim*(A)⟩` is a unit vector
(`norm_simStage`), it is the outer measure of a distribution: the Born distribution of the state
mapped by the readout.

- `PMF.toOuterMeasure_born`: the Born distribution's outer measure is the Born weights.
- `simPMF`, `simLaw_eq_toOuterMeasure_simPMF`: the distribution of the outcome of `Sim*(A)`.
-/

open MeasureTheory
open scoped ENNReal

namespace GordieHowe.Quantum

variable {ι : Type*} [Fintype ι]

/-- **The Born distribution's outer measure is the Born weights.** -/
theorem toOuterMeasure_born (v : QState ι) (hv : ‖v‖ = 1) (S : Set ι) :
    (born v hv).toOuterMeasure S = bornWeight v S := by
  classical
  rw [bornWeight_apply_eq_sum, PMF.toOuterMeasure_apply, tsum_fintype]
  rfl

end GordieHowe.Quantum

namespace GordieHowe.QROM

open Quantum

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B : Type} (e : BitStr I J ≃ B) {t : ℕ}

/-- `|Sim*(A)⟩` is a unit vector (`norm_simStage`). -/
theorem norm_simState {O : Type} (A : QueryAlg (Bits m) (BitStr I J) t O) :
    ‖simState e A‖ = 1 := by
  rw [simState]
  exact norm_simStage e A t

/-- **The distribution of the outcome of `Sim*(A)`**: the Born distribution of `|Sim*(A)⟩` read as
the output and the database the slots hold. -/
noncomputable def simPMF {O : Type} (A : QueryAlg (Bits m) (BitStr I J) t O) :
    PMF (O × DB (Bits m) B) :=
  (born (simState e A) (norm_simState e A)).map fun b => (A.out b.1.1, slotsDB e b.2)

/-- **`simLaw` is the outer measure of `simPMF`.** -/
theorem simLaw_eq_toOuterMeasure_simPMF {O : Type} (A : QueryAlg (Bits m) (BitStr I J) t O)
    (S : Set (O × DB (Bits m) B)) : simLaw e A S = (simPMF e A).toOuterMeasure S := by
  rw [simPMF, PMF.toOuterMeasure_map_apply, toOuterMeasure_born, simLaw,
    OuterMeasure.map_apply]

end GordieHowe.QROM
