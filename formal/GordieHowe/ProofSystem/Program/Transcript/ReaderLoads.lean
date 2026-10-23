-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Transcript.Format
public import GordieHowe.ProofSystem.Program.Transcript.CircuitCodecs
public import GordieHowe.Applications.Falcon512.PoP.Configuration
public import GordieHowe.Applications.MLDSA44.PoP.Configuration

@[expose] public section

/-!
# The largest challenge loads of the A circuits

The GKR pads of a source circuit of bounded shape, the GKR part of the largest load of a challenge
round of an A circuit: at most `depth · (4 · width + 3)` (`GordieHowe.GKR.LayeredCircuit.ShapeAtMost.card_padIdx_le`),
from the round count of a layer (`GKR.CircuitFlatten.roundCount_le`) and the count of the
remaining layers (`GordieHowe.GKR.LayeredCircuit.ShapeAtMost.tail_depth`).
-/

namespace GordieHowe

open IOP SPBCS SPBCS.Configurations QROM RelativePacking

/-! ### GKR pads -/

namespace GKR.CircuitFlatten

variable {F : Type} [Field F]

/-- A layer of at most `2^width` inputs has at most `2 · width` sumcheck rounds. -/
theorem roundCount_le {d : ℕ} (C : GKR.Circuit F d) {width : ℕ}
    (h : CircuitBudget.WidthsAtMost C width) (l : Fin C.depth) : roundCount C l ≤ 2 * width := by
  induction C with
  | input => exact l.elim0
  | layer Q tail ih =>
    obtain ⟨hi, ht⟩ := h
    refine Fin.cases ?_ (fun l => ?_) l
    · simp only [roundCount, Fin.cases_zero, LayerSumcheck.schedule_length]
      omega
    · simp only [roundCount, Fin.cases_succ]
      exact ih ht l

end GKR.CircuitFlatten

namespace GKR.LayeredCircuit

variable {F : Type} [Field F] {d : ℕ}

/-- The remaining layers number at most `depth - 1`. -/
theorem ShapeAtMost.tail_depth {S : LayeredCircuit F d} {width depth : ℕ}
    (h : S.ShapeAtMost width depth) : S.tail.depth + 1 ≤ depth := h.depth_le

/-- **The GKR pads of a source circuit of bounded shape**: per layer two pads per sumcheck round
and three claim pads, at most `depth · (4 · width + 3)`. -/
theorem ShapeAtMost.card_padIdx_le {S : LayeredCircuit F d} {width depth : ℕ}
    (h : S.ShapeAtMost width depth) : Fintype.card S.PadIdx ≤ depth * (4 * width + 3) := by
  have hc : Fintype.card S.PadIdx =
      ∑ l : Fin S.circuit.depth, (CircuitFlatten.roundCount S.circuit l * 2 + 3) := by
    unfold LayeredCircuit.PadIdx CircuitFlatten.PadIndex
    simp [Fintype.card_sigma, Fintype.card_sum]
  rw [hc]
  calc ∑ l : Fin S.circuit.depth, (CircuitFlatten.roundCount S.circuit l * 2 + 3)
      ≤ ∑ _l : Fin S.circuit.depth, (4 * width + 3) := Finset.sum_le_sum fun l _ => by
        have := CircuitFlatten.roundCount_le S.circuit h.widths l
        omega
    _ = S.circuit.depth * (4 * width + 3) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ h.depth_le

end GKR.LayeredCircuit

end GordieHowe

