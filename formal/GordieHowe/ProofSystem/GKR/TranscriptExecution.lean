-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Transcript
public import GordieHowe.ProofSystem.GKR.LayerProtocol

@[expose] public section

/-!
# Masked transcript execution

The symbolic constraint builder and the ordered sumcheck execution use the
same recurrence. Pads are arbitrary fixed committed values. Interpolation
coefficients below are computed from the actual challenge and chosen nodes.
-/
namespace GordieHowe.GKR.TranscriptExecution
open IOP

open LayerProtocol
variable {F σ PadIdx : Type} [Field F] [DecidableEq σ]

theorem run_scalar (nodes : Sumcheck.Nodes F) (env : σ → F) (incoming : F)
    (todo : List σ) (tr : Fin todo.length → Message F) :
    (run nodes env incoming todo tr).2 =
      (List.ofFn tr).foldl (step nodes) incoming := by
  induction todo generalizing env incoming with
  | nil => rfl
  | cons v vs ih =>
    simp only [run, List.ofFn_succ, List.foldl_cons]
    exact ih _ _ _

/-- Unmasking is a fixed translation of the two prover-supplied values. -/
def message (p0 p2 pad0 pad2 challenge : F) : Message F :=
  ⟨p0 + pad0, p2 + pad2, challenge⟩

theorem step_message (nodes : Sumcheck.Nodes F)
    (incoming p0 p2 pad0 pad2 challenge : F) :
    step nodes incoming (message p0 p2 pad0 pad2 challenge) =
      Sumcheck.Round.coefficients nodes challenge 1 * (incoming - (p0 + pad0)) +
      Sumcheck.Round.coefficients nodes challenge 0 * (p0 + pad0) +
      Sumcheck.Round.coefficients nodes challenge 2 * (p2 + pad2) := rfl

open GKR.Transcript in
/-- The transcript constructor supplies genuine interpolation coefficients.
This bridge identifies its symbolic fold with the executable layer fold. -/
theorem claim_eq_fold {L : ℕ} (layout : Layout PadIdx L)
    (tr : Transcript F PadIdx L layout) (pads : PadIdx → F)
    (nodes : Sumcheck.Nodes F) (l : Fin (L + 1))
    (challenge : Fin (layout.rounds l) → F)
    (hlag : tr.lag l = fun r => Sumcheck.Round.coefficients nodes (challenge r)) :
    claim layout tr pads l =
      (List.ofFn (fun r : Fin (layout.rounds l) =>
        message (tr.hp l r 0) (tr.hp l r 1)
          (pads (layout.polyPad l r 0)) (pads (layout.polyPad l r 1))
          (challenge r))).foldl (LayerProtocol.step nodes) (start layout tr pads l) := by
  rw [List.ofFn_eq_map, List.foldl_map]
  unfold claim
  congr 1
  funext acc r
  simp only [Transcript.step, LayerProtocol.step, message, hlag]

end GordieHowe.GKR.TranscriptExecution
