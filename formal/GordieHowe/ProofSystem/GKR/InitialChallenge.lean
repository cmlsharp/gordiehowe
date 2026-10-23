-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.ClaimEvaluation

@[expose] public section

/-!
# The initial GKR challenge

The verifier draws the initial point uniformly from `F^d` for the circuit's output dimension
`d` (the paper's `ρ^(0) ← K^{m_0}`, prot:gkr). A nonzero output or assertion table vanishes
there with probability at most `d/|F|` each (Schwartz–Zippel on its multilinear extension).
-/
namespace GordieHowe.GKR.InitialChallenge
open ClaimEvaluation
open scoped Classical NNReal
section
variable {F : Type} [Field F] [Fintype F]

/-- The initial challenge of a circuit of output dimension `d`: a point of `F^d`. -/
abbrev Challenge (F : Type) (d : ℕ) := Fin d → F

/-- A false table evaluated to zero is the initial-evaluation escape event. -/
def BadTable {d : ℕ} (w : Fin (2^d) → F) (g : Challenge F d) : Prop :=
  (∃ i, w i ≠ 0) ∧ evalTable w g = 0

theorem single_count_nat {d : ℕ} (w : Fin (2^d) → F) :
    (Finset.univ.filter (BadTable w)).card * Fintype.card F ≤
      d * Fintype.card (Challenge F d) := by
  unfold BadTable
  by_cases h : ∃ i, w i ≠ 0
  · simp only [h, true_and]
    simpa [Challenge] using evalTable_count w h
  · simp [h]

theorem single_count {d : ℕ} (w : Fin (2^d) → F) :
    ((Finset.univ.filter (BadTable w)).card : NNReal) ≤
      (d / Fintype.card F : NNReal) * Fintype.card (Challenge F d) := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := F))]
  exact_mod_cast single_count_nat w

/-- Output and active assertion residuals are both fixed before this challenge. -/
def Bad {d : ℕ} (output assertions : Fin (2^d) → F) (g : Challenge F d) : Prop :=
  BadTable output g ∨ BadTable assertions g

theorem bad_count {d : ℕ} (output assertions : Fin (2^d) → F) :
    ((Finset.univ.filter (Bad output assertions)).card : NNReal) ≤
      (2*d / Fintype.card F : NNReal) * Fintype.card (Challenge F d) := by
  have hu : (Finset.univ.filter (Bad output assertions)).card ≤
      (Finset.univ.filter (BadTable output)).card +
      (Finset.univ.filter (BadTable assertions)).card := by
    have he : Finset.univ.filter (Bad output assertions) =
        (Finset.univ.filter (BadTable output)) ∪
          (Finset.univ.filter (BadTable assertions)) := by ext c; simp [Bad]
    rw [he]
    exact Finset.card_union_le _ _
  have hcast : ((Finset.univ.filter (Bad output assertions)).card : NNReal) ≤
      (Finset.univ.filter (BadTable output)).card +
      (Finset.univ.filter (BadTable assertions)).card := by exact_mod_cast hu
  calc
    _ ≤ _ := hcast.trans (add_le_add (single_count output) (single_count assertions))
    _ = _ := by ring

end
end GordieHowe.GKR.InitialChallenge
