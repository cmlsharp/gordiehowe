-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.SourceReduction
public import GordieHowe.ProofSystem.GKR.CircuitBudget
public import GordieHowe.ProofSystem.GKR.Transcript

@[expose] public section

/-! Explicit errors for the constructed source protocol, including packed reveals. -/
namespace GordieHowe.GKR.SourceReduction
open IOP
open GKR.Circuit CircuitBudget Schedule ProtocolEvents CircuitFlatten
open scoped Classical NNReal
variable {F Pub Wit : Type} [Field F] [Fintype F]

theorem protocol_error_sum {d : ℕ} (C : Circuit F d) :
    (∑ i, ProtocolReduction.error F C i) = (numerator C : NNReal) / Fintype.card F := by
  change (∑ i, Sum.elim (fun _ : Unit => (2*d : NNReal)/Fintype.card F)
    (CircuitEvents.error C) (index F C i)) = _
  rw [(index F C).sum_comp, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]
  rw [CircuitBudget.error_sum, ← add_div]
  congr 1
  simp only [numerator, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

end GordieHowe.GKR.SourceReduction
