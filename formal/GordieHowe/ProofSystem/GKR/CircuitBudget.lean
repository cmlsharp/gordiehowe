-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Circuit
public import GordieHowe.ProofSystem.GKR.CircuitEvents

@[expose] public section

/-!
# Circuit-shape security budgets

The fixed circuit shape determines the number of sumcheck challenges. Shape
bounds here are parameter conditions, not assertions about prover-chosen
values. Numerical certificates include both fields and the masked Ligero
budget; they do not attest a compiled circuit's dimensions.
-/
namespace GordieHowe.GKR.CircuitBudget
open IOP
open GKR.Circuit
open scoped Classical NNReal
variable {F : Type} [Field F]

def dimensions {d : ℕ} (C : Circuit F d) : ℕ :=
  match C with
  | .input _ => 0
  | .layer (inDim := i) _ tail => i + dimensions tail

def WidthsAtMost {d : ℕ} (C : Circuit F d) (bound : ℕ) : Prop :=
  match C with
  | .input _ => True
  | .layer (inDim := i) _ tail => i ≤ bound ∧ WidthsAtMost tail bound

theorem dimensions_le {d : ℕ} (C : Circuit F d) (bound : ℕ)
    (h : WidthsAtMost C bound) : dimensions C ≤ bound * C.depth := by
  induction C with
  | input => simp [dimensions, Circuit.depth]
  | layer Q tail ih =>
    have ht := ih h.2
    have hi := h.1
    simp only [dimensions, Circuit.depth, Nat.mul_add, Nat.mul_one]
    omega

/-- Initial evaluation, shared layer batching, interleaved rounds, and final
input batching. A hand-zero round pays 2 for sumcheck and 1 for assertions. -/
def numerator {d : ℕ} (C : Circuit F d) : ℕ :=
  2*d + 2*C.depth + 5*dimensions C + 1

/-! ## Shape parameters -/

/-- The numerator budget for an address bound and a circuit-depth bound. -/
def shapeBudget (bound depth : ℕ) : ℕ :=
  2*bound + (2+5*bound)*depth + 1

/-- The interleaved schedule visits every hand/coordinate exactly once. -/
def scheduleEquiv (d : ℕ) :
    Fin (LayerSumcheck.schedule d).length ≃ LayerPolynomial.Vars d :=
  List.Nodup.getEquivOfForallMemList (LayerSumcheck.schedule d)
    (LayerSumcheck.schedule_nodup d) (LayerSumcheck.mem_schedule d)

theorem round_cost_sum (d : ℕ) :
    (∑ j : Fin (LayerSumcheck.schedule d).length,
      (2 + if ((LayerSumcheck.schedule d).get j).1 then 0 else 1 : ℕ)) = 5*d := by
  have h := (scheduleEquiv d).sum_comp
    (fun v : LayerPolynomial.Vars d => (2 + if v.1 then 0 else 1 : ℕ))
  change (∑ j, (2 + if ((LayerSumcheck.schedule d).get j).1 then 0 else 1 : ℕ)) = _ at h
  rw [h]
  simp [Fintype.sum_prod_type]
  omega

theorem cost_sum {d : ℕ} (C : Circuit F d) :
    (∑ i, CircuitEvents.cost C i) = 2*C.depth + 5*dimensions C + 1 := by
  induction C with
  | input =>
    change (∑ _i : Unit, (1 : ℕ)) = 1
    simp
  | @layer outDim inDim T Q tail ih =>
    change (∑ i : Unit ⊕ (Fin (LayerSumcheck.schedule inDim).length ⊕ CircuitEvents.Index tail),
      CircuitEvents.cost (.layer Q tail) i) = _
    simp only [Fintype.sum_sum_type, CircuitEvents.cost, Fintype.sum_unique]
    rw [round_cost_sum, ih]
    simp only [Circuit.depth, dimensions]
    omega

theorem error_sum [Fintype F] {d : ℕ} (C : Circuit F d) :
    (∑ i, CircuitEvents.error C i) =
      ((2*C.depth + 5*dimensions C + 1 : ℕ) : NNReal) / Fintype.card F := by
  simp only [CircuitEvents.error, ← Finset.sum_div, ← Nat.cast_sum, cost_sum]

/-- Every circuit-phase challenge has error at most 3/|F|. The separate initial
array move carries its dimension-dependent bound. -/
theorem cost_le_three {d : ℕ} (C : Circuit F d) (i : CircuitEvents.Index C) :
    CircuitEvents.cost C i ≤ 3 := by
  induction C with
  | input => exact Nat.le_refl 1 |>.trans (by decide)
  | layer Q tail ih =>
    rcases i with u | (j | k)
    · exact (by decide : 2 ≤ 3)
    · change 2 + (if _ then 0 else 1) ≤ 3
      split <;> decide
    · exact ih k

theorem error_le_three [Fintype F] {d : ℕ} (C : Circuit F d)
    (i : CircuitEvents.Index C) :
    CircuitEvents.error C i ≤ 3 / (Fintype.card F : NNReal) := by
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (cost_le_three C i)) (by positivity)

theorem numerator_le {d : ℕ} (C : Circuit F d) (bound depth : ℕ)
    (hd : d ≤ bound) (hw : WidthsAtMost C bound) (hl : C.depth ≤ depth) :
    numerator C ≤ shapeBudget bound depth := by
  have hs := (dimensions_le C bound hw).trans (Nat.mul_le_mul_left bound hl)
  unfold numerator shapeBudget
  nlinarith

/-- **The dimensions of a circuit below a layer of at most `2^bound` inputs**: for a circuit whose
output dimension `i` and every layer's input dimension are at most `bound`,
`i + dimensions C ≤ bound · depth C + inputDim C`. -/
theorem add_dimensions_le {i : ℕ} (C : Circuit F i) {bound : ℕ} (hi : i ≤ bound)
    (h : WidthsAtMost C bound) : i + dimensions C ≤ bound * C.depth + C.inputDim := by
  induction C with
  | input d => simp [dimensions, Circuit.depth, Circuit.inputDim]
  | layer Q tail ih =>
    have ht := ih h.1 h.2
    simp only [dimensions, Circuit.depth, Circuit.inputDim, Nat.mul_succ]
    omega

end GordieHowe.GKR.CircuitBudget
