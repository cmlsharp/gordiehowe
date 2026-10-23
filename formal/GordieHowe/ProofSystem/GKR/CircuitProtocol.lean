-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Circuit
public import GordieHowe.ProofSystem.GKR.ClaimEvaluation
public import GordieHowe.ProofSystem.GKR.LayerProtocol

@[expose] public section

/-!
# Recursive Longfellow GKR transcript semantics

Every intermediate wire table is computed from the fixed input. The checker
uses shared alpha/beta binding, interleaved two-value sumcheck rounds, two
revealed wire claims, and a final scalar input batching challenge. Escape
events are explicit false-equality transitions. Soundness outside these
events is deterministic; their challenge probabilities and causal ordering
are supplied separately by the round-by-round assembly.
-/
namespace GordieHowe.GKR.CircuitProtocol
open IOP
open GKR.Circuit LayerPolynomial LayerSumcheck LayerProtocol
open scoped Classical
variable {F : Type} [Field F]

structure LayerTrace (F : Type) (d : ℕ) (Tail : Type) where
  alpha : F
  beta : F
  rounds : Fin (schedule d).length → Message F
  wc : Fin 2 → F
  tail : Tail

def Trace {d : ℕ} (C : Circuit F d) : Type :=
  match C with
  | .input _ => F
  | .layer (inDim := i) _ tail => LayerTrace F i (Trace tail)

noncomputable def cubeTable {d : ℕ} (w : Fin (2^d) → F) : Cube d → F :=
  fun b => w ((ClaimEvaluation.binaryLabelEquiv d).symm b)

omit [Field F] in
@[simp] theorem cubeTable_label {d : ℕ} (w : Fin (2^d) → F) (i : Fin (2^d)) :
    cubeTable w (ClaimEvaluation.binaryLabelEquiv d i) = w i := by
  simp [cubeTable]

/-- Both hand MLEs are exactly the source's integer-indexed table evaluations. -/
theorem hand_eval {d : ℕ} (w : Fin (2^d) → F) (h : Bool) (env : Vars d → F) :
    MvPolynomial.eval env (LayerPolynomial.mle h (cubeTable w)) =
      ClaimEvaluation.evalTable w (fun j => env (h,j)) := by
  rw [ClaimEvaluation.evalTable_eq_value]
  simp only [LayerPolynomial.mle, map_sum, map_mul, MvPolynomial.eval_C,
    LayerPolynomial.selector, map_prod, ClaimEvaluation.value, cubeTable]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  cases b j <;> simp

/-- Ordinary corner binding is the evaluation of the computed output table. -/
theorem ordinary_eq_evalTable {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T) (w : Fin (2^inDim) → F)
    (g : Fin outDim → F) :
    Layer.ordinary Q w (fun i => PackedClaim.eqPt g i.val) =
      ClaimEvaluation.evalTable (Circuit.output Q w) g :=
  (Circuit.output_weighted Q w (fun i => PackedClaim.eqPt g i.val)).symm

/-- Shared-beta assertion binding evaluates the actual grouped assertion table. -/
theorem asserted_eq_evalTable {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T) (w : Fin (2^inDim) → F)
    (g : Fin outDim → F) :
    Layer.asserted Q w (fun i => PackedClaim.eqPt g i.val) =
      ClaimEvaluation.evalTable (Layer.assertions Q w) g := by
  have hp : ClaimEvaluation.padded (ClaimEvaluation.binaryLabelEquiv outDim)
      (Layer.assertions Q w) = cubeTable (Layer.assertions Q w) := by
    ext b
    obtain ⟨i,rfl⟩ := (ClaimEvaluation.binaryLabelEquiv outDim).surjective b
    rw [ClaimEvaluation.padded_at _ (ClaimEvaluation.binaryLabelEquiv outDim).injective,
      cubeTable_label]
  have h := ClaimEvaluation.assertion_value Q (ClaimEvaluation.binaryLabelEquiv outDim) w g
  rw [hp] at h
  rw [ClaimEvaluation.evalTable_eq_value]
  change Layer.asserted Q w (fun i => PackedClaim.eqPt g i.val) =
    ClaimEvaluation.value (cubeTable (Layer.assertions Q w)) g
  rw [h]
  apply congrArg (Layer.asserted Q w)
  funext i
  exact (ClaimEvaluation.chi_binary i.val g).symm

def weight {d : ℕ} (g0 g1 : Fin d → F) (alpha : F) (i : Fin (2^d)) : F :=
  PackedClaim.eqPt g0 i.val + alpha * PackedClaim.eqPt g1 i.val

def layerRun {d : ℕ} {Tail : Type} (nodes : Sumcheck.Nodes F)
    (c0 c1 : F) (tr : LayerTrace F d Tail) : (Vars d → F) × F :=
  run nodes (fun _ => 0) (c0 + tr.alpha*c1) (schedule d) tr.rounds

noncomputable def layerWiring {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (g0 g1 : Fin outDim → F) (alpha beta : F) (env : Vars inDim → F) : F :=
  MvPolynomial.eval env (wiring Q (ClaimEvaluation.binaryLabelEquiv inDim)
    (weight g0 g1 alpha) beta)

/-- **The layer wiring value, executable**: the sum over the corners of the prepared coefficient
times the equality weights of the two hands at their integer indices (`wiring_binary_eval`), the
form `bind_gh_all` computes. Equal to `layerWiring` (`layerWiringDec_eq`). -/
def layerWiringDec [DecidableEq F] {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (g0 g1 : Fin outDim → F) (alpha beta : F) (env : Vars inDim → F) : F :=
  ∑ i, coefficientDec Q (weight g0 g1 alpha) beta i *
    (PackedClaim.eqPt (fun j => env (false,j)) (Q i).left.val *
     PackedClaim.eqPt (fun j => env (true,j)) (Q i).right.val)

theorem layerWiringDec_eq [DecidableEq F] {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (g0 g1 : Fin outDim → F) (alpha beta : F) (env : Vars inDim → F) :
    layerWiringDec Q g0 g1 alpha beta env = layerWiring Q g0 g1 alpha beta env := by
  unfold layerWiringDec layerWiring
  change _ = MvPolynomial.eval env (wiring Q (fun i => binaryLabel i.val) (weight g0 g1 alpha) beta)
  rw [wiring_binary_eval]
  simp only [coefficientDec_eq]

/-- **The layer polynomial's value, executable**: the wiring value (`layerWiringDec`) times the
two hands' table evaluations (`ClaimEvaluation.evalTable`), the factorization `terminal` of the
layer polynomial `target`; equal to its evaluation (`targetEval_eq`). The honest prover's round
messages are marginals of it (`LayerSumcheck.marginalFn`). -/
def targetEval [DecidableEq F] {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T) (w : Fin (2^inDim) → F)
    (g0 g1 : Fin outDim → F) (alpha beta : F) (env : Vars inDim → F) : F :=
  layerWiringDec Q g0 g1 alpha beta env *
    (ClaimEvaluation.evalTable w (fun j => env (false,j)) *
      ClaimEvaluation.evalTable w (fun j => env (true,j)))

theorem targetEval_eq [DecidableEq F] {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T) (w : Fin (2^inDim) → F)
    (g0 g1 : Fin outDim → F) (alpha beta : F) :
    targetEval Q w g0 g1 alpha beta = fun env => MvPolynomial.eval env
      (target Q (ClaimEvaluation.binaryLabelEquiv inDim) (cubeTable w) (weight g0 g1 alpha) beta) := by
  funext env
  rw [terminal, hand_eval, hand_eval, targetEval, layerWiringDec_eq]
  rfl

/-- Verifier algebra, including the final linear combination of input claims. -/
def check (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (c0 c1 : F) (tr : Trace C) : Prop :=
  match C with
  | .input _ => c0 + (show F from tr)*c1 = ClaimEvaluation.evalTable input g0 +
      (show F from tr) * ClaimEvaluation.evalTable input g1
  | .layer Q tail =>
    let result := layerRun nodes c0 c1 tr
    result.2 = layerWiring Q g0 g1 tr.alpha tr.beta result.1 * (tr.wc 0 * tr.wc 1) ∧
      check nodes tail input (fun j => result.1 (false,j)) (fun j => result.1 (true,j))
        (tr.wc 0) (tr.wc 1) tr.tail

/-- Final scalar batching heals an incorrect pair of input claims. -/
def FinalEscape {d : ℕ} (w : Fin (2^d) → F) (g0 g1 : Fin d → F)
    (c0 c1 alpha : F) : Prop :=
  (c0 ≠ ClaimEvaluation.evalTable w g0 ∨ c1 ≠ ClaimEvaluation.evalTable w g1) ∧
    c0 + alpha*c1 = ClaimEvaluation.evalTable w g0 + alpha*ClaimEvaluation.evalTable w g1

/-- The actual shared-alpha/beta layer binding heals a wrong claim or a
nonzero assertion evaluation. -/
def BeginEscape {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T) (w : Fin (2^inDim) → F)
    (g0 g1 : Fin outDim → F) (c0 c1 alpha beta : F) : Prop :=
  (c0 ≠ ClaimEvaluation.evalTable (Circuit.output Q w) g0 ∨
   c1 ≠ ClaimEvaluation.evalTable (Circuit.output Q w) g1 ∨
   Layer.asserted Q w (fun g => PackedClaim.eqPt g0 g.val) ≠ 0 ∨
   Layer.asserted Q w (fun g => PackedClaim.eqPt g1 g.val) ≠ 0) ∧
    c0 + alpha*c1 = Layer.bind Q w (weight g0 g1 alpha) beta

/-- A violated layer assertion table evaluates to zero at hand zero. Its
absence is later obtained by tracking partial MLE specialization challenges. -/
def AssertionEscape {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T) (w : Fin (2^inDim) → F)
    (g0 : Fin outDim → F) : Prop :=
  (¬ ∀ g, Layer.assertions Q w g = 0) ∧
    Layer.asserted Q w (fun g => PackedClaim.eqPt g0 g.val) = 0

def NoEscape (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (c0 c1 : F) (tr : Trace C) : Prop :=
  match C with
  | .input _ => ¬ FinalEscape input g0 g1 c0 c1 tr
  | .layer Q tail =>
    let w := tail.eval input
    let result := layerRun nodes c0 c1 tr
    ¬ BeginEscape Q w g0 g1 c0 c1 tr.alpha tr.beta ∧
    (∀ j, ¬ BadStep nodes (target Q (ClaimEvaluation.binaryLabelEquiv _) (cubeTable w)
      (weight g0 g1 tr.alpha) tr.beta) (fun _ => 0) (c0+tr.alpha*c1) (schedule _) tr.rounds j) ∧
    ¬ AssertionEscape Q w g0 ∧
    NoEscape nodes tail input (fun j => result.1 (false,j)) (fun j => result.1 (true,j))
      (tr.wc 0) (tr.wc 1) tr.tail

/-- All wire claims and all assertions follow from the checker when none of
the concrete equality-healing events occurs. -/
theorem sound (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (c0 c1 : F) (tr : Trace C)
    (hc : check nodes C input g0 g1 c0 c1 tr)
    (hn : NoEscape nodes C input g0 g1 c0 c1 tr) :
    c0 = ClaimEvaluation.evalTable (C.eval input) g0 ∧
    c1 = ClaimEvaluation.evalTable (C.eval input) g1 ∧ C.AssertionsHold input := by
  induction C generalizing c0 c1 with
  | input d =>
    have he : c0 = ClaimEvaluation.evalTable input g0 ∧
        c1 = ClaimEvaluation.evalTable input g1 := by
      by_contra h
      apply hn
      exact ⟨by simpa only [not_and_or, not_not] using h, hc⟩
    exact ⟨he.1, he.2, trivial⟩
  | @layer outDim inDim T Q tail ih =>
    rcases hc with ⟨hl, ht⟩
    rcases hn with ⟨hb, hs, ha, hn⟩
    have htail := ih input _ _ _ _ tr.tail ht hn
    have hterminal : (layerRun nodes c0 c1 tr).2 =
        MvPolynomial.eval (layerRun nodes c0 c1 tr).1
          (wiring Q (ClaimEvaluation.binaryLabelEquiv inDim) (weight g0 g1 tr.alpha) tr.beta) *
        (MvPolynomial.eval (layerRun nodes c0 c1 tr).1 (mle false (cubeTable (tail.eval input))) *
         MvPolynomial.eval (layerRun nodes c0 c1 tr).1 (mle true (cubeTable (tail.eval input)))) := by
      rw [hand_eval, hand_eval, ← htail.1, ← htail.2.1]
      exact hl
    have hbind := layer_initial_of_terminal nodes Q (ClaimEvaluation.binaryLabelEquiv inDim)
      (cubeTable (tail.eval input)) (weight g0 g1 tr.alpha) tr.beta (fun _ => 0)
      (c0+tr.alpha*c1) tr.rounds hs hterminal
    have htable : cubeTable (tail.eval input) ∘ ClaimEvaluation.binaryLabelEquiv inDim =
        tail.eval input := by ext i; simp
    rw [htable] at hbind
    have hgood : c0 = ClaimEvaluation.evalTable (Circuit.output Q (tail.eval input)) g0 ∧
        c1 = ClaimEvaluation.evalTable (Circuit.output Q (tail.eval input)) g1 ∧
        Layer.asserted Q (tail.eval input) (fun g => PackedClaim.eqPt g0 g.val) = 0 := by
      by_contra h
      apply hb
      refine ⟨?_, hbind⟩
      simp only [not_and_or] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    have hass : ∀ g, Layer.assertions Q (tail.eval input) g = 0 := by
      by_contra h
      exact ha ⟨h,hgood.2.2⟩
    exact ⟨hgood.1,hgood.2.1,hass,htail.2.2⟩

def OutputEscape {d : ℕ} (w : Fin (2^d) → F) (g0 : Fin d → F) : Prop :=
  (∃ i, w i ≠ 0) ∧ ClaimEvaluation.evalTable w g0 = 0

/-- Zero-start checking proves the computed circuit relation, outside the
explicit output-evaluation and recursive transcript escape events. -/
theorem satisfied (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (tr : Trace C)
    (hc : check nodes C input g0 g1 0 0 tr) (hn : NoEscape nodes C input g0 g1 0 0 tr)
    (ho : ¬ OutputEscape (C.eval input) g0) : C.Satisfied input := by
  have h := sound nodes C input g0 g1 0 0 tr hc hn
  refine ⟨?_, h.2.2⟩
  intro i
  by_contra hi
  exact ho ⟨⟨i,hi⟩,h.1.symm⟩

end GordieHowe.GKR.CircuitProtocol
