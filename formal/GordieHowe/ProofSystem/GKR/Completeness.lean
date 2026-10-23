-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.CircuitProtocol

@[expose] public section

/-! Honest messages for the concrete two-value Longfellow GKR checker. -/
namespace GordieHowe.GKR.Completeness
open IOP
open GKR.Circuit LayerPolynomial LayerSumcheck LayerProtocol CircuitProtocol
open scoped Classical
variable {F : Type} [Field F] {σ : Type} [Fintype σ] [DecidableEq σ]

/-- Two revealed evaluations determine the honest quadratic exactly. -/
theorem reconstruct_honest (nodes : Sumcheck.Nodes F) (p : Polynomial F)
    (hp : p.natDegree ≤ 2) :
    Sumcheck.Round.reconstruct nodes (p.eval 0 + p.eval 1)
      (p.eval 0) (p.eval (nodes.point 2)) = p := by
  symm
  apply Lagrange.eq_interpolate_of_eval_eq _ nodes.injective.injOn
  · apply Polynomial.degree_le_natDegree.trans_lt
    simpa using (show (p.natDegree : WithBot ℕ) < 3 by exact_mod_cast (show p.natDegree < 3 by omega))
  · intro i _
    fin_cases i <;> simp [nodes.zero, nodes.one]

noncomputable def honestMessage (nodes : Sumcheck.Nodes F)
    (p : MvPolynomial σ F) (env : σ → F) (v : σ) (vs : List σ) (r : F) : Message F :=
  ⟨(roundPolynomial p env v vs).eval 0,
    (roundPolynomial p env v vs).eval (nodes.point 2), r⟩

theorem step_honest (nodes : Sumcheck.Nodes F) (p : MvPolynomial σ F)
    (env : σ → F) (v : σ) (vs : List σ) (r : F) (hp : p.degreeOf v ≤ 2) :
    step nodes (marginal p env (v :: vs)) (honestMessage nodes p env v vs r) =
      marginal p (Function.update env v r) vs := by
  rw [← round_endpoints p env v vs]
  simp only [step, honestMessage]
  rw [← Sumcheck.Round.reconstruct_eval]
  rw [reconstruct_honest nodes _ ((round_degree p env v vs).trans hp), round_eval]

/-- Each message uses only the preceding challenges; the current scalar is
stored solely as the verifier component of the round. -/
noncomputable def honestRounds (nodes : Sumcheck.Nodes F) (p : MvPolynomial σ F)
    (env : σ → F) : (todo : List σ) → (Fin todo.length → F) → Fin todo.length → Message F
  | [], _ => fun j => Fin.elim0 j
  | v :: vs, r => Fin.cons (honestMessage nodes p env v vs (r 0))
      (honestRounds nodes p (Function.update env v (r 0)) vs (fun j => r j.succ))

@[simp] theorem honestRounds_challenge (nodes : Sumcheck.Nodes F)
    (p : MvPolynomial σ F) (env : σ → F) (todo : List σ)
    (r : Fin todo.length → F) (j : Fin todo.length) :
    (honestRounds nodes p env todo r j).challenge = r j := by
  induction todo generalizing env with
  | nil => exact Fin.elim0 j
  | cons v vs ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · exact ih _ _ j

/-- Honest interpolation preserves the exact remaining marginal. -/
theorem run_honest (nodes : Sumcheck.Nodes F) (p : MvPolynomial σ F)
    (env : σ → F) (todo : List σ) (r : Fin todo.length → F)
    (hp : ∀ v, p.degreeOf v ≤ 2) :
    run nodes env (marginal p env todo) todo (honestRounds nodes p env todo r) =
      (install env todo r, MvPolynomial.eval (install env todo r) p) := by
  induction todo generalizing env with
  | nil => rfl
  | cons v vs ih =>
    simp only [run, honestRounds, Fin.cons_zero, Fin.cons_succ]
    rw [step_honest nodes p env v vs (r 0) (hp v)]
    exact ih _ _

structure LayerChallenges (F : Type) (d : ℕ) (Tail : Type) where
  alpha : F
  beta : F
  rounds : Fin (schedule d).length → F
  tail : Tail

def Challenges {d : ℕ} (C : Circuit F d) : Type :=
  match C with
  | .input _ => F
  | .layer (inDim := i) _ tail => LayerChallenges F i (Challenges tail)

/-- Circuit messages are obtained from its computed wire tables. No prover
message depends on a later challenge. -/
noncomputable def honestTrace (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (ch : Challenges C) : Trace C :=
  match C with
  | .input _ => ch
  | .layer (inDim := i) Q tail =>
    let env := install (fun _ : Vars i => (0 : F)) (schedule i) ch.rounds
    let p := target Q (ClaimEvaluation.binaryLabelEquiv i) (cubeTable (tail.eval input))
      (weight g0 g1 ch.alpha) ch.beta
    ⟨ch.alpha, ch.beta, honestRounds nodes p (fun _ => 0) (schedule i) ch.rounds,
      ![ClaimEvaluation.evalTable (tail.eval input) (fun j => env (false,j)),
        ClaimEvaluation.evalTable (tail.eval input) (fun j => env (true,j))],
      honestTrace nodes tail input (fun j => env (false,j)) (fun j => env (true,j)) ch.tail⟩

theorem asserted_zero {G W T : ℕ} (Q : GKR.Layer F G W T) (w : Fin W → F)
    (h : ∀ g, Layer.assertions Q w g = 0) (weights : Fin G → F) :
    Layer.asserted Q w weights = 0 := by
  rw [Layer.asserted_eq_sum]
  exact Finset.sum_eq_zero fun g _ => by rw [h g, mul_zero]

theorem initial_marginal {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T) (w : Fin (2^inDim) → F)
    (g0 g1 : Fin outDim → F) (alpha beta : F)
    (h : ∀ g, Layer.assertions Q w g = 0) :
    marginal (target Q (ClaimEvaluation.binaryLabelEquiv inDim) (cubeTable w)
      (weight g0 g1 alpha) beta) (fun _ => 0) (schedule inDim) =
      ClaimEvaluation.evalTable (output Q w) g0 +
        alpha * ClaimEvaluation.evalTable (output Q w) g1 := by
  rw [layer_initial]
  have hw : cubeTable w ∘ ClaimEvaluation.binaryLabelEquiv inDim = w := by ext i; simp
  rw [hw]
  unfold weight
  rw [Layer.bind_combined, asserted_zero Q w h, asserted_zero Q w h]
  simp only [mul_zero, add_zero, ordinary_eq_evalTable]

theorem check_honest (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (ch : Challenges C)
    (h : C.AssertionsHold input) :
    check nodes C input g0 g1 (ClaimEvaluation.evalTable (C.eval input) g0)
      (ClaimEvaluation.evalTable (C.eval input) g1) (honestTrace nodes C input g0 g1 ch) := by
  induction C with
  | input d => rfl
  | @layer outDim inDim T Q tail ih =>
    let env := install (fun _ : Vars inDim => (0 : F)) (schedule inDim) ch.rounds
    let p := target Q (ClaimEvaluation.binaryLabelEquiv inDim) (cubeTable (tail.eval input))
      (weight g0 g1 ch.alpha) ch.beta
    have hr := run_honest nodes p (fun _ => 0) (schedule inDim) ch.rounds
      (target_degree Q _ _ _ _)
    have hi := initial_marginal Q (tail.eval input) g0 g1 ch.alpha ch.beta h.1
    change marginal p (fun _ => 0) (schedule inDim) = _ at hi
    rw [hi] at hr
    change _ ∧ _
    have hl : layerRun nodes
        (ClaimEvaluation.evalTable (output Q (tail.eval input)) g0)
        (ClaimEvaluation.evalTable (output Q (tail.eval input)) g1)
        (honestTrace nodes (.layer Q tail) input g0 g1 ch) =
        (env, MvPolynomial.eval env p) := hr
    simp only [Circuit.eval]
    rw [hl]
    constructor
    · change MvPolynomial.eval env p = _
      rw [LayerPolynomial.terminal, hand_eval, hand_eval]
      rfl
    · exact ih input _ _ ch.tail h.2

/-- Every challenge family admits zero-start acceptance for a satisfied source
circuit. No challenge values are excluded. -/
theorem satisfied_check_honest (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (ch : Challenges C)
    (h : C.Satisfied input) :
    check nodes C input g0 g1 0 0 (honestTrace nodes C input g0 g1 ch) := by
  have hz : ∀ g, ClaimEvaluation.evalTable (C.eval input) g = 0 := by
    intro g
    simp [ClaimEvaluation.evalTable, h.1]
  simpa only [hz] using check_honest nodes C input g0 g1 ch h.2

/-- Forget prover coordinates, retaining precisely the verifier challenges. -/
def traceChallenges {d : ℕ} (C : Circuit F d) (tr : Trace C) : Challenges C :=
  match C with
  | .input _ => tr
  | .layer _ tail =>
    ⟨tr.alpha, tr.beta, fun j => (tr.rounds j).challenge, traceChallenges tail tr.tail⟩

@[simp] theorem honestTrace_challenges (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F)
    (ch : Challenges C) : traceChallenges C (honestTrace nodes C input g0 g1 ch) = ch := by
  induction C with
  | input d => rfl
  | @layer outDim inDim T Q tail ih =>
    cases ch
    simp only [honestTrace, traceChallenges, honestRounds_challenge]
    congr 1
    exact ih input _ _ _

end GordieHowe.GKR.Completeness
