-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.LayerSumcheck

@[expose] public section

/-!
# Deterministic and counting interface for one Longfellow GKR layer

Each interleaved hand round fixes the two unmasked values p0 and p2 before
its challenge. The claim uses the source reconstruction p1=incoming-p0.
`position` reads only earlier rounds. `BadStep` is exactly an incorrect
incoming marginal becoming correct. Outside these events, correctness of the
terminal expression implies correctness of the incoming layer claim.
This module supplies the per-layer interface for cumulative-event protocol
assembly; it does not introduce a separate protocol soundness premise.
-/
namespace GordieHowe.GKR.LayerProtocol
open IOP
open LayerSumcheck LayerPolynomial
open scoped Classical NNReal
variable {F : Type} [Field F] {σ : Type} [Fintype σ] [DecidableEq σ]

structure Message (F : Type) where
  p0 : F
  p2 : F
  challenge : F

def step (nodes : Sumcheck.Nodes F) (incoming : F) (msg : Message F) : F :=
  Sumcheck.Round.coefficients nodes msg.challenge 1 * (incoming-msg.p0) +
    Sumcheck.Round.coefficients nodes msg.challenge 0 * msg.p0 +
    Sumcheck.Round.coefficients nodes msg.challenge 2 * msg.p2

structure Position (F σ : Type) where
  env : σ → F
  incoming : F
  next : σ
  suffix : List σ

/-- The current state is computed only from strictly earlier transcript entries. -/
def position (nodes : Sumcheck.Nodes F) (env : σ → F) (incoming : F) :
    (todo : List σ) → (Fin todo.length → Message F) → Fin todo.length → Position F σ
  | [], _, j => Fin.elim0 j
  | v :: vs, tr, j => Fin.cases ⟨env,incoming,v,vs⟩
      (fun i => position nodes (Function.update env v (tr 0).challenge)
        (step nodes incoming (tr 0)) vs (fun k => tr k.succ) i) j

/-- Final environment and scalar after the entire ordered round list. -/
def run (nodes : Sumcheck.Nodes F) (env : σ → F) (incoming : F) :
    (todo : List σ) → (Fin todo.length → Message F) → (σ → F) × F
  | [], _ => (env,incoming)
  | v :: vs, tr => run nodes (Function.update env v (tr 0).challenge)
      (step nodes incoming (tr 0)) vs (fun k => tr k.succ)

omit [Fintype σ] in
theorem position_congr (nodes : Sumcheck.Nodes F) (env : σ → F) (incoming : F)
    (todo : List σ) (tr tr' : Fin todo.length → Message F) (j : Fin todo.length)
    (h : ∀ i, i.val < j.val → tr i = tr' i) :
    position nodes env incoming todo tr j = position nodes env incoming todo tr' j := by
  induction todo generalizing env incoming with
  | nil => exact Fin.elim0 j
  | cons v vs ih =>
    revert h
    refine Fin.cases (fun _ => rfl) (fun k h => ?_) j
    simp only [position, Fin.cases_succ]
    have hz := h 0 (by simp)
    rw [hz]
    apply ih
    intro i hi
    exact h i.succ (by simpa using hi)

omit [Fintype σ] in
theorem position_update (nodes : Sumcheck.Nodes F) (env : σ → F) (incoming : F)
    (todo : List σ) (tr : Fin todo.length → Message F) (j : Fin todo.length) (msg : Message F) :
    position nodes env incoming todo (Function.update tr j msg) j =
      position nodes env incoming todo tr j := by
  apply position_congr
  intro i hi
  exact Function.update_of_ne (by intro he; subst i; omega) _ _

omit [Fintype σ] in
theorem position_next (nodes : Sumcheck.Nodes F) (env : σ → F) (incoming : F)
    (todo : List σ) (tr : Fin todo.length → Message F) (j : Fin todo.length) :
    (position nodes env incoming todo tr j).next = todo.get j := by
  induction todo generalizing env incoming with
  | nil => exact Fin.elim0 j
  | cons v vs ih =>
    refine Fin.cases rfl (fun i => ?_) j
    exact ih _ _ _ i

omit [Fintype σ] in
theorem position_suffix (nodes : Sumcheck.Nodes F) (env : σ → F) (incoming : F)
    (todo : List σ) (tr : Fin todo.length → Message F) (j : Fin todo.length) :
    (position nodes env incoming todo tr j).suffix = todo.drop (j.val+1) := by
  induction todo generalizing env incoming with
  | nil => exact Fin.elim0 j
  | cons v vs ih =>
    refine Fin.cases rfl (fun i => ?_) j
    exact ih _ _ _ i

def BadAt (nodes : Sumcheck.Nodes F) (p : MvPolynomial σ F)
    (s : Position F σ) (msg : Message F) : Prop :=
  s.incoming ≠ marginal p s.env (s.next :: s.suffix) ∧
    step nodes s.incoming msg =
      marginal p (Function.update s.env s.next msg.challenge) s.suffix

def BadStep (nodes : Sumcheck.Nodes F) (p : MvPolynomial σ F)
    (env : σ → F) (incoming : F) (todo : List σ) (tr : Fin todo.length → Message F)
    (j : Fin todo.length) : Prop :=
  BadAt nodes p (position nodes env incoming todo tr j) (tr j)

/-- Arbitrary fixed p0,p2 have at most two challenges that heal a false claim. -/
theorem badAt_count [Fintype F] (nodes : Sumcheck.Nodes F) (p : MvPolynomial σ F)
    (hp : ∀ v, p.degreeOf v ≤ 2) (s : Position F σ) (p0 p2 : F) :
    (Finset.univ.filter fun r : F => BadAt nodes p s ⟨p0,p2,r⟩).card ≤ 2 := by
  by_cases hfalse : s.incoming ≠ marginal p s.env (s.next :: s.suffix)
  · have h := Sumcheck.Round.reconstructed_bad_challenge_count nodes s.incoming p0 p2
      (roundPolynomial p s.env s.next s.suffix)
      ((round_degree p s.env s.next s.suffix).trans (hp s.next))
      (by simpa only [round_endpoints] using hfalse)
    apply (Finset.card_le_card ?_).trans h
    intro r hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [step, round_eval] using (Finset.mem_filter.mp hr).2.2
  · simp [BadAt, hfalse]

/-- Exact prefix-conditioned bound: replacing the current challenge changes
neither its prefix state nor its two fixed response values. -/
theorem badStep_count [Fintype F] (nodes : Sumcheck.Nodes F) (p : MvPolynomial σ F)
    (hp : ∀ v, p.degreeOf v ≤ 2) (env : σ → F) (incoming : F)
    (todo : List σ) (tr : Fin todo.length → Message F) (j : Fin todo.length) :
    (Finset.univ.filter fun r : F => BadStep nodes p env incoming todo
      (Function.update tr j ⟨(tr j).p0, (tr j).p2, r⟩) j).card ≤ 2 := by
  simpa only [BadStep, position_update, Function.update_self] using
    badAt_count nodes p hp (position nodes env incoming todo tr j) (tr j).p0 (tr j).p2

omit [Fintype σ] in
/-- Correctness cannot appear during a complete layer without a healing event. -/
theorem initial_of_final (nodes : Sumcheck.Nodes F) (p : MvPolynomial σ F)
    (env : σ → F) (incoming : F) (todo : List σ) (tr : Fin todo.length → Message F)
    (hbad : ∀ j, ¬ BadStep nodes p env incoming todo tr j)
    (hfinal : (run nodes env incoming todo tr).2 =
      MvPolynomial.eval (run nodes env incoming todo tr).1 p) :
    incoming = marginal p env todo := by
  induction todo generalizing env incoming with
  | nil => exact hfinal
  | cons v vs ih =>
    have ht : ∀ j, ¬ BadStep nodes p (Function.update env v (tr 0).challenge)
        (step nodes incoming (tr 0)) vs (fun k => tr k.succ) j := by
      intro j
      exact hbad j.succ
    have hi := ih (Function.update env v (tr 0).challenge)
      (step nodes incoming (tr 0)) (fun k => tr k.succ) ht hfinal
    by_contra hn
    exact hbad 0 ⟨hn, hi⟩

omit [Fintype σ] in
/-- The final environment is the ordered installation of all challenge values. -/
theorem run_env (nodes : Sumcheck.Nodes F) (env : σ → F) (incoming : F)
    (todo : List σ) (tr : Fin todo.length → Message F) :
    (run nodes env incoming todo tr).1 = install env todo (fun j => (tr j).challenge) := by
  induction todo generalizing env incoming with
  | nil => rfl
  | cons v vs ih => exact ih _ _ _

/-- The terminal environment agrees with every actual interleaved challenge. -/
theorem layer_run_env_at {d : ℕ} (nodes : Sumcheck.Nodes F)
    (env : Vars d → F) (incoming : F) (tr : Fin (schedule d).length → Message F)
    (j : Fin (schedule d).length) :
    (run nodes env incoming (schedule d) tr).1 ((schedule d).get j) = (tr j).challenge := by
  rw [run_env, install_at env (schedule d) (schedule_nodup d)]

/-- Exact per-round count in the round-by-round error convention. -/
theorem badStep_count_nnreal [Fintype F] (nodes : Sumcheck.Nodes F) (p : MvPolynomial σ F)
    (hp : ∀ v, p.degreeOf v ≤ 2) (env : σ → F) (incoming : F)
    (todo : List σ) (tr : Fin todo.length → Message F) (j : Fin todo.length) :
    ((Finset.univ.filter fun r : F => BadStep nodes p env incoming todo
      (Function.update tr j ⟨(tr j).p0, (tr j).p2, r⟩) j).card : NNReal) ≤
        (2 / Fintype.card F : NNReal) * Fintype.card F := by
  have hcard : (Fintype.card F : NNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [div_mul_cancel₀ _ hcard]
  exact_mod_cast badStep_count nodes p hp env incoming todo tr j

/-- No polynomial-degree hypothesis remains for the actual layer target. -/
theorem layer_badStep_count [Fintype F] {d G W T : ℕ} (nodes : Sumcheck.Nodes F)
    (Q : GKR.Layer F G W T) (label : Fin W → Cube d) (w : Cube d → F)
    (weight : Fin G → F) (beta : F) (env : Vars d → F) (incoming : F)
    (tr : Fin (schedule d).length → Message F) (j : Fin (schedule d).length) :
    ((Finset.univ.filter fun r : F => BadStep nodes (target Q label w weight beta) env incoming
      (schedule d) (Function.update tr j ⟨(tr j).p0, (tr j).p2, r⟩) j).card : NNReal) ≤
        (2 / Fintype.card F : NNReal) * Fintype.card F :=
  badStep_count_nnreal nodes _ (target_degree Q label w weight beta) env incoming _ tr j

/-- Source-layer form: outside all healing events, the factored terminal
check implies the exact prep_v-bound input claim. -/
theorem layer_initial_of_terminal {d G W T : ℕ} (nodes : Sumcheck.Nodes F)
    (Q : GKR.Layer F G W T) (label : Fin W → Cube d) (w : Cube d → F)
    (weight : Fin G → F) (beta : F) (env : Vars d → F) (incoming : F)
    (tr : Fin (schedule d).length → Message F)
    (hbad : ∀ j, ¬ BadStep nodes (target Q label w weight beta) env incoming (schedule d) tr j)
    (hfinal : (run nodes env incoming (schedule d) tr).2 =
      MvPolynomial.eval (run nodes env incoming (schedule d) tr).1 (wiring Q label weight beta) *
        (MvPolynomial.eval (run nodes env incoming (schedule d) tr).1 (mle false w) *
         MvPolynomial.eval (run nodes env incoming (schedule d) tr).1 (mle true w))) :
    incoming = Layer.bind Q (w ∘ label) weight beta := by
  rw [← layer_initial Q label w weight beta env]
  apply initial_of_final nodes _ env incoming _ tr hbad
  simpa only [terminal] using hfinal

end GordieHowe.GKR.LayerProtocol
