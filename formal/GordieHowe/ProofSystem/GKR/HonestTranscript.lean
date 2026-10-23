-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Completeness
public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.ProofSystem.GKR.PadTranslation
public import GordieHowe.ProofSystem.GKR.SourceReduction
public import GordieHowe.Model.IOP.CompletenessAppend
public import GordieHowe.Foundations.Probability.IdentDistrib
public import GordieHowe.ProofSystem.GKR.ScheduleFintype

@[expose] public section

/-!
# Honest messages on the source GKR schedule, with fixed committed pads

`maskedFamily` is the honest prover on the typed GKR schedule: every revealed
value (both round coefficients of every sumcheck round, both wire claims of
every layer) is sent minus its committed pad. The pads are fixed before the
first challenge, so every message depends only on earlier challenges.
`family` is the same prover at zero pads (`maskedFamily_zero`).

`valueFamily` sends given values in the shape of the free pads (`FreePads`) and
runs no prover. `maskedFamily_identDistrib` is the hiding law: for fixed challenges,
the masked transcript under uniform free pads has the law of `valueFamily` under
uniform values, whatever the input (`maskedFamily_eq_value`: the masked
transcript at `π` is `valueFamily` at the revealed honest values minus `π`).
-/
namespace GordieHowe.GKR.HonestTranscript
open IOP
open GKR.Circuit CircuitProtocol LayerProtocol LayerSumcheck
open Completeness PadTranslation LayerPolynomial
open scoped Classical
variable {F : Type} [Field F]

@[simp] theorem mask_challenges {d : ℕ} (C : Circuit F d) (pads : Pads C) (tr : Trace C) :
    traceChallenges C (mask C pads tr) = traceChallenges C tr := by
  induction C with
  | input d => rfl
  | layer Q tail ih =>
    simp only [mask, traceChallenges, maskMessage_challenge, ih]
    rfl

/-- Zero pads are an available fixed commitment for completeness. -/
def zeroPads {d : ℕ} (C : Circuit F d) : Pads C :=
  match C with
  | .input _ => ()
  | .layer _ tail => ⟨fun _ _ => 0, fun _ => 0, zeroPads tail⟩

@[simp] theorem zeroPads_products {d : ℕ} (C : Circuit F d) : ProductsHold C (zeroPads C) := by
  induction C with
  | input d => trivial
  | layer Q tail ih => exact ⟨by simp [zeroPads], ih⟩

@[simp] theorem unmask_zero {d : ℕ} (C : Circuit F d) (tr : Trace C) :
    unmask C (zeroPads C) tr = tr := by
  induction C with
  | input d => rfl
  | layer Q tail ih =>
    cases tr
    simp only [unmask, zeroPads, unmaskMessage, add_zero, ih]
    rfl

@[simp] theorem mask_zero {d : ℕ} (C : Circuit F d) (tr : Trace C) :
    mask C (zeroPads C) tr = tr := by
  rw [← unmask_zero C (mask C (zeroPads C) tr), unmask_mask]

theorem masked_honest_check (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (pads : Pads C) (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F)
    (ch : Challenges C) (h : C.Satisfied input) :
    check nodes C input g0 g1 0 0
      (unmask C pads (mask C pads (honestTrace nodes C input g0 g1 ch))) := by
  rw [unmask_mask]
  exact satisfied_check_honest nodes C input g0 g1 ch h

open Schedule ProtocolSpec

/-- The scalar challenges of an interleaved sumcheck phase, read from their
verifier moves. -/
def roundChallenges : (k : ℕ) → (rounds F k).Challenges → Fin k → F
  | 0, _ => Fin.elim0
  | k + 1, ch => Fin.cons ((CausalTranscript.oneChallenge F).transcript ch.right.left ⟨0, by decide⟩)
      (roundChallenges k ch.right.right)

/-- Causal two-value messages followed by their fresh challenges. -/
def roundFamily {σ : Type} [Fintype σ] [DecidableEq σ]
    (nodes : Sumcheck.Nodes F) (pe : (σ → F) → F) (env : σ → F) :
    (todo : List σ) → CausalTranscript (rounds F todo.length)
  | [] => CausalTranscript.empty _
  | v :: vs =>
    (CausalTranscript.oneMessage (marginalFn pe (Function.update env v 0) vs,
      marginalFn pe (Function.update env v (nodes.point 2)) vs)).append (fun _ =>
      (CausalTranscript.oneChallenge F).append (fun tr =>
        roundFamily nodes pe (Function.update env v (tr ⟨0, by decide⟩)) vs))

/-- `roundFamily` with both values of round `j` sent minus the pads `pads j`. -/
def maskedRoundFamily {σ : Type} [Fintype σ] [DecidableEq σ]
    (nodes : Sumcheck.Nodes F) (pe : (σ → F) → F) (env : σ → F) :
    (todo : List σ) → (Fin todo.length → Fin 2 → F) → CausalTranscript (rounds F todo.length)
  | [], _ => CausalTranscript.empty _
  | v :: vs, pads =>
    (CausalTranscript.oneMessage (marginalFn pe (Function.update env v 0) vs - pads 0 0,
      marginalFn pe (Function.update env v (nodes.point 2)) vs - pads 0 1)).append (fun _ =>
      (CausalTranscript.oneChallenge F).append (fun tr =>
        maskedRoundFamily nodes pe (Function.update env v (tr ⟨0, by decide⟩)) vs
          (fun k => pads k.succ)))

theorem maskedRoundFamily_zero {σ : Type} [Fintype σ] [DecidableEq σ]
    (nodes : Sumcheck.Nodes F) (pe : (σ → F) → F) (env : σ → F) (todo : List σ) :
    maskedRoundFamily nodes pe env todo (fun _ _ => 0) = roundFamily nodes pe env todo := by
  induction todo generalizing env with
  | nil => rfl
  | cons v vs ih =>
    simp only [maskedRoundFamily, roundFamily, sub_zero, ih]
    rfl

/-- The decoded masked rounds are the masked honest rounds at the actual challenges. -/
theorem maskedRoundFamily_messages {σ : Type} [Fintype σ] [DecidableEq σ]
    (nodes : Sumcheck.Nodes F) (p : MvPolynomial σ F) (env : σ → F)
    (todo : List σ) (pads : Fin todo.length → Fin 2 → F) (ch : (rounds F todo.length).Challenges) :
    roundMessages F todo.length ((maskedRoundFamily nodes (fun e => MvPolynomial.eval e p) env todo pads).transcript ch) =
      fun j => maskMessage (pads j)
        (honestRounds nodes p env todo (roundChallenges todo.length ch) j) := by
  induction todo generalizing env with
  | nil => exact funext fun j => Fin.elim0 j
  | cons v vs ih =>
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [List.length_cons, maskedRoundFamily, CausalTranscript.append, honestRounds,
        Fin.cons_zero, honestMessage, round_eval_marginalFn]
      rfl
    · let c := ((CausalTranscript.oneChallenge F).transcript ch.right.left) ⟨0, by decide⟩
      change roundMessages F vs.length
        (((maskedRoundFamily nodes (fun e => MvPolynomial.eval e p) env (v :: vs) pads).transcript ch).right.right) j =
          maskMessage (pads j.succ) (honestRounds nodes p (Function.update env v c) vs
            (roundChallenges vs.length ch.right.right) j)
      have houter := CausalTranscript.append_right
        (CausalTranscript.oneMessage
          (marginalFn (fun e => MvPolynomial.eval e p) (Function.update env v 0) vs - pads 0 0,
          marginalFn (fun e => MvPolynomial.eval e p) (Function.update env v (nodes.point 2)) vs -
            pads 0 1))
        (fun _ => (CausalTranscript.oneChallenge F).append (fun tr =>
          maskedRoundFamily nodes (fun e => MvPolynomial.eval e p)
            (Function.update env v (tr ⟨0, by decide⟩)) vs (fun k => pads k.succ))) ch
      change ((maskedRoundFamily nodes (fun e => MvPolynomial.eval e p) env (v :: vs) pads).transcript ch).right = _ at houter
      rw [houter]
      have hinner := CausalTranscript.append_right (CausalTranscript.oneChallenge F)
        (fun tr => maskedRoundFamily nodes (fun e => MvPolynomial.eval e p)
          (Function.update env v (tr ⟨0, by decide⟩)) vs (fun k => pads k.succ)) ch.right
      erw [hinner]
      exact congrFun (ih (Function.update env v c) (fun k => pads k.succ) ch.right.right) j

def roundFamilyOfLength {σ : Type} [Fintype σ] [DecidableEq σ]
    (nodes : Sumcheck.Nodes F) (pe : (σ → F) → F) (env : σ → F)
    (todo : List σ) (k : ℕ) (h : todo.length = k) : CausalTranscript (rounds F k) :=
  h ▸ roundFamily nodes pe env todo

def maskedRoundFamilyOfLength {σ : Type} [Fintype σ] [DecidableEq σ]
    (nodes : Sumcheck.Nodes F) (pe : (σ → F) → F) (env : σ → F)
    (todo : List σ) (k : ℕ) (h : todo.length = k) (pads : Fin todo.length → Fin 2 → F) :
    CausalTranscript (rounds F k) :=
  h ▸ maskedRoundFamily nodes pe env todo pads

theorem maskedRoundFamilyOfLength_zero {σ : Type} [Fintype σ] [DecidableEq σ]
    (nodes : Sumcheck.Nodes F) (pe : (σ → F) → F) (env : σ → F)
    (todo : List σ) (k : ℕ) (h : todo.length = k) :
    maskedRoundFamilyOfLength nodes pe env todo k h (fun _ _ => 0) =
      roundFamilyOfLength nodes pe env todo k h := by
  rw [maskedRoundFamilyOfLength, roundFamilyOfLength, maskedRoundFamily_zero]

theorem maskedRoundFamilyOfLength_messages {σ : Type} [Fintype σ] [DecidableEq σ]
    (nodes : Sumcheck.Nodes F) (p : MvPolynomial σ F) (env : σ → F)
    (todo : List σ) (k : ℕ) (h : todo.length = k) (pads : Fin todo.length → Fin 2 → F)
    (ch : (rounds F k).Challenges) (j : Fin todo.length) :
    roundMessages F k ((maskedRoundFamilyOfLength nodes (fun e => MvPolynomial.eval e p) env todo k h pads).transcript ch)
      ⟨j.val, by omega⟩ =
      maskMessage (pads j) (honestRounds nodes p env todo
        (fun i => roundChallenges k ch ⟨i.val, by omega⟩) j) := by
  subst k
  exact congrFun (maskedRoundFamily_messages nodes p env todo pads ch) j

/-- The round challenges of a completed sumcheck phase, indexed by the schedule. -/
def scheduleChallenges (i : ℕ) (rt : (rounds F (2*i)).Transcript (Fin.last (roundLength (2*i)))) :
    Fin (schedule i).length → F :=
  fun j => (roundMessages F (2*i) rt
    ⟨j.val, by simpa only [schedule_length] using j.isLt⟩).challenge

theorem scheduleChallenges_masked (nodes : Sumcheck.Nodes F) {i : ℕ}
    (p : MvPolynomial (Vars i) F) (env : Vars i → F)
    (pads : Fin (schedule i).length → Fin 2 → F) (ch : (rounds F (2*i)).Challenges) :
    scheduleChallenges i ((maskedRoundFamilyOfLength nodes (fun e => MvPolynomial.eval e p) env
      (schedule i) (2*i)
      (schedule_length i) pads).transcript ch) =
      fun j => roundChallenges (2*i) ch ⟨j.val, by simpa only [schedule_length] using j.isLt⟩ := by
  funext j
  simp only [scheduleChallenges]
  rw [maskedRoundFamilyOfLength_messages, maskMessage_challenge, honestRounds_challenge]

variable [DecidableEq F]

/-- Actual numeric circuit schedule with an online honest prover. The round messages are
marginals of the executable layer evaluation `targetEval` (`LayerSumcheck.marginalFn`). -/
def circuitFamily (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) : CausalTranscript (circuit F C) :=
  match C with
  | .input _ => CausalTranscript.oneChallenge F
  | .layer (inDim := i) Q tail =>
    (CausalTranscript.oneChallenge (F × F)).append (fun ab =>
      let a := (ab ⟨0, by decide⟩).1
      let b := (ab ⟨0, by decide⟩).2
      (roundFamilyOfLength nodes (targetEval Q (tail.eval input) g0 g1 a b) (fun _ => 0) (schedule i) (2*i) (schedule_length i)).append
        (fun rt =>
          let r := fun j : Fin (schedule i).length =>
            (roundMessages F (2*i) rt ⟨j.val, by simpa only [schedule_length] using j.isLt⟩).challenge
          let env := install (fun _ => 0) (schedule i) r
          (CausalTranscript.oneMessage
            (ClaimEvaluation.evalTable (tail.eval input) (fun j => env (false,j)),
             ClaimEvaluation.evalTable (tail.eval input) (fun j => env (true,j)))).append
              (fun _ => circuitFamily nodes tail input (fun j => env (false,j)) (fun j => env (true,j)))))

/-- `circuitFamily` with every revealed value sent minus its committed pad.
The pads are fixed before the first challenge. -/
def maskedCircuitFamily (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (pads : Pads C) :
    CausalTranscript (circuit F C) :=
  match C with
  | .input _ => CausalTranscript.oneChallenge F
  | .layer (inDim := i) Q tail =>
    (CausalTranscript.oneChallenge (F × F)).append (fun ab =>
      let a := (ab ⟨0, by decide⟩).1
      let b := (ab ⟨0, by decide⟩).2
      (maskedRoundFamilyOfLength nodes (targetEval Q (tail.eval input) g0 g1 a b) (fun _ => 0) (schedule i) (2*i) (schedule_length i)
        pads.polynomial).append
        (fun rt =>
          let env := install (fun _ => 0) (schedule i) (scheduleChallenges i rt)
          (CausalTranscript.oneMessage
            (ClaimEvaluation.evalTable (tail.eval input) (fun j => env (false,j)) -
                pads.claim ⟨0, by decide⟩,
             ClaimEvaluation.evalTable (tail.eval input) (fun j => env (true,j)) -
                pads.claim ⟨1, by decide⟩)).append
              (fun _ => maskedCircuitFamily nodes tail input (fun j => env (false,j))
                (fun j => env (true,j)) pads.tail)))

theorem maskedCircuitFamily_zero (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) :
    maskedCircuitFamily nodes C input g0 g1 (zeroPads C) = circuitFamily nodes C input g0 g1 := by
  induction C with
  | input d => rfl
  | layer Q tail ih =>
    have ih' : ∀ g0 g1, maskedCircuitFamily nodes tail input g0 g1 (zeroPads tail) =
        circuitFamily nodes tail input g0 g1 := fun g0 g1 => ih input g0 g1
    simp only [maskedCircuitFamily, circuitFamily, zeroPads, maskedRoundFamilyOfLength_zero,
      sub_zero, ih']
    rfl

/-- The verifier challenges of the circuit phase, in the shape of the honest trace. -/
def circuitChallenges {d : ℕ} : (C : Circuit F d) → (circuit F C).Challenges → Completeness.Challenges C
  | .input _, ch => (CausalTranscript.oneChallenge F).transcript ch ⟨0, by decide⟩
  | .layer (inDim := i) _ tail, ch =>
    ⟨((CausalTranscript.oneChallenge (F × F)).transcript ch.left ⟨0, by decide⟩).1,
     ((CausalTranscript.oneChallenge (F × F)).transcript ch.left ⟨0, by decide⟩).2,
     fun j => roundChallenges (2*i) ch.right.left ⟨j.val, by simpa only [schedule_length] using j.isLt⟩,
     circuitChallenges tail ch.right.right.right⟩

/-- One layer of the masked family, with the round challenges read from `ch`. -/
theorem maskedCircuitFamily_layer (nodes : Sumcheck.Nodes F) {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (tail : Circuit F inDim) (input : Fin (2^(Circuit.layer Q tail).inputDim) → F)
    (g0 g1 : Fin outDim → F)
    (pads : Pads (.layer Q tail)) (ch : (circuit F (.layer Q tail)).Challenges) :
    (maskedCircuitFamily nodes (.layer Q tail) input g0 g1 pads).transcript ch =
      Transcript.join ((CausalTranscript.oneChallenge (F × F)).transcript ch.left)
        (Transcript.join ((maskedRoundFamilyOfLength nodes
            (fun e => MvPolynomial.eval e
              (target Q (ClaimEvaluation.binaryLabelEquiv inDim) (cubeTable (tail.eval input))
                (weight g0 g1 (circuitChallenges (.layer Q tail) ch).alpha)
                (circuitChallenges (.layer Q tail) ch).beta))
            (fun _ => 0) (schedule inDim)
            (2*inDim) (schedule_length inDim) pads.polynomial).transcript ch.right.left)
          (Transcript.join ((CausalTranscript.oneMessage
              (ClaimEvaluation.evalTable (tail.eval input) (fun j => install (fun _ => 0)
                  (schedule inDim) (circuitChallenges (.layer Q tail) ch).rounds (false,j)) -
                  pads.claim ⟨0, by decide⟩,
               ClaimEvaluation.evalTable (tail.eval input) (fun j => install (fun _ => 0)
                  (schedule inDim) (circuitChallenges (.layer Q tail) ch).rounds (true,j)) -
                  pads.claim ⟨1, by decide⟩)).transcript ch.right.right.left)
            ((maskedCircuitFamily nodes tail input
              (fun j => install (fun _ => 0) (schedule inDim)
                (circuitChallenges (.layer Q tail) ch).rounds (false,j))
              (fun j => install (fun _ => 0) (schedule inDim)
                (circuitChallenges (.layer Q tail) ch).rounds (true,j))
              pads.tail).transcript ch.right.right.right))) := by
  simp only [maskedCircuitFamily, CausalTranscript.append, targetEval_eq]
  rw [scheduleChallenges_masked]
  rfl

/-- The decoded masked circuit transcript is the masked honest trace at the
actual challenges. -/
theorem maskedCircuitFamily_trace (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (pads : Pads C)
    (ch : (circuit F C).Challenges) :
    circuitTrace F C ((maskedCircuitFamily nodes C input g0 g1 pads).transcript ch) =
      mask C pads (honestTrace nodes C input g0 g1 (circuitChallenges C ch)) := by
  induction C with
  | input d => rfl
  | @layer outDim inDim T Q tail ih =>
    rw [maskedCircuitFamily_layer]
    simp only [circuitTrace]
    repeat (first | erw [ProtocolSpec.Transcript.left_join] | erw [ProtocolSpec.Transcript.right_join])
    rw [ih input]
    show LayerTrace.mk _ _ _ _ _ = LayerTrace.mk _ _ _ _ _
    congr 1
    · funext j
      exact maskedRoundFamilyOfLength_messages nodes _ _ (schedule inDim) (2*inDim)
        (schedule_length inDim) pads.polynomial ch.right.left j
    · funext h
      fin_cases h <;> rfl

/-! ### Transcripts that send given values -/

/-- The sumcheck-phase transcript that sends `vals j 0`, `vals j 1` as the two values of round
`j`, whatever the challenges. -/
def valueRoundFamily : (k : ℕ) → (Fin k → Fin 2 → F) → CausalTranscript (rounds F k)
  | 0, _ => CausalTranscript.empty _
  | k + 1, vals =>
    (CausalTranscript.oneMessage (vals 0 0, vals 0 1)).append (fun _ =>
      (CausalTranscript.oneChallenge F).append (fun _ =>
        valueRoundFamily k (fun j => vals j.succ)))

/-- The masked round transcript sends the masked honest values. -/
theorem maskedRoundFamily_eq_value {σ : Type} [Fintype σ] [DecidableEq σ]
    (nodes : Sumcheck.Nodes F) (p : MvPolynomial σ F) (env : σ → F)
    (todo : List σ) (pads : Fin todo.length → Fin 2 → F) (ch : (rounds F todo.length).Challenges) :
    (maskedRoundFamily nodes (fun e => MvPolynomial.eval e p) env todo pads).transcript ch =
      (valueRoundFamily todo.length fun j =>
        ![(honestRounds nodes p env todo (roundChallenges _ ch) j).p0 - pads j 0,
          (honestRounds nodes p env todo (roundChallenges _ ch) j).p2 - pads j 1]).transcript ch := by
  induction todo generalizing env with
  | nil => exact funext fun i => i.elim0
  | cons v vs ih =>
    have hrest := ih (Function.update env v
      ((CausalTranscript.oneChallenge F).transcript ch.right.left ⟨0, by decide⟩))
      (fun k => pads k.succ) ch.right.right
    simp only [maskedRoundFamily, CausalTranscript.append, honestRounds, Fin.cons_zero,
      honestMessage, round_eval_marginalFn]
    exact congrArg (fun t => Transcript.join _ (Transcript.join
      ((CausalTranscript.oneChallenge F).transcript ch.right.left) t)) hrest

theorem maskedRoundFamilyOfLength_eq_value {σ : Type} [Fintype σ] [DecidableEq σ]
    (nodes : Sumcheck.Nodes F) (p : MvPolynomial σ F) (env : σ → F)
    (todo : List σ) (k : ℕ) (h : todo.length = k) (pads : Fin todo.length → Fin 2 → F)
    (ch : (rounds F k).Challenges) :
    (maskedRoundFamilyOfLength nodes (fun e => MvPolynomial.eval e p) env todo k h pads).transcript ch =
      (valueRoundFamily k fun j =>
        ![(honestRounds nodes p env todo (fun i => roundChallenges k ch ⟨i.val, by omega⟩)
            ⟨j.val, by omega⟩).p0 - pads ⟨j.val, by omega⟩ 0,
          (honestRounds nodes p env todo (fun i => roundChallenges k ch ⟨i.val, by omega⟩)
            ⟨j.val, by omega⟩).p2 - pads ⟨j.val, by omega⟩ 1]).transcript ch := by
  subst k
  exact maskedRoundFamily_eq_value nodes p env todo pads ch

/-- The circuit-phase transcript that sends the given values `vals`, in the shape of the free
pads: the two values of every sumcheck round and the two wire claims of every layer, whatever
the challenges. -/
def valueCircuitFamily {d : ℕ} (C : Circuit F d) (vals : FreePads C) :
    CausalTranscript (circuit F C) :=
  match C, vals with
  | .input _, _ => CausalTranscript.oneChallenge F
  | .layer (inDim := i) _ tail, vals =>
    (CausalTranscript.oneChallenge (F × F)).append (fun _ =>
      (valueRoundFamily (2*i) (fun j => vals.1 ⟨j.val, by
          simpa only [schedule_length] using j.isLt⟩)).append (fun _ =>
        (CausalTranscript.oneMessage (vals.2.1 0, vals.2.1 1)).append (fun _ =>
          valueCircuitFamily tail vals.2.2)))

/-- One layer of the value family, with the round challenges read from `ch`. -/
theorem valueCircuitFamily_layer {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (tail : Circuit F inDim) (vals : FreePads (.layer Q tail))
    (ch : (circuit F (.layer Q tail)).Challenges) :
    (valueCircuitFamily (.layer Q tail) vals).transcript ch =
      Transcript.join ((CausalTranscript.oneChallenge (F × F)).transcript ch.left)
        (Transcript.join ((valueRoundFamily (2*inDim) fun j => vals.1 ⟨j.val, by
            simpa only [schedule_length] using j.isLt⟩).transcript ch.right.left)
          (Transcript.join ((CausalTranscript.oneMessage (vals.2.1 0, vals.2.1 1)).transcript
              ch.right.right.left)
            ((valueCircuitFamily tail vals.2.2).transcript ch.right.right.right))) := rfl

/-- **The masked circuit transcript sends the revealed honest values minus the free pads.** -/
theorem maskedCircuitFamily_eq_value (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (π : FreePads C)
    (ch : (circuit F C).Challenges) :
    (maskedCircuitFamily nodes C input g0 g1 π.pads).transcript ch =
      (valueCircuitFamily C
        (revealed C (honestTrace nodes C input g0 g1 (circuitChallenges C ch)) - π)).transcript ch := by
  induction C with
  | input d => rfl
  | @layer outDim inDim T Q tail ih =>
    rw [maskedCircuitFamily_layer]
    rw [maskedRoundFamilyOfLength_eq_value]
    erw [ih input _ _ π.2.2 ch.right.right.right]
    rw [valueCircuitFamily_layer]
    congr 3
    refine congrArg (valueRoundFamily (2*inDim)) (funext fun j => funext fun x => ?_)
    fin_cases x <;> rfl

/-- The honest transcript family: the initial point of `F^d` drawn by the first verifier move,
then the circuit phase at that point. -/
def family (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) : CausalTranscript (spec F C) :=
  (CausalTranscript.oneChallenge (Fin d → F)).append (fun init =>
    let g := init ⟨0, by decide⟩
    circuitFamily nodes C input g g)

/-- The honest prover of the typed GKR schedule, with every revealed value sent
minus its committed pad, as the C++ sends it. -/
def maskedFamily (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (pads : Pads C) :
    CausalTranscript (spec F C) :=
  (CausalTranscript.oneChallenge (Fin d → F)).append (fun init =>
    let g := init ⟨0, by decide⟩
    maskedCircuitFamily nodes C input g g pads)

theorem maskedFamily_zero (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) :
    maskedFamily nodes C input (zeroPads C) = family nodes C input := by
  simp only [maskedFamily, family, maskedCircuitFamily_zero]
  rfl

/-- The initial point both families read from the first verifier move. -/
def initialChallengePoint {d : ℕ} (C : Circuit F d) (ch : (spec F C).Challenges) :
    Fin d → F :=
  (CausalTranscript.oneChallenge (Fin d → F)).transcript ch.left ⟨0, by decide⟩

theorem maskedFamily_transcript (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (pads : Pads C) (ch : (spec F C).Challenges) :
    (maskedFamily nodes C input pads).transcript ch =
      Transcript.join ((CausalTranscript.oneChallenge (Fin d → F)).transcript ch.left)
        ((maskedCircuitFamily nodes C input (initialChallengePoint C ch)
          (initialChallengePoint C ch) pads).transcript ch.right) := rfl

theorem maskedFamily_initialPoint (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (pads : Pads C) (ch : (spec F C).Challenges) :
    ProtocolEvents.initialPoint F C ((maskedFamily nodes C input pads).transcript ch) =
      initialChallengePoint C ch := by
  unfold ProtocolEvents.initialPoint initialValues
  rw [maskedFamily_transcript]
  repeat (first | erw [ProtocolSpec.Transcript.left_join] | erw [ProtocolSpec.Transcript.right_join])
  try rfl

/-- The masked family's trace is the masked honest trace at the actual challenges. -/
theorem maskedFamily_trace (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (pads : Pads C) (ch : (spec F C).Challenges) :
    trace F C ((maskedFamily nodes C input pads).transcript ch) =
      mask C pads (honestTrace nodes C input (initialChallengePoint C ch)
        (initialChallengePoint C ch) (circuitChallenges C ch.right)) := by
  unfold trace circuitTranscript
  rw [maskedFamily_transcript]
  repeat (first | erw [ProtocolSpec.Transcript.left_join] | erw [ProtocolSpec.Transcript.right_join])
  exact maskedCircuitFamily_trace nodes C input _ _ pads ch.right

/-- Completeness with arbitrary committed pads satisfying the product relation:
the masked family reaches the soundness reduction's terminal claim for every
verifier challenge. -/
theorem maskedFamily_terminal (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (pads : Pads C) (h : C.Satisfied input)
    (hp : ProductsHold C pads) (ch : (spec F C).Challenges) :
    ProtocolEvents.terminal F nodes C (input, pads)
      ((maskedFamily nodes C input pads).transcript ch) := by
  refine ⟨hp, ?_⟩
  rw [maskedFamily_initialPoint, maskedFamily_trace]
  exact masked_honest_check nodes C pads input _ _ _ h

/-- **The simulated GKR transcript**: the initial verifier move, then the circuit phase sending
the values `vals` (`valueCircuitFamily`). No prover runs: every message is a coordinate of
`vals`. -/
def valueFamily {d : ℕ} (C : Circuit F d) (vals : FreePads C) : CausalTranscript (spec F C) :=
  (CausalTranscript.oneChallenge (Fin d → F)).append (fun _ =>
    valueCircuitFamily C vals)

/-- The masked transcript at the free pads `π` is the value family at the revealed honest values
minus `π`. -/
theorem maskedFamily_eq_value (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (π : FreePads C) (ch : (spec F C).Challenges) :
    (maskedFamily nodes C input π.pads).transcript ch =
      (valueFamily C (revealed C (honestTrace nodes C input (initialChallengePoint C ch)
        (initialChallengePoint C ch) (circuitChallenges C ch.right)) - π)).transcript ch := by
  rw [maskedFamily_transcript]
  exact congrArg (Transcript.join _) (maskedCircuitFamily_eq_value nodes C input _ _ π ch.right)

/-- **Hiding of the masked GKR transcript.** For fixed challenges, the honest masked transcript
under uniform free pads has the law of the value family under uniform values: the free pads
`π` map to the sent values `revealed − π`, where the revealed honest values depend only on the
input and the challenges, so the map is a bijection of the free pads. -/
theorem maskedFamily_identDistrib [Fintype F] (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (input : Fin (2^C.inputDim) → F)
    (ch : (spec F C).Challenges) :
    (fun π : FreePads C => (maskedFamily nodes C input π.pads).transcript ch) =ᵈ
      (fun vals : FreePads C => (valueFamily C vals).transcript ch) :=
  IdentDistrib.of_equiv (Equiv.subLeft (revealed C (honestTrace nodes C input
      (initialChallengePoint C ch) (initialChallengePoint C ch) (circuitChallenges C ch.right))))
    fun π => maskedFamily_eq_value nodes C input π ch

@[simp] theorem flat_zeroPads {d : ℕ} (C : Circuit F d) :
    CircuitFlatten.pads C (fun _ => (0 : F)) = zeroPads C := by
  induction C with
  | input d => rfl
  | layer Q tail ih =>
    simp only [CircuitFlatten.pads, zeroPads, ih]
    rfl

/-! ### The value families are bijective -/

/-- The values of `k + 1` sumcheck rounds: the first round's two values, and the later rounds'. -/
def roundValuesEquiv (k : ℕ) : (Fin (k + 1) → Fin 2 → F) ≃ (F × F) × (Unit × (Fin k → Fin 2 → F)) where
  toFun v := ((v 0 0, v 0 1), ((), fun j => v j.succ))
  invFun x := Fin.cons ![x.1.1, x.1.2] x.2.2
  left_inv v := by
    funext i b
    refine Fin.cases ?_ (fun j => rfl) i
    fin_cases b <;> rfl
  right_inv x := by
    obtain ⟨⟨a, b⟩, ⟨⟩, t⟩ := x
    rfl

/-- **The sumcheck value family is bijective**: the challenges and the values give the transcript,
and back. -/
theorem valueRoundFamily_bijective : (k : ℕ) →
    CausalTranscript.ValuesBijective (valueRoundFamily (F := F) k)
  | 0 => (CausalTranscript.valuesBijective_empty _).comp_equiv (Equiv.ofUnique _ _)
  | k + 1 => ((CausalTranscript.valuesBijective_oneMessage (F × F)).append
      ((CausalTranscript.valuesBijective_oneChallenge F).append
        (valueRoundFamily_bijective k))).comp_equiv (roundValuesEquiv k)

/-- The values of a layer of the circuit phase, in the order the layer sends them: nothing for the
layer challenge, the sumcheck rounds' values, the two wire claims, then the tail's values. -/
def layerValuesEquiv {outDim inDim T : ℕ} (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (tail : Circuit F inDim) :
    FreePads (.layer Q tail) ≃
      Unit × ((Fin (2 * inDim) → Fin 2 → F) × ((F × F) × FreePads tail)) where
  toFun vals := ((), (fun j => vals.1 ⟨j.val, by simpa only [schedule_length] using j.isLt⟩,
    ((vals.2.1 0, vals.2.1 1), vals.2.2)))
  invFun x := (fun j => x.2.1 ⟨j.val, by simpa only [schedule_length] using j.isLt⟩,
    ![x.2.2.1.1, x.2.2.1.2], x.2.2.2)
  left_inv vals := by
    obtain ⟨r, w, t⟩ := vals
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext b
    fin_cases b <;> rfl
  right_inv x := by
    obtain ⟨⟨⟩, r, ⟨a, b⟩, t⟩ := x
    rfl

/-- **The circuit-phase value family is bijective.** -/
theorem valueCircuitFamily_bijective : {d : ℕ} → (C : Circuit F d) →
    CausalTranscript.ValuesBijective (valueCircuitFamily C)
  | _, .input _ => CausalTranscript.valuesBijective_oneChallenge F
  | _, .layer (inDim := b) Q tail =>
    ((CausalTranscript.valuesBijective_oneChallenge (F × F)).append
      ((valueRoundFamily_bijective (2 * b)).append
        ((CausalTranscript.valuesBijective_oneMessage (F × F)).append
          (valueCircuitFamily_bijective tail)))).comp_equiv (layerValuesEquiv Q tail)

/-- **The GKR value family is bijective**: the simulated GKR transcript, as a function of the
challenges and the sent values, is a bijection onto the full transcripts. -/
theorem valueFamily_bijective {d : ℕ} (C : Circuit F d) :
    CausalTranscript.ValuesBijective (valueFamily C) :=
  (valueCircuitFamily_bijective C).oneChallenge_append

end GordieHowe.GKR.HonestTranscript
