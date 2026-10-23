-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.PadTranslation
public import GordieHowe.ProofSystem.GKR.TranscriptExecution

@[expose] public section

/-!
# Source-derived flat GKR transcript fields

The flat constraint builder receives interpolation coefficients and wiring
values computed from the actual recursive circuit and its challenge stream.
These are not free verifier parameters. Layer numbering is output to input.
-/
namespace GordieHowe.GKR.CircuitFlatten
open IOP
open GKR.Circuit CircuitProtocol LayerProtocol LayerSumcheck PadTranslation
variable {F : Type} [Field F]

def roundCount {d : ℕ} (C : Circuit F d) : Fin C.depth → ℕ :=
  match C with
  | .input _ => Fin.elim0
  | .layer (inDim := i) _ tail => Fin.cases (schedule i).length (roundCount tail)

structure LayerValues (F : Type) (r : ℕ) where
  alpha : F
  rounds : Fin r → Message F
  wc : Fin 2 → F

def layerValues {d : ℕ} (C : Circuit F d) (tr : Trace C) :
    (l : Fin C.depth) → LayerValues F (roundCount C l) :=
  match C with
  | .input _ => fun l => Fin.elim0 l
  | .layer _ tail => Fin.cases ⟨tr.alpha, tr.rounds, tr.wc⟩ (layerValues tail tr.tail)

def inputAlpha {d : ℕ} (C : Circuit F d) (tr : Trace C) : F :=
  match C with
  | .input _ => tr
  | .layer _ tail => inputAlpha tail tr.tail

/-- Final evaluation points depend only on scalar challenges, including when
the prover messages are masked. -/
def inputPoints (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (g0 g1 : Fin d → F) (tr : Trace C) :
    (Fin C.inputDim → F) × (Fin C.inputDim → F) :=
  match C with
  | .input _ => (g0, g1)
  | .layer _ tail =>
    let env := (layerRun nodes 0 0 tr).1
    inputPoints nodes tail (fun j => env (false,j)) (fun j => env (true,j)) tr.tail

noncomputable def wiringValues (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (g0 g1 : Fin d → F) (tr : Trace C) : Fin C.depth → F :=
  match C with
  | .input _ => Fin.elim0
  | .layer Q tail =>
    let env := (layerRun nodes 0 0 tr).1
    Fin.cases (layerWiring Q g0 g1 tr.alpha tr.beta env)
      (wiringValues nodes tail (fun j => env (false,j)) (fun j => env (true,j)) tr.tail)

/-- `wiringValues` computed with the executable layer wiring (`layerWiringDec`). -/
def wiringValuesDec [DecidableEq F] (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (g0 g1 : Fin d → F) (tr : Trace C) : Fin C.depth → F :=
  match C with
  | .input _ => Fin.elim0
  | .layer Q tail =>
    let env := (layerRun nodes 0 0 tr).1
    Fin.cases (layerWiringDec Q g0 g1 tr.alpha tr.beta env)
      (wiringValuesDec nodes tail (fun j => env (false,j)) (fun j => env (true,j)) tr.tail)

theorem wiringValuesDec_eq [DecidableEq F] (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (g0 g1 : Fin d → F) (tr : Trace C) :
    wiringValuesDec nodes C g0 g1 tr = wiringValues nodes C g0 g1 tr := by
  induction C with
  | input => rfl
  | layer Q tail ih =>
    simp only [wiringValuesDec, wiringValues, layerWiringDec_eq, ih]
    rfl

def PadIndex {d : ℕ} (C : Circuit F d) : Type :=
  (l : Fin C.depth) × ((Fin (roundCount C l) × Fin 2) ⊕ Fin 3)

/-- The nonempty source circuit fixes all allocation coordinates before GKR. -/
def layout {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (tail : Circuit F inDim) :
    Transcript.Layout (PadIndex (.layer Q tail)) tail.depth where
  rounds := roundCount (.layer Q tail)
  polyPad l r h := ⟨l, .inl (r,h)⟩
  claimPad l h := ⟨l, .inr h⟩

def transcript [DecidableEq F] (nodes : Sumcheck.Nodes F) {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (tail : Circuit F inDim)
    (g0 g1 : Fin outDim → F) (tr : Trace (.layer Q tail)) :
    GKR.Transcript F (PadIndex (.layer Q tail)) tail.depth
      (layout Q tail) where
  alpha l := (layerValues (.layer Q tail) tr l).alpha
  lag l r := Sumcheck.Round.coefficients nodes
    ((layerValues (.layer Q tail) tr l).rounds r).challenge
  hp l r h := if h = 0 then ((layerValues (.layer Q tail) tr l).rounds r).p0
    else ((layerValues (.layer Q tail) tr l).rounds r).p2
  wc l := (layerValues (.layer Q tail) tr l).wc
  eqq := wiringValuesDec nodes (.layer Q tail) g0 g1 tr
  inputAlpha := inputAlpha (.layer Q tail) tr

def pads {d : ℕ} (C : Circuit F d) (p : PadIndex C → F) : Pads C :=
  match C with
  | .input _ => ()
  | .layer _ tail =>
    { polynomial := fun r h => p ⟨⟨0, Nat.zero_lt_succ _⟩, .inl (r,h)⟩
      claim := fun h => p ⟨⟨0, Nat.zero_lt_succ _⟩, .inr h⟩
      tail := pads tail (fun x => p ⟨x.1.succ, x.2⟩) }

/-- The structured pads stored at their flat indices; the inverse of `pads`
(`pads_flatPads`). -/
def flatPads {d : ℕ} : (C : Circuit F d) → Pads C → PadIndex C → F
  | .input _, _, x => x.1.elim0
  | .layer Q tail, p, x =>
    Fin.cases (motive := fun l =>
        ((Fin (roundCount (Circuit.layer Q tail) l) × Fin 2) ⊕ Fin 3) → F)
      (Sum.elim (fun rh => p.polynomial rh.1 rh.2) p.claim)
      (fun l s => flatPads tail p.tail ⟨l, s⟩) x.1 x.2

@[simp] theorem pads_flatPads {d : ℕ} (C : Circuit F d) (p : Pads C) :
    pads C (flatPads C p) = p := by
  induction C with
  | input => rfl
  | layer Q tail ih =>
    change LayerPads.mk _ _ (pads tail (flatPads tail p.tail)) = p
    rw [ih]
    rfl

theorem inputAlpha_unmask {d : ℕ} (C : Circuit F d) (p : Pads C) (tr : Trace C) :
    inputAlpha C (unmask C p tr) = inputAlpha C tr := by
  induction C with
  | input => rfl
  | layer Q tail ih => exact ih _ _

theorem inputPoints_unmask (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (p : Pads C) (g0 g1 : Fin d → F) (tr : Trace C) :
    inputPoints nodes C g0 g1 (unmask C p tr) = inputPoints nodes C g0 g1 tr := by
  induction C with
  | input => rfl
  | layer Q tail ih =>
    change inputPoints nodes tail _ _ (unmask tail p.tail tr.tail) = _
    have he : (layerRun nodes 0 0 (unmask (.layer Q tail) p tr)).1 =
        (layerRun nodes 0 0 tr).1 := by
      unfold layerRun
      rw [run_env, run_env]
      rfl
    rw [he]
    exact ih _ _ _ _

/-- Incoming scalar at each layer, in output-to-input order. -/
def incoming {d : ℕ} (C : Circuit F d) (tr : Trace C) (c0 c1 : F) : Fin C.depth → F :=
  match C with
  | .input _ => Fin.elim0
  | .layer _ tail => Fin.cases (c0 + tr.alpha*c1)
      (incoming tail tr.tail (tr.wc 0) (tr.wc 1))

/-- Final pair combined by the actual terminal challenge. -/
def terminalValue {d : ℕ} (C : Circuit F d) (tr : Trace C) (c0 c1 : F) : F :=
  match C with
  | .input _ => c0 + (show F from tr)*c1
  | .layer _ tail => terminalValue tail tr.tail (tr.wc 0) (tr.wc 1)

def layerEquations (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (g0 g1 : Fin d → F) (tr : Trace C) (c0 c1 : F) : Prop :=
  ∀ l, (List.ofFn (layerValues C tr l).rounds).foldl (step nodes) (incoming C tr c0 c1 l) =
    wiringValues nodes C g0 g1 tr l * (layerValues C tr l).wc 0 * (layerValues C tr l).wc 1

def terminalEvaluation (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (input : Fin (2^C.inputDim) → F)
    (g0 g1 : Fin d → F) (tr : Trace C) : F :=
  ClaimEvaluation.evalTable input (inputPoints nodes C g0 g1 tr).1 +
    inputAlpha C tr * ClaimEvaluation.evalTable input (inputPoints nodes C g0 g1 tr).2

theorem layerRun_env_independent {d : ℕ} {Tail : Type} (nodes : Sumcheck.Nodes F)
    (tr : LayerTrace F d Tail) (c0 c1 : F) :
    (layerRun nodes c0 c1 tr).1 = (layerRun nodes 0 0 tr).1 := by
  unfold layerRun
  rw [run_env, run_env]

theorem check_iff_layerEquations (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (input : Fin (2^C.inputDim) → F)
    (g0 g1 : Fin d → F) (tr : Trace C) (c0 c1 : F) :
    check nodes C input g0 g1 c0 c1 tr ↔
      layerEquations nodes C g0 g1 tr c0 c1 ∧
      terminalValue C tr c0 c1 = terminalEvaluation nodes C input g0 g1 tr := by
  induction C generalizing c0 c1 with
  | input => simp [check, layerEquations, terminalValue, terminalEvaluation, inputPoints,
      inputAlpha, Circuit.depth]
  | layer Q tail ih =>
    change LayerTrace F _ (Trace tail) at tr
    change (Fin (2^tail.inputDim) → F) at input
    change ((layerRun nodes c0 c1 tr).2 =
      layerWiring Q g0 g1 tr.alpha tr.beta (layerRun nodes c0 c1 tr).1 * (tr.wc 0 * tr.wc 1) ∧
      check nodes tail input _ _ (tr.wc 0) (tr.wc 1) tr.tail) ↔ _
    rw [layerRun_env_independent nodes tr c0 c1, ih]
    have hs : (layerRun nodes c0 c1 tr).2 =
        (List.ofFn tr.rounds).foldl (step nodes) (c0+tr.alpha*c1) :=
      TranscriptExecution.run_scalar nodes _ _ _ _
    rw [hs]
    simp only [layerEquations, layerValues, incoming, wiringValues, terminalValue,
      terminalEvaluation, inputPoints, inputAlpha, Circuit.depth, Fin.forall_fin_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [mul_assoc]
    exact and_assoc.symm

theorem layerValues_unmask {d : ℕ} (C : Circuit F d) (p : PadIndex C → F)
    (tr : Trace C) (l : Fin C.depth) :
    layerValues C (unmask C (pads C p) tr) l =
      ⟨(layerValues C tr l).alpha,
        fun r => unmaskMessage (fun h => p ⟨l,.inl (r,h)⟩) ((layerValues C tr l).rounds r),
        fun h => (layerValues C tr l).wc h + p ⟨l,.inr ⟨h.val,by omega⟩⟩⟩ := by
  induction C with
  | input => exact Fin.elim0 l
  | layer Q tail ih =>
    change Fin (tail.depth+1) at l
    induction l using Fin.cases with
    | zero => rfl
    | succ l => exact ih _ _ _

theorem wiringValues_unmask (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (p : Pads C) (g0 g1 : Fin d → F) (tr : Trace C) :
    wiringValues nodes C g0 g1 (unmask C p tr) = wiringValues nodes C g0 g1 tr := by
  induction C with
  | input => rfl
  | layer Q tail ih =>
    change LayerTrace F _ (Trace tail) at tr
    change LayerPads F _ (Pads tail) at p
    have he : (layerRun nodes 0 0 (unmask (.layer Q tail) p tr)).1 =
        (layerRun nodes 0 0 tr).1 := by
      unfold layerRun
      rw [run_env, run_env]
      rfl
    simp only [wiringValues]
    rw [he]
    funext l
    induction l using Fin.cases with
    | zero => rfl
    | succ l => exact congrFun (ih _ _ _ _) l

theorem productsHold_iff {d : ℕ} (C : Circuit F d) (p : PadIndex C → F) :
    ProductsHold C (pads C p) ↔
      ∀ l, p ⟨l,.inr 0⟩ * p ⟨l,.inr 1⟩ = p ⟨l,.inr 2⟩ := by
  induction C with
  | input => simp [ProductsHold,Circuit.depth]
  | layer Q tail ih =>
    simp only [ProductsHold,pads]
    rw [ih]
    simp only [Circuit.depth, Fin.forall_fin_succ]
    rfl

theorem incoming_formula {d : ℕ} (C : Circuit F d) (tr : Trace C) (c0 c1 : F)
    (l : Fin C.depth) :
    incoming C tr c0 c1 l = if _h : l.val = 0 then c0 + (layerValues C tr l).alpha*c1 else
      let prev : Fin C.depth := ⟨l.val-1,by omega⟩
      (layerValues C tr prev).wc 0 + (layerValues C tr l).alpha*(layerValues C tr prev).wc 1 := by
  induction C generalizing c0 c1 with
  | input => exact Fin.elim0 l
  | layer Q tail ih =>
    change LayerTrace F _ (Trace tail) at tr
    change Fin (tail.depth+1) at l
    induction l using Fin.cases with
    | zero => rfl
    | succ l =>
      change incoming tail tr.tail (tr.wc 0) (tr.wc 1) l = _
      rw [ih]
      simp only [Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false,
        layerValues]
      cases tail with
      | input => exact Fin.elim0 l
      | layer Q' tail' =>
        change Fin (tail'.depth+1) at l
        induction l using Fin.cases with
        | zero => rfl
        | succ l =>
          simp only [Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false,
            ]
          rfl

theorem terminalValue_last {d : ℕ} (C : Circuit F d) (tr : Trace C) (c0 c1 : F)
    (hdepth : 0 < C.depth) :
    terminalValue C tr c0 c1 =
      (layerValues C tr ⟨C.depth-1,by omega⟩).wc 0 +
      inputAlpha C tr * (layerValues C tr ⟨C.depth-1,by omega⟩).wc 1 := by
  induction C generalizing c0 c1 with
  | input => simp [Circuit.depth] at hdepth
  | layer Q tail ih =>
    change LayerTrace F _ (Trace tail) at tr
    cases tail with
    | input => rfl
    | layer Q' tail' =>
      exact ih tr.tail (tr.wc 0) (tr.wc 1) (Nat.zero_lt_succ _)

variable (nodes : Sumcheck.Nodes F) {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (tail : Circuit F inDim)
    (g0 g1 : Fin outDim → F) (tr : Trace (.layer Q tail))
    (p : PadIndex (.layer Q tail) → F)

theorem flat_start [DecidableEq F] (l : Fin (tail.depth+1)) :
    Transcript.start (layout Q tail) (transcript nodes Q tail g0 g1 tr) p l =
      incoming (.layer Q tail) (unmask _ (pads _ p) tr) 0 0 l := by
  erw [incoming_formula]
  unfold Transcript.start
  split_ifs with h
  · simp
  · simp only [Transcript.unmasked, layerValues_unmask, transcript, layout]
    erw [layerValues_unmask]
    rfl

theorem flat_claim [DecidableEq F] (l : Fin (tail.depth+1)) :
    Transcript.claim (layout Q tail) (transcript nodes Q tail g0 g1 tr) p l =
      (List.ofFn (layerValues (.layer Q tail) (unmask _ (pads _ p) tr) l).rounds).foldl
        (step nodes) (incoming (.layer Q tail) (unmask _ (pads _ p) tr) 0 0 l) := by
  rw [TranscriptExecution.claim_eq_fold (layout Q tail)
    (transcript nodes Q tail g0 g1 tr) p nodes l
    (fun r => ((layerValues (.layer Q tail) tr l).rounds r).challenge) rfl,
    flat_start]
  erw [layerValues_unmask]
  congr 1

theorem flat_unmasked [DecidableEq F] (l : Fin (tail.depth+1)) (h : Fin 2) :
    Transcript.unmasked (layout Q tail) (transcript nodes Q tail g0 g1 tr) p l h =
      (layerValues (.layer Q tail) (unmask _ (pads _ p) tr) l).wc h := by
  erw [layerValues_unmask]
  rfl

theorem flat_value [DecidableEq F] :
    Transcript.value (layout Q tail) (transcript nodes Q tail g0 g1 tr) p =
      terminalValue (.layer Q tail) (unmask _ (pads _ p) tr) 0 0 := by
  rw [terminalValue_last (.layer Q tail) _ 0 0 (Nat.zero_lt_succ _)]
  simp only [Transcript.value, flat_unmasked, inputAlpha_unmask]
  rfl

theorem flat_padOK [DecidableEq F] :
    Transcript.PadOK (layout Q tail) (transcript nodes Q tail g0 g1 tr) p ↔
      ProductsHold (.layer Q tail) (pads _ p) ∧
      layerEquations nodes (.layer Q tail) g0 g1 (unmask _ (pads _ p) tr) 0 0 := by
  unfold Transcript.PadOK
  simp only [flat_claim, flat_unmasked]
  rw [productsHold_iff]
  unfold layerEquations
  rw [wiringValues_unmask]
  simp only [transcript, wiringValuesDec_eq]
  exact forall_and

theorem terminalEvaluation_unmask {d : ℕ} (C : Circuit F d) (p : Pads C)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (tr : Trace C) :
    terminalEvaluation nodes C input g0 g1 (unmask C p tr) =
      terminalEvaluation nodes C input g0 g1 tr := by
  simp only [terminalEvaluation, inputPoints_unmask, inputAlpha_unmask]

theorem terminalEvaluation_sum (input : Fin (2^tail.inputDim) → F) :
    terminalEvaluation nodes (.layer Q tail) input g0 g1 tr =
      ∑ i, PackedClaim.claimCoeff (inputPoints nodes (.layer Q tail) g0 g1 tr).1
        (inputPoints nodes (.layer Q tail) g0 g1 tr).2
        (inputAlpha (.layer Q tail) tr) i.val * input i := by
  simp only [terminalEvaluation, ClaimEvaluation.evalTable, PackedClaim.claimCoeff,
    add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
  rfl

/-- The concrete flat terminal constraints are exactly the recursive unmasked
verifier checks together with the committed product-pad equations. -/
theorem terminal_iff [DecidableEq F] (input : Fin (2^tail.inputDim) → F) :
    (Transcript.PadOK (layout Q tail) (transcript nodes Q tail g0 g1 tr) p ∧
      (∑ i, PackedClaim.claimCoeff (inputPoints nodes (.layer Q tail) g0 g1 tr).1
        (inputPoints nodes (.layer Q tail) g0 g1 tr).2
        (inputAlpha (.layer Q tail) tr) i.val * input i) =
        Transcript.value (layout Q tail) (transcript nodes Q tail g0 g1 tr) p) ↔
    ProductsHold (.layer Q tail) (pads _ p) ∧
      check nodes (.layer Q tail) input g0 g1 0 0 (unmask _ (pads _ p) tr) := by
  rw [flat_padOK, flat_value, ← terminalEvaluation_sum]
  erw [check_iff_layerEquations]
  have hu := terminalEvaluation_unmask nodes (.layer Q tail) (pads _ p) input g0 g1 tr
  rw [hu]
  constructor
  · rintro ⟨⟨hp,he⟩,hv⟩
    exact ⟨hp,he,hv.symm⟩
  · rintro ⟨hp,he,hv⟩
    exact ⟨⟨hp,he⟩,hv.symm⟩

end GordieHowe.GKR.CircuitFlatten
