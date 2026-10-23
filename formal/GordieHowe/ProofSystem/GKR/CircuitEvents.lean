-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.CircuitProtocol
public import GordieHowe.ProofSystem.GKR.AssertionTracking
public import GordieHowe.ProofSystem.GKR.PadTranslation

@[expose] public section

/-!
# Explicit challenge events for recursive no-copy GKR

A layer contributes its alpha/beta event and one event for each interleaved
sumcheck challenge. Hand-zero rounds additionally track the next layer's
assertion table. Thus no assertion-evaluation soundness premise remains in
the recursive deterministic theorem. Initial output/assertion evaluation is
a separate event; the terminal input uses one scalar batching event.
-/
namespace GordieHowe.GKR.CircuitEvents
open IOP
open GKR.Circuit CircuitProtocol LayerPolynomial LayerSumcheck LayerProtocol
open scoped Classical NNReal
variable {F : Type} [Field F]

/-- The assertion table at the current layer, computed from circuit input. -/
noncomputable def assertionTable {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) : Fin (2^d) → F :=
  match C with
  | .input _ => fun _ => 0
  | .layer Q tail => Layer.assertions Q (tail.eval input)

def HeadEscape {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g : Fin d → F) : Prop :=
  match C with
  | .input _ => False
  | .layer Q tail => AssertionEscape Q (tail.eval input) g

/-- The initial evaluation can hide a nonzero output or current assertion table. -/
def InitialEvent {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g : Fin d → F) : Prop :=
  OutputEscape (C.eval input) g ∨ HeadEscape C input g

/-- One event per actual verifier challenge in the recursive circuit phase. -/
def Index {d : ℕ} (C : Circuit F d) : Type :=
  match C with
  | .input _ => Unit
  | .layer (inDim := i) _ tail => Unit ⊕ (Fin (schedule i).length ⊕ Index tail)

instance indexFintype {d : ℕ} (C : Circuit F d) : Fintype (Index C) :=
  match C with
  | .input _ => inferInstanceAs (Fintype Unit)
  | .layer (inDim := i) _ tail =>
    letI := indexFintype tail
    inferInstanceAs (Fintype (Unit ⊕ (Fin (schedule i).length ⊕ Index tail)))

/-- Exact type of the challenge at a recursive event index. -/
def Challenge {d : ℕ} (C : Circuit F d) (i : Index C) : Type :=
  match C with
  | .input _ => F
  | .layer _ tail => match i with
    | .inl _ => F × F
    | .inr (.inl _) => F
    | .inr (.inr j) => Challenge tail j

instance challengeFintype [Fintype F] {d : ℕ} (C : Circuit F d) (i : Index C) :
    Fintype (Challenge C i) :=
  match C with
  | .input _ => inferInstanceAs (Fintype F)
  | .layer _ tail => match i with
    | .inl _ => inferInstanceAs (Fintype (F × F))
    | .inr (.inl _) => inferInstanceAs (Fintype F)
    | .inr (.inr j) => challengeFintype tail j

/-- Numerator of the proved field-sized error for this challenge. -/
def cost {d : ℕ} (C : Circuit F d) (i : Index C) : ℕ :=
  match C with
  | .input _ => 1
  | .layer (inDim := iDim) _ tail => match i with
    | .inl _ => 2
    | .inr (.inl j) => 2 + if ((schedule iDim).get j).1 then 0 else 1
    | .inr (.inr j) => cost tail j

/-- Round-by-round error at the concrete recursive challenge index. -/
noncomputable def error [Fintype F] {d : ℕ} (C : Circuit F d) (i : Index C) : NNReal :=
  (cost C i : NNReal) / Fintype.card F

/-- Hand-zero collapse of the fixed next-layer assertion table. -/
def AssertionStep (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (input : Fin (2^C.inputDim) → F) {Tail : Type}
    (c0 c1 : F) (tr : LayerTrace F d Tail) (j : Fin (schedule d).length) : Prop :=
  let v := (schedule d).get j
  ¬ v.1 = true ∧ AssertionTracking.Bad (cubeTable (assertionTable C input))
    (fun i => (layerRun nodes c0 c1 tr).1 (false,i)) v.2 (tr.rounds j).challenge

def RoundEvent (nodes : Sumcheck.Nodes F) {d : ℕ}
    (p : MvPolynomial (Vars d) F) (C : Circuit F d) (input : Fin (2^C.inputDim) → F)
    {Tail : Type} (c0 c1 : F) (tr : LayerTrace F d Tail) (j : Fin (schedule d).length) : Prop :=
  BadStep nodes p (fun _ => 0) (c0+tr.alpha*c1) (schedule d) tr.rounds j ∨
    AssertionStep nodes C input c0 c1 tr j

def Event (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (c0 c1 : F)
    (tr : Trace C) (i : Index C) : Prop :=
  match C with
  | .input _ => FinalEscape input g0 g1 c0 c1 tr
  | .layer Q tail =>
    let result := layerRun nodes c0 c1 tr
    match i with
    | .inl _ => BeginEscape Q (tail.eval input) g0 g1 c0 c1 tr.alpha tr.beta
    | .inr (.inl j) =>
      RoundEvent nodes (target Q (ClaimEvaluation.binaryLabelEquiv _) (cubeTable (tail.eval input))
        (weight g0 g1 tr.alpha) tr.beta) tail input c0 c1 tr j
    | .inr (.inr j) => Event nodes tail input
        (fun k => result.1 (false,k)) (fun k => result.1 (true,k))
        (tr.wc 0) (tr.wc 1) tr.tail j

/-- Replace only a round's fresh challenge, leaving both response values fixed. -/
def updateRound {d : ℕ} {Tail : Type} (tr : LayerTrace F d Tail)
    (j : Fin (schedule d).length) (x : F) : LayerTrace F d Tail :=
  { tr with rounds := Function.update tr.rounds j { tr.rounds j with challenge := x } }

/-- Replace exactly one verifier challenge in the recursive trace. -/
def update {d : ℕ} (C : Circuit F d) (tr : Trace C)
    (i : Index C) (x : Challenge C i) : Trace C :=
  match C with
  | .input _ => x
  | .layer _ tail => match i with
    | .inl _ => { tr with alpha := (show F × F from x).1, beta := (show F × F from x).2 }
    | .inr (.inl j) => updateRound tr j x
    | .inr (.inr j) => { tr with tail := update tail tr.tail j x }

omit [Field F] in
@[simp] theorem updateRound_challenge {d : ℕ} {Tail : Type} (tr : LayerTrace F d Tail)
    (j : Fin (schedule d).length) (x : F) : ((updateRound tr j x).rounds j).challenge = x := by
  simp [updateRound]

/-- Changing one challenge changes precisely its terminal environment coordinate. -/
theorem layerRun_update_env (nodes : Sumcheck.Nodes F) {d : ℕ} {Tail : Type}
    (c0 c1 : F) (tr : LayerTrace F d Tail) (j : Fin (schedule d).length) (x : F) :
    (layerRun nodes c0 c1 (updateRound tr j x)).1 =
      Function.update (layerRun nodes c0 c1 tr).1 ((schedule d).get j) x := by
  ext v
  obtain ⟨k,rfl⟩ := List.mem_iff_get.mp (mem_schedule d v)
  have hn := layer_run_env_at nodes (fun _ : Vars d => 0) (c0+tr.alpha*c1)
    (updateRound tr j x).rounds k
  have ho := layer_run_env_at nodes (fun _ : Vars d => 0) (c0+tr.alpha*c1) tr.rounds k
  by_cases hkj : k = j
  · subst k
    simpa only [layerRun, updateRound, Function.update_self] using hn
  · have hget : (schedule d).get k ≠ (schedule d).get j := by
      intro h
      exact hkj ((schedule_nodup d).get_inj_iff.mp h)
    simpa only [layerRun, updateRound, Function.update_of_ne hkj,
      Function.update_of_ne hget, ho] using hn

/-- The extra assertion event is absent on hand one and costs at most one
scalar root on hand zero. -/
theorem assertionStep_count [Fintype F] (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (input : Fin (2^C.inputDim) → F) {Tail : Type}
    (c0 c1 : F) (tr : LayerTrace F d Tail) (j : Fin (schedule d).length) :
    (Finset.univ.filter fun x : F => AssertionStep nodes C input c0 c1 (updateRound tr j x) j).card ≤
      if ((schedule d).get j).1 then 0 else 1 := by
  cases hv : ((schedule d).get j).1
  · have he (x : F) : AssertionStep nodes C input c0 c1 (updateRound tr j x) j ↔
        AssertionTracking.Bad (cubeTable (assertionTable C input))
          (fun i => (layerRun nodes c0 c1 tr).1 (false,i)) ((schedule d).get j).2 x := by
      have hp : (schedule d).get j = (false, ((schedule d).get j).2) := by
        exact Prod.ext hv rfl
      have he : (fun i => (layerRun nodes c0 c1 (updateRound tr j x)).1 (false,i)) =
          Function.update (fun i => (layerRun nodes c0 c1 tr).1 (false,i)) ((schedule d).get j).2 x := by
        rw [layerRun_update_env, hp]
        ext i
        simp only [Function.update_apply, Prod.mk.injEq, true_and]
      simp only [AssertionStep, hv, Bool.false_eq_true, not_false_eq_true, true_and,
        updateRound_challenge]
      rw [he, AssertionTracking.bad_update]
    simp only [Bool.false_eq_true, ↓reduceIte]
    simpa only [he] using AssertionTracking.bad_count (cubeTable (assertionTable C input))
      (fun i => (layerRun nodes c0 c1 tr).1 (false,i)) ((schedule d).get j).2
  · have he : (Finset.univ.filter fun x : F =>
        AssertionStep nodes C input c0 c1 (updateRound tr j x) j) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x _ hx
      exact hx.1 hv
    rw [he]
    simp

/-- Sumcheck healing and hand-zero assertion collapse are the only scalar
round events: at most three roots on hand zero and two on hand one. -/
theorem roundEvent_count [Fintype F] (nodes : Sumcheck.Nodes F) {d : ℕ}
    (p : MvPolynomial (Vars d) F) (hp : ∀ v, p.degreeOf v ≤ 2)
    (C : Circuit F d) (input : Fin (2^C.inputDim) → F) {Tail : Type}
    (c0 c1 : F) (tr : LayerTrace F d Tail) (j : Fin (schedule d).length) :
    (Finset.univ.filter fun x : F => RoundEvent nodes p C input c0 c1 (updateRound tr j x) j).card ≤
      2 + if ((schedule d).get j).1 then 0 else 1 := by
  have hs := badStep_count nodes p hp (fun _ => 0) (c0+tr.alpha*c1) (schedule d) tr.rounds j
  have ha := assertionStep_count nodes C input c0 c1 tr j
  have hu := Finset.card_union_le
    (Finset.univ.filter fun x : F => BadStep nodes p (fun _ => 0) (c0+tr.alpha*c1)
      (schedule d) (updateRound tr j x).rounds j)
    (Finset.univ.filter fun x : F => AssertionStep nodes C input c0 c1 (updateRound tr j x) j)
  have he : (Finset.univ.filter fun x : F => RoundEvent nodes p C input c0 c1 (updateRound tr j x) j) =
      (Finset.univ.filter fun x : F => BadStep nodes p (fun _ => 0) (c0+tr.alpha*c1)
        (schedule d) (updateRound tr j x).rounds j) ∪
      (Finset.univ.filter fun x : F => AssertionStep nodes C input c0 c1 (updateRound tr j x) j) := by
    ext x
    constructor
    · intro hx
      rcases (Finset.mem_filter.mp hx).2 with hs | ha
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
    · intro hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.mp hx with hs | ha
      · exact Or.inl (Finset.mem_filter.mp hs).2
      · exact Or.inr (Finset.mem_filter.mp ha).2
  rw [he]
  apply hu.trans
  exact Nat.add_le_add hs ha

/-- The final input challenge hides a false pair on at most one scalar. -/
theorem finalEscape_count [Fintype F] {d : ℕ} (w : Fin (2^d) → F)
    (g0 g1 : Fin d → F) (c0 c1 : F) :
    (Finset.univ.filter fun x : F => FinalEscape w g0 g1 c0 c1 x).card ≤ 1 := by
  by_cases hbad : c0 ≠ ClaimEvaluation.evalTable w g0 ∨ c1 ≠ ClaimEvaluation.evalTable w g1
  · have h := ClaimEvaluation.scalar_batch_count
      (c0-ClaimEvaluation.evalTable w g0) (c1-ClaimEvaluation.evalTable w g1)
      (by simpa only [sub_ne_zero] using hbad)
    apply (Finset.card_le_card ?_).trans h
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hh := (Finset.mem_filter.mp hx).2.2
    linear_combination hh
  · simp [FinalEscape, hbad]

/-- Shared alpha/beta batching has the actual two-field-element challenge
space and costs at most `2/|F|`. -/
theorem beginEscape_count [Fintype F] {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T) (w : Fin (2^inDim) → F)
    (g0 g1 : Fin outDim → F) (c0 c1 : F) :
    ((Finset.univ.filter fun r : F × F => BeginEscape Q w g0 g1 c0 c1 r.1 r.2).card : NNReal) ≤
      (2 / Fintype.card F : NNReal) * Fintype.card (F × F) := by
  have he := (finTwoArrowEquiv F).sum_comp
    (fun r : F × F => if BeginEscape Q w g0 g1 c0 c1 r.1 r.2 then (1 : ℕ) else 0)
  have hcard : (Finset.univ.filter fun r : Fin 2 → F => BeginEscape Q w g0 g1 c0 c1 (r 0) (r 1)).card =
      (Finset.univ.filter fun r : F × F => BeginEscape Q w g0 g1 c0 c1 r.1 r.2).card := by
    change (∑ r : Fin 2 → F, if BeginEscape Q w g0 g1 c0 c1 (r 0) (r 1) then (1:ℕ) else 0) =
      ∑ r : F × F, if BeginEscape Q w g0 g1 c0 c1 r.1 r.2 then (1:ℕ) else 0 at he
    simpa only [Finset.sum_boole, Nat.cast_id] using he
  rw [← hcard]
  by_cases hbad : c0 ≠ ClaimEvaluation.evalTable (Circuit.output Q w) g0 ∨
    c1 ≠ ClaimEvaluation.evalTable (Circuit.output Q w) g1 ∨
    Layer.asserted Q w (fun g => PackedClaim.eqPt g0 g.val) ≠ 0 ∨
    Layer.asserted Q w (fun g => PackedClaim.eqPt g1 g.val) ≠ 0
  · have h := Layer.bound_claim_count Q w
      (fun g => PackedClaim.eqPt g0 g.val) (fun g => PackedClaim.eqPt g1 g.val) c0 c1
      (by simpa only [ordinary_eq_evalTable] using hbad)
    have heq : (Finset.univ.filter fun r : Fin 2 → F =>
        BeginEscape Q w g0 g1 c0 c1 (r 0) (r 1)) =
        Finset.univ.filter (fun r : Fin 2 → F => c0 + r 0*c1 =
          Layer.bind Q w (fun g => PackedClaim.eqPt g0 g.val + r 0*PackedClaim.eqPt g1 g.val) (r 1)) := by
      ext r
      constructor
      · intro hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.2⟩
      · intro hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad, (Finset.mem_filter.mp hr).2⟩
    rw [heq]
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, pow_two] using h
  · simp [BeginEscape, hbad]

/-- Every recursive event has the claimed conditional finite-count bound
when only its own challenge is replaced. All prover values remain arbitrary. -/
theorem event_count [Fintype F] (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (c0 c1 : F) (tr : Trace C)
    (i : Index C) :
    ((Finset.univ.filter fun x : Challenge C i =>
      Event nodes C input g0 g1 c0 c1 (update C tr i x) i).card : NNReal) ≤
      ((cost C i : ℕ) / (Fintype.card F : NNReal)) * Fintype.card (Challenge C i) := by
  have hcard : (Fintype.card F : NNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  induction C generalizing c0 c1 with
  | input d =>
    have h : ((Finset.univ.filter fun x : F =>
        FinalEscape (show Fin (2^d) → F from input) g0 g1 c0 c1 x).card : NNReal) ≤ 1 := by
      exact_mod_cast finalEscape_count (show Fin (2^d) → F from input) g0 g1 c0 c1
    calc
      _ ≤ (1 : NNReal) := h
      _ = _ := by simp only [cost, Nat.cast_one]; exact (div_mul_cancel₀ 1 hcard).symm
  | @layer outDim inDim T Q tail ih =>
    rcases i with i | (j | j)
    · exact beginEscape_count Q (tail.eval input) g0 g1 c0 c1
    · change ((Finset.univ.filter fun x : F =>
        RoundEvent nodes (target Q (ClaimEvaluation.binaryLabelEquiv inDim) (cubeTable (tail.eval input))
          (weight g0 g1 tr.alpha) tr.beta) tail input c0 c1 (updateRound tr j x) j).card : NNReal) ≤
        (((2 + if ((schedule inDim).get j).1 then 0 else 1 : ℕ) : NNReal) / Fintype.card F) * Fintype.card F
      rw [div_mul_cancel₀ _ hcard]
      exact_mod_cast roundEvent_count nodes _
        (target_degree Q (ClaimEvaluation.binaryLabelEquiv inDim) (cubeTable (tail.eval input))
          (weight g0 g1 tr.alpha) tr.beta) tail input c0 c1 tr j
    · exact ih input (fun k => (layerRun nodes c0 c1 tr).1 (false,k))
        (fun k => (layerRun nodes c0 c1 tr).1 (true,k)) (tr.wc 0) (tr.wc 1) tr.tail j

/-- Tracker events in the source schedule cover every hand-zero coordinate. -/
theorem tracking_of_no_assertionSteps (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (input : Fin (2^C.inputDim) → F) {Tail : Type}
    (c0 c1 : F) (tr : LayerTrace F d Tail)
    (h : ∀ j, ¬ AssertionStep nodes C input c0 c1 tr j) :
    ∀ i, ¬ AssertionTracking.Bad (cubeTable (assertionTable C input))
      (fun k => (layerRun nodes c0 c1 tr).1 (false,k)) i
      ((layerRun nodes c0 c1 tr).1 (false,i)) := by
  intro i hi
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp (mem_schedule d (false,i))
  have hr := layer_run_env_at nodes (fun _ : Vars d => 0) (c0+tr.alpha*c1) tr.rounds j
  rw [hj] at hr
  apply h j
  constructor
  · simp only [hj, Bool.false_eq_true, not_false_eq_true]
  · simpa only [hj, ← hr, layerRun] using hi

/-- Prefix tracking rules out the next layer's aggregate assertion escape. -/
theorem headEscape_of_tracking {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g : Fin d → F)
    (h : ∀ i, ¬ AssertionTracking.Bad (cubeTable (assertionTable C input)) g i (g i)) :
    ¬ HeadEscape C input g := by
  cases C with
  | input _ => exact not_false
  | layer Q tail =>
    intro he
    rcases he with ⟨hbad,hzero⟩
    have hz : ∀ i, Layer.assertions Q (tail.eval input) i = 0 :=
      AssertionTracking.indexed_zero_of_no_bad _ g h
        (by simpa only [asserted_eq_evalTable] using hzero)
    exact hbad hz

/-- No recursively indexed challenge event implies all of the deterministic
no-escape conditions, using actual assertion tracking between adjacent layers. -/
theorem noEscape_of_noEvents (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (c0 c1 : F) (tr : Trace C)
    (hhead : ¬ HeadEscape C input g0)
    (h : ∀ i, ¬ Event nodes C input g0 g1 c0 c1 tr i) :
    NoEscape nodes C input g0 g1 c0 c1 tr := by
  induction C generalizing c0 c1 with
  | input _ => exact h ()
  | layer Q tail ih =>
    refine ⟨h (.inl ()), ?_, hhead, ?_⟩
    · intro j hj
      exact h (.inr (.inl j)) (Or.inl hj)
    · apply ih input _ _ _ _ tr.tail
      · apply headEscape_of_tracking
        apply tracking_of_no_assertionSteps nodes tail input c0 c1 tr
        intro j hj
        exact h (.inr (.inl j)) (Or.inr hj)
      · intro j hj
        exact h (.inr (.inr j)) hj

/-- Any accepting transcript for a false source circuit relation has an
explicit initial event or an event at an actual recursive challenge. -/
theorem accepted_false_has_event (nodes : Sumcheck.Nodes F) {d : ℕ} (C : Circuit F d)
    (input : Fin (2^C.inputDim) → F) (g0 g1 : Fin d → F) (tr : Trace C)
    (hc : check nodes C input g0 g1 0 0 tr) (hfalse : ¬ C.Satisfied input) :
    InitialEvent C input g0 ∨ ∃ i, Event nodes C input g0 g1 0 0 tr i := by
  by_contra h
  have hi : ¬ InitialEvent C input g0 := fun hi => h (Or.inl hi)
  have he : ∀ i, ¬ Event nodes C input g0 g1 0 0 tr i := fun i he => h (Or.inr ⟨i,he⟩)
  apply hfalse
  exact satisfied nodes C input g0 g1 tr hc
    (noEscape_of_noEvents nodes C input g0 g1 0 0 tr (fun hh => hi (Or.inr hh)) he)
    (fun ho => hi (Or.inl ho))

theorem layerRun_hand_zero (nodes : Sumcheck.Nodes F) {d : ℕ} {Tail : Type}
    (c0 c1 : F) (tr : LayerTrace F d Tail) (i : Fin d) :
    (layerRun nodes c0 c1 tr).1 (false,i) =
      (tr.rounds (AssertionTracking.zeroRound i)).challenge := by
  simpa only [AssertionTracking.schedule_get_zeroRound, layerRun] using
    layer_run_env_at nodes (fun _ : Vars d => 0) (c0+tr.alpha*c1) tr.rounds
      (AssertionTracking.zeroRound i)

theorem assertionStep_congr (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (input : Fin (2^C.inputDim) → F) {Tail : Type}
    (c0 c1 : F) (tr tr' : LayerTrace F d Tail) (j : Fin (schedule d).length)
    (h : ∀ k, k.val ≤ j.val → tr.rounds k = tr'.rounds k) :
    AssertionStep nodes C input c0 c1 tr j ↔ AssertionStep nodes C input c0 c1 tr' j := by
  unfold AssertionStep
  by_cases hb : ((schedule d).get j).1 = true
  · simp only [hb, not_true_eq_false, false_and]
  · have hv : (schedule d).get j = (false, ((schedule d).get j).2) := by
      ext <;> simp_all
    have hj : j = AssertionTracking.zeroRound ((schedule d).get j).2 := by
      apply (schedule_nodup d).injective_get
      rw [AssertionTracking.schedule_get_zeroRound]
      exact hv
    have hp : ∀ k, k.val < ((schedule d).get j).2.val →
        (layerRun nodes c0 c1 tr).1 (false,k) = (layerRun nodes c0 c1 tr').1 (false,k) := by
      intro k hk
      rw [layerRun_hand_zero, layerRun_hand_zero, h]
      rw [hj]
      exact le_of_lt (AssertionTracking.zeroRound_strictMono hk)
    rw [h j le_rfl]
    exact and_congr_right (fun _ => AssertionTracking.bad_prefix _ _ _ _ hp _)

theorem roundEvent_congr (nodes : Sumcheck.Nodes F) {d : ℕ}
    (p : MvPolynomial (Vars d) F) (C : Circuit F d) (input : Fin (2^C.inputDim) → F)
    {Tail : Type} (c0 c1 : F) (tr tr' : LayerTrace F d Tail) (j : Fin (schedule d).length)
    (ha : tr.alpha = tr'.alpha)
    (h : ∀ k, k.val ≤ j.val → tr.rounds k = tr'.rounds k) :
    RoundEvent nodes p C input c0 c1 tr j ↔ RoundEvent nodes p C input c0 c1 tr' j := by
  unfold RoundEvent
  apply or_congr
  · unfold BadStep
    rw [ha, position_congr nodes _ _ _ tr.rounds tr'.rounds j (fun k hk => h k (le_of_lt hk)), h j le_rfl]
  · exact assertionStep_congr nodes C input c0 c1 tr tr' j h
theorem unmask_update {d : ℕ} (C : Circuit F d) (pads : PadTranslation.Pads C)
    (tr : Trace C) (i : Index C) (x : Challenge C i) :
    PadTranslation.unmask C pads (update C tr i x) =
      update C (PadTranslation.unmask C pads tr) i x := by
  induction C with
  | input _ => rfl
  | @layer outDim inDim T Q tail ih =>
    rcases i with i | (j | j)
    · rfl
    · simp only [PadTranslation.unmask, update, updateRound]
      congr 1
      funext k
      by_cases hk : k = j
      · subst k
        simp only [Function.update_self, PadTranslation.unmaskMessage]
      · simp only [Function.update_of_ne hk]
    · simp only [PadTranslation.unmask, update]
      congr 1
      exact ih pads.tail tr.tail j x

end GordieHowe.GKR.CircuitEvents
