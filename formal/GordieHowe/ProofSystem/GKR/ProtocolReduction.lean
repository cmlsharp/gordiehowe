-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.ProtocolEvents
public import GordieHowe.ProofSystem.GKR.ProtocolCounting
public import GordieHowe.ProofSystem.GKR.InitialChallenge

@[expose] public section

/-!
# Round-by-round reduction for the concrete GKR protocol

The error function follows the actual typed schedule. Initial evaluation,
shared batching, degree-two sumcheck, assertion tracking, and final scalar
batching have proved finite counting bounds.
-/
namespace GordieHowe.GKR.ProtocolReduction
open IOP
open Schedule ProtocolEvents GKR.Circuit CircuitProtocol CircuitEvents
open scoped Classical NNReal
variable (F : Type) [Field F] [Fintype F]

noncomputable def error {d : ℕ} (C : Circuit F d) : (spec F C).ChallengeIdx → NNReal :=
  Sum.elim (fun _ => (2*d : NNReal) / Fintype.card F) (CircuitEvents.error C) ∘ index F C

omit [Fintype F] in
/-- The grouped source assertion table supplies the initial MLE residual. -/
theorem initialEvent_iff {d : ℕ} (C : Circuit F d) (input : Fin (2^C.inputDim) → F)
    (c : InitialChallenge.Challenge F d) :
    InitialEvent C input c ↔
      InitialChallenge.Bad (C.eval input) (assertionTable C input) c := by
  unfold InitialEvent InitialChallenge.Bad InitialChallenge.BadTable OutputEscape
  apply or_congr Iff.rfl
  cases C with
  | input => simp [HeadEscape,assertionTable]
  | layer Q tail =>
    change (¬ (∀ g, Layer.assertions Q (tail.eval input) g = 0) ∧ _) ↔ _
    simp only [not_forall, asserted_eq_evalTable]
    rfl

theorem initialEvent_count {d : ℕ} (C : Circuit F d) (input : Fin (2^C.inputDim) → F) :
    ((Finset.univ.filter fun c : InitialChallenge.Challenge F d =>
      InitialEvent C input c).card : NNReal) ≤
      (2*d / Fintype.card F : NNReal) * Fintype.card (InitialChallenge.Challenge F d) := by
  simp only [initialEvent_iff]
  exact InitialChallenge.bad_count (C.eval input) (assertionTable C input)

omit [Fintype F] in
/-- The first verifier move has the initial point's challenge type `F^d`. -/
theorem initialChallengeType {d : ℕ} (C : Circuit F d) :
    (spec F C).Challenge ((index F C).symm (.inl ())) = InitialChallenge.Challenge F d := by
  change (one .V_to_P (InitialChallenge.Challenge F d) ++ (_ : ProtocolSpec _)).Challenge
    (ProtocolSpec.ChallengeIdx.inl
    ((verifierIndex (InitialChallenge.Challenge F d)).symm ())) = _
  rw [ProtocolSpec.append_Challenge_inl]
  rfl

omit [Fintype F] in
theorem initialValues_update {d : ℕ} (C : Circuit F d)
    (tr : (spec F C).Transcript (Fin.last (1+circuitLength F C)))
    (x : (spec F C).Challenge ((index F C).symm (.inl ()))) :
    initialValues F C (Function.update tr ((index F C).symm (.inl ())).1 x) =
      cast (initialChallengeType F C) x := by
  unfold initialValues
  change oneValue (ProtocolSpec.Transcript.left (P₁ := initial F d) (P₂ := circuit F C)
    (Function.update tr ((⟨0,by decide⟩ : Fin 1).castAdd (circuitLength F C)) x)) = _
  erw [left_update_left]
  unfold oneValue
  erw [Function.update_self]
  rfl

omit [Fintype F] in
theorem initialValues_agree {d : ℕ} (C : Circuit F d)
    (tr tr' : (spec F C).Transcript (Fin.last (1+circuitLength F C)))
    (k : ℕ) (h : ∀ j, j.val ≤ k → tr j = tr' j) : initialValues F C tr = initialValues F C tr' := by
  unfold initialValues oneValue
  exact left_agrees tr tr' k h ⟨0,by decide⟩ (Nat.zero_le k)

omit [Fintype F] in
/-- No event depends on messages after its actual verifier challenge. -/
theorem fullBad_causal (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) :
    TranscriptEventReduction.Causal (spec F C) (fullBad F nodes C) := by
  intro i ctx tr tr' h
  have hv := initialValues_agree F C tr tr' i.1.val h
  have hg : initialPoint F C tr = initialPoint F C tr' := by
    unfold initialPoint
    rw [hv]
  obtain ⟨j,rfl⟩ := (index F C).symm.surjective i
  cases j with
  | inl u =>
    simp only [fullBad, Equiv.apply_symm_apply]
    rw [hg]
  | inr j =>
    simp only [fullBad, Equiv.apply_symm_apply]
    rw [← hg]
    exact circuitEvent_causal F nodes C ctx.1 _ _ 0 0 ctx.2 j
      tr.right tr'.right (right_agrees tr tr' _ h)

theorem count_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → Prop) :
    (Finset.univ.filter fun a => p (e a)).card = (Finset.univ.filter p).card := by
  apply Finset.card_bij (fun a _ => e a)
  · intro a ha; simpa using ha
  · intro a _ b _ h; exact e.injective h
  · intro b hb
    exact ⟨e.symm b, by simpa using hb, by simp⟩

/-- The initial point retains its exact finite distribution in the typed schedule. -/
theorem initial_count (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (ctx : Context F C)
    (tr : (spec F C).Transcript (Fin.last (1+circuitLength F C))) :
    ((Finset.univ.filter fun x : (spec F C).Challenge ((index F C).symm (.inl ())) =>
      fullBad F nodes C ((index F C).symm (.inl ())) ctx
        (Function.update tr ((index F C).symm (.inl ())).1 x)).card : NNReal) ≤
      error F C ((index F C).symm (.inl ())) *
        Fintype.card ((spec F C).Challenge ((index F C).symm (.inl ()))) := by
  let e := Equiv.cast (initialChallengeType F C)
  have he (x : (spec F C).Challenge ((index F C).symm (.inl ()))) :
      fullBad F nodes C ((index F C).symm (.inl ())) ctx
        (Function.update tr ((index F C).symm (.inl ())).1 x) ↔
      InitialEvent C ctx.1 (e x) := by
    simp only [fullBad, Equiv.apply_symm_apply]
    unfold initialPoint
    rw [initialValues_update]
    rfl
  simp only [he]
  have hc := count_equiv e (fun c => InitialEvent C ctx.1 c)
  erw [hc, Fintype.card_congr e]
  exact initialEvent_count F C ctx.1

omit [Fintype F] in
/-- Circuit-phase challenge types are unchanged by the initial point. -/
theorem circuitPhaseChallengeType {d : ℕ} (C : Circuit F d) (i : Index C) :
    (spec F C).Challenge ((index F C).symm (.inr i)) =
      (circuit F C).Challenge ((circuitIndex F C).symm i) := by
  change (initial F d ++ circuit F C).Challenge
    (ProtocolSpec.ChallengeIdx.inr ((circuitIndex F C).symm i)) = _
  exact ProtocolSpec.append_Challenge_inr _

omit [Fintype F] in
theorem circuitPhase_initialValues {d : ℕ} (C : Circuit F d)
    (tr : (spec F C).Transcript (Fin.last (1+circuitLength F C))) (i : Index C)
    (x : (spec F C).Challenge ((index F C).symm (.inr i))) :
    initialValues F C (Function.update tr ((index F C).symm (.inr i)).1 x) =
      initialValues F C tr := by
  exact congrArg oneValue (left_update_right tr ((circuitIndex F C).symm i).1 x)

omit [Fintype F] in
theorem circuitPhase_trace {d : ℕ} (C : Circuit F d)
    (tr : (spec F C).Transcript (Fin.last (1+circuitLength F C))) (i : Index C)
    (x : (spec F C).Challenge ((index F C).symm (.inr i))) :
    trace F C (Function.update tr ((index F C).symm (.inr i)).1 x) =
      circuitTrace F C (Function.update tr.right ((circuitIndex F C).symm i).1
        (cast (circuitPhaseChallengeType F C i) x)) := by
  exact congrArg (circuitTrace F C) (right_update_right tr ((circuitIndex F C).symm i).1 x)

/-- Circuit-phase replacement counts are transported through the initial round. -/
theorem circuit_count (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (ctx : Context F C)
    (tr : (spec F C).Transcript (Fin.last (1+circuitLength F C))) (i : Index C) :
    ((Finset.univ.filter fun x : (spec F C).Challenge ((index F C).symm (.inr i)) =>
      fullBad F nodes C ((index F C).symm (.inr i)) ctx
        (Function.update tr ((index F C).symm (.inr i)).1 x)).card : NNReal) ≤
      error F C ((index F C).symm (.inr i)) *
        Fintype.card ((spec F C).Challenge ((index F C).symm (.inr i))) := by
  let e := Equiv.cast (circuitPhaseChallengeType F C i)
  let g := initialPoint F C tr
  let bad := fun x : (circuit F C).Challenge ((circuitIndex F C).symm i) =>
    Event nodes C ctx.1 g g 0 0 (PadTranslation.unmask C ctx.2
      (circuitTrace F C (Function.update tr.right ((circuitIndex F C).symm i).1 x))) i
  have he (x : (spec F C).Challenge ((index F C).symm (.inr i))) :
      fullBad F nodes C ((index F C).symm (.inr i)) ctx
        (Function.update tr ((index F C).symm (.inr i)).1 x) ↔ bad (e x) := by
    simp only [fullBad, Equiv.apply_symm_apply]
    rw [circuitPhase_trace]
    unfold initialPoint
    rw [circuitPhase_initialValues]
    rfl
  simp only [he]
  have hc := count_equiv e bad
  erw [hc, Fintype.card_congr e]
  simpa only [error, Function.comp_apply, Equiv.apply_symm_apply, Sum.elim_inr] using
    ProtocolCounting.circuitEvent_count F nodes C ctx.1 ctx.2 g g 0 0 tr.right i

/-- Per-prefix replacement bounds for every verifier message of the actual protocol. -/
theorem fullBad_count (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) (ctx : Context F C) (i : (spec F C).ChallengeIdx)
    (tr : (spec F C).Transcript (Fin.last (1+circuitLength F C))) :
    ((Finset.univ.filter fun x : (spec F C).Challenge i =>
      fullBad F nodes C i ctx (Function.update tr i.1 x)).card : NNReal) ≤
      error F C i * Fintype.card ((spec F C).Challenge i) := by
  obtain ⟨j,rfl⟩ := (index F C).symm.surjective i
  cases j with
  | inl u => cases u; exact initial_count F nodes C ctx tr
  | inr j => exact circuit_count F nodes C ctx tr j

/-- Source-derived GKR RBR reduction, with no statistical security premise. -/
noncomputable def reduction (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : Circuit F d) :
    ClaimReduction (spec F C) (Context F C) (error F C) :=
  TranscriptEventReduction.reduction (spec F C) (fullBad F nodes C)
    (fullBad_causal F nodes C) (fun ctx => C.Satisfied ctx.1)
    (terminal F nodes C) (error F C) (fullBad_count F nodes C)
    (by
      intro ctx tr ht
      by_cases hc : C.Satisfied ctx.1
      · exact Or.inl hc
      · exact Or.inr (terminal_false_has_event F nodes C ctx tr ht hc))

/-- Every round of the concrete GKR protocol is at most `δ` when its initial round
`2d/|F|` and every circuit round are. -/
theorem error_le_of {d : ℕ} (C : Circuit F d)
    {δ : ℝ≥0} (hinit : (2 * d : ℝ≥0) / Fintype.card F ≤ δ)
    (hround : ∀ i, CircuitEvents.error C i ≤ δ) (i) : error F C i ≤ δ :=
  Sum.elim_comp_le_of _ _ _ (fun _ => hinit) hround i

end GordieHowe.GKR.ProtocolReduction
