-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.ProofSystem.GKR.CircuitEvents
public import GordieHowe.ProofSystem.GKR.PadTranslation
public import GordieHowe.Model.IOP.TranscriptEventReduction

@[expose] public section

/-! Concrete challenge coordinates for the typed Longfellow schedule. -/
namespace GordieHowe.GKR.ProtocolEvents
open IOP
open Schedule CircuitEvents
variable (F : Type) [Field F]

/-- Exactly one recursive event coordinate per circuit-phase verifier move. -/
def circuitIndex {d : ℕ} : (C : GKR.Circuit F d) →
    (circuit F C).ChallengeIdx ≃ Index C
  | .input _ => verifierIndex F
  | .layer (inDim := b) _ tail =>
    ProtocolSpec.challengeIdxEquiv.trans
      (Equiv.sumCongr (verifierIndex (F×F))
        (ProtocolSpec.challengeIdxEquiv.trans
          (Equiv.sumCongr
            ((roundIndex F (2*b)).trans (finCongr (LayerSumcheck.schedule_length b).symm))
            ((skipProver (F×F) _).trans (circuitIndex tail)))))

/-- The index bijection also preserves each challenge's exact message type. -/
theorem circuitChallengeType {d : ℕ} (C : GKR.Circuit F d) (i : Index C) :
    (circuit F C).Challenge ((circuitIndex F C).symm i) = Challenge C i := by
  induction C with
  | input d => rfl
  | @layer outDim inDim T Q tail ih =>
    rcases i with u | (j | j)
    · change (one .V_to_P (F×F) ++ (_ : ProtocolSpec _)).Challenge
        (ProtocolSpec.ChallengeIdx.inl ((verifierIndex (F×F)).symm u)) = (F×F)
      rw [ProtocolSpec.append_Challenge_inl]
      rfl
    · change (one .V_to_P (F×F) ++ (_ : ProtocolSpec _)).Challenge
        (ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inl
          ((roundIndex F (2*inDim)).symm
            ((finCongr (LayerSumcheck.schedule_length inDim).symm).symm j)))) = F
      rw [ProtocolSpec.append_Challenge_inr, ProtocolSpec.append_Challenge_inl,
        roundIndex_symm, roundChallenge_type]
    · change (one .V_to_P (F×F) ++ (_ : ProtocolSpec _)).Challenge
        (ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inr
          (ProtocolSpec.ChallengeIdx.inr ((circuitIndex F tail).symm j)))) = Challenge tail j
      rw [ProtocolSpec.append_Challenge_inr, ProtocolSpec.append_Challenge_inr,
        ProtocolSpec.append_Challenge_inr]
      exact ih j

def index {d : ℕ} (C : GKR.Circuit F d) :
    (spec F C).ChallengeIdx ≃ Unit ⊕ Index C :=
  ProtocolSpec.challengeIdxEquiv.trans
    (Equiv.sumCongr (verifierIndex (Fin d → F)) (circuitIndex F C))

/-- Context fixed before any verifier randomness: the input and arbitrary pads. -/
def Context {d : ℕ} (C : GKR.Circuit F d) :=
  (Fin (2^C.inputDim) → F) × PadTranslation.Pads C

/-- The initial point: the first verifier move. -/
def initialPoint {d : ℕ} (C : GKR.Circuit F d)
    (tr : (spec F C).Transcript (Fin.last (1+circuitLength F C))) : Fin d → F :=
  initialValues F C tr

def fullBad (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : GKR.Circuit F d) (i : (spec F C).ChallengeIdx)
    (ctx : Context F C)
    (tr : (spec F C).Transcript (Fin.last (1+circuitLength F C))) : Prop :=
  let g := initialPoint F C tr
  match index F C i with
  | .inl _ => InitialEvent C ctx.1 g
  | .inr j => Event nodes C ctx.1 g g 0 0
      (PadTranslation.unmask C ctx.2 (trace F C tr)) j

def terminal (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : GKR.Circuit F d) (ctx : Context F C)
    (tr : (spec F C).Transcript (Fin.last (1+circuitLength F C))) : Prop :=
  PadTranslation.ProductsHold C ctx.2 ∧
    CircuitProtocol.check nodes C ctx.1 (initialPoint F C tr)
      (initialPoint F C tr) 0 0 (PadTranslation.unmask C ctx.2 (trace F C tr))

/-- Deterministic soundness is transported to the actual typed transcript. -/
theorem terminal_false_has_event (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : GKR.Circuit F d) (ctx : Context F C)
    (tr : (spec F C).Transcript (Fin.last (1+circuitLength F C)))
    (ht : terminal F nodes C ctx tr) (hf : ¬ C.Satisfied ctx.1) :
    ∃ i, fullBad F nodes C i ctx tr := by
  obtain hi | ⟨j,hj⟩ := accepted_false_has_event nodes C ctx.1
    (initialPoint F C tr) (initialPoint F C tr)
    (PadTranslation.unmask C ctx.2 (trace F C tr)) ht.2 hf
  · refine ⟨(index F C).symm (.inl ()), ?_⟩
    simpa only [fullBad, Equiv.apply_symm_apply] using hi
  · refine ⟨(index F C).symm (.inr j), ?_⟩
    simpa only [fullBad, Equiv.apply_symm_apply] using hj

/-- A complete first phase is fixed by agreement through its final position. -/
theorem fst_eq_of_agrees {a b : ℕ} {A : ProtocolSpec a} {B : ProtocolSpec b}
    (tr tr' : (A ++ B).Transcript (Fin.last (a+b))) (k : ℕ)
    (h : ∀ j, j.val ≤ k → tr j = tr' j) (hlen : a ≤ k+1) :
    tr.left = tr'.left := by
  funext j
  apply left_agrees tr tr' k h j
  have hj : j.val < a := j.isLt
  omega

theorem circuitIndex_round_val {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (tail : GKR.Circuit F inDim) (j : Fin (LayerSumcheck.schedule inDim).length) :
    ((circuitIndex F (.layer Q tail)).symm (.inr (.inl j))).1.val = 1+(2*j.val+1) := by
  change 1+((roundIndex F (2*inDim)).symm
    ((finCongr (LayerSumcheck.schedule_length inDim).symm).symm j)).1.val = _
  rw [roundIndex_symm, roundChallenge_val]
  rfl

/-- Every recursive event uses only raw messages through its actual challenge. -/
theorem circuitEvent_causal (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : GKR.Circuit F d) (input : Fin (2^C.inputDim) → F)
    (g0 g1 : Fin d → F) (c0 c1 : F) (pads : PadTranslation.Pads C) (i : Index C)
    (tr tr' : (circuit F C).Transcript (Fin.last (circuitLength F C)))
    (h : ∀ j, j.val ≤ ((circuitIndex F C).symm i).1.val → tr j = tr' j) :
    Event nodes C input g0 g1 c0 c1 (PadTranslation.unmask C pads (circuitTrace F C tr)) i ↔
      Event nodes C input g0 g1 c0 c1 (PadTranslation.unmask C pads (circuitTrace F C tr')) i := by
  induction C generalizing c0 c1 with
  | input d =>
    have he : tr = tr' := by
      funext j
      apply h j
      change j.val ≤ 0
      have hj : j.val < 1 := j.isLt
      omega
    rw [he]
  | @layer outDim inDim T Q tail ih =>
    rcases i with u | (j | j)
    · have he := fst_eq_of_agrees tr tr' 0 h (by omega)
      change CircuitProtocol.BeginEscape Q (tail.eval input) g0 g1 c0 c1
        (oneValue tr.left).1 (oneValue tr.left).2 ↔
        CircuitProtocol.BeginEscape Q (tail.eval input) g0 g1 c0 c1
        (oneValue tr'.left).1 (oneValue tr'.left).2
      rw [he]
    · rw [circuitIndex_round_val] at h
      have hab := fst_eq_of_agrees tr tr' (1+(2*j.val+1)) h (by omega)
      have hr : ∀ k : Fin (LayerSumcheck.schedule inDim).length, k.val ≤ j.val →
          (PadTranslation.unmask (.layer Q tail) pads (circuitTrace F (.layer Q tail) tr)).rounds k =
          (PadTranslation.unmask (.layer Q tail) pads (circuitTrace F (.layer Q tail) tr')).rounds k := by
        intro k hk
        apply congrArg (PadTranslation.unmaskMessage (pads.polynomial k))
        apply roundMessages_congr_at
        intro l hl
        apply left_agrees tr.right tr'.right (2*j.val+1)
          (right_agrees tr tr' (2*j.val+1) h) l
        change l.val ≤ 2*k.val+1 at hl
        omega
      have ha : (oneValue tr.left).1 = (oneValue tr'.left).1 := congrArg (fun t => (oneValue t).1) hab
      have hb : (oneValue tr.left).2 = (oneValue tr'.left).2 := congrArg (fun t => (oneValue t).2) hab
      change RoundEvent nodes _ tail input c0 c1 _ j ↔ RoundEvent nodes _ tail input c0 c1 _ j
      simp only [circuitTrace, PadTranslation.unmask] at *
      rw [ha, hb]
      apply roundEvent_congr
      · rfl
      · exact hr
    · have hcut : ∀ k, k.val ≤ 1+(roundLength (2*inDim)+(1+((circuitIndex F tail).symm j).1.val)) →
          tr k = tr' k := h
      have hab := fst_eq_of_agrees tr tr' _ hcut (by omega)
      have hrest := right_agrees tr tr' _ hcut
      have hround := fst_eq_of_agrees tr.right tr'.right _ hrest (by omega)
      have hclaims := right_agrees tr.right tr'.right _ hrest
      have hwc := fst_eq_of_agrees tr.right.right tr'.right.right _ hclaims (by omega)
      have htail := right_agrees tr.right.right tr'.right.right _ hclaims
      let decoded := PadTranslation.unmask (.layer Q tail) pads
        (circuitTrace F (.layer Q tail) tr')
      have ht := ih input
        (fun k => (CircuitProtocol.layerRun nodes c0 c1 decoded).1 (false,k))
        (fun k => (CircuitProtocol.layerRun nodes c0 c1 decoded).1 (true,k))
        (decoded.wc 0) (decoded.wc 1) pads.tail j
        tr.right.right.right tr'.right.right.right htail
      simpa only [decoded, Event, circuitTrace, PadTranslation.unmask, CircuitProtocol.layerRun, hab, hround, hwc] using ht

end GordieHowe.GKR.ProtocolEvents
