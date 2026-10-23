-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.ProtocolEvents
public import GordieHowe.ProofSystem.GKR.RoundUpdate

@[expose] public section

namespace GordieHowe.GKR.ProtocolCounting
open IOP
open Schedule ProtocolEvents CircuitEvents CircuitProtocol
open scoped Classical NNReal
variable (F : Type) [Field F]

theorem update_cast {ι : Type} [DecidableEq ι] {B : ι → Type} {A : Type}
    (f : (i : ι) → B i) {i j : ι} (h : i = j) (ei : A = B i) (ej : A = B j) (x : A) :
    Function.update f i (cast ei x) = Function.update f j (cast ej x) := by
  subst j
  rfl

def circuitUpdate {d : ℕ} (C : GKR.Circuit F d)
    (tr : (circuit F C).Transcript (Fin.last (circuitLength F C)))
    (i : Index C) (x : Challenge C i) :
    (circuit F C).Transcript (Fin.last (circuitLength F C)) :=
  Function.update tr ((circuitIndex F C).symm i).1 (cast (circuitChallengeType F C i).symm x)

theorem circuitUpdate_begin_rest {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (C : GKR.Circuit F inDim)
    (tr : (circuit F (.layer Q C)).Transcript (Fin.last (circuitLength F (.layer Q C))))
    (x : F×F) : (circuitUpdate F (.layer Q C) tr (.inl ()) x).right = tr.right := by
  exact right_update_left tr _ _

theorem circuitUpdate_begin_head {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (C : GKR.Circuit F inDim)
    (tr : (circuit F (.layer Q C)).Transcript (Fin.last (circuitLength F (.layer Q C))))
    (x : F×F) : oneValue (circuitUpdate F (.layer Q C) tr (.inl ()) x).left = x := by
  rfl
theorem circuitUpdate_tail_head {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (C : GKR.Circuit F inDim)
    (tr : (circuit F (.layer Q C)).Transcript (Fin.last (circuitLength F (.layer Q C))))
    (i : Index C) (x : Challenge C i) :
    (circuitUpdate F (.layer Q C) tr (.inr (.inr i)) x).left = tr.left := by
  exact left_update_right tr _ _

theorem circuitUpdate_tail_rounds {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (C : GKR.Circuit F inDim)
    (tr : (circuit F (.layer Q C)).Transcript (Fin.last (circuitLength F (.layer Q C))))
    (i : Index C) (x : Challenge C i) :
    (circuitUpdate F (.layer Q C) tr (.inr (.inr i)) x).right.left = tr.right.left := by
  have h1 := right_update_right tr
    ((((circuitIndex F C).symm i).1.natAdd 1).natAdd (roundLength (2*inDim)))
    (cast (circuitChallengeType F (.layer Q C) (.inr (.inr i))).symm x)
  exact (congrArg (fun t => t.left) h1).trans (left_update_right tr.right _ _)

theorem circuitUpdate_tail_wc {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (C : GKR.Circuit F inDim)
    (tr : (circuit F (.layer Q C)).Transcript (Fin.last (circuitLength F (.layer Q C))))
    (i : Index C) (x : Challenge C i) :
    (circuitUpdate F (.layer Q C) tr (.inr (.inr i)) x).right.right.left = tr.right.right.left := by
  have h1 := right_update_right tr
    ((((circuitIndex F C).symm i).1.natAdd 1).natAdd (roundLength (2*inDim)))
    (cast (circuitChallengeType F (.layer Q C) (.inr (.inr i))).symm x)
  refine (congrArg (fun t => t.right.left) h1).trans ?_
  refine (congrArg (fun t => t.left) (right_update_right tr.right
    (((circuitIndex F C).symm i).1.natAdd 1) _)).trans ?_
  exact left_update_right _ _ _

theorem circuitUpdate_tail_tail {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (C : GKR.Circuit F inDim)
    (tr : (circuit F (.layer Q C)).Transcript (Fin.last (circuitLength F (.layer Q C))))
    (i : Index C) (x : Challenge C i) :
    (circuitUpdate F (.layer Q C) tr (.inr (.inr i)) x).right.right.right =
      circuitUpdate F C tr.right.right.right i x := by
  have h1 := right_update_right tr
    ((((circuitIndex F C).symm i).1.natAdd 1).natAdd (roundLength (2*inDim)))
    (cast (circuitChallengeType F (.layer Q C) (.inr (.inr i))).symm x)
  refine (congrArg (fun t => t.right.right) h1).trans ?_
  refine (congrArg (fun t => t.right) (right_update_right tr.right
    (((circuitIndex F C).symm i).1.natAdd 1) _)).trans ?_
  refine (right_update_right _ _ _).trans ?_
  unfold circuitUpdate
  congr 1
  exact (cast_cast _ _ _).trans ((cast_cast _ _ _).trans (cast_cast _ _ _))

theorem circuitUpdate_round_head {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (C : GKR.Circuit F inDim)
    (tr : (circuit F (.layer Q C)).Transcript (Fin.last (circuitLength F (.layer Q C))))
    (j : Fin (LayerSumcheck.schedule inDim).length) (x : F) :
    (circuitUpdate F (.layer Q C) tr (.inr (.inl j)) x).left = tr.left := by
  exact left_update_right tr _ _

theorem circuitUpdate_round_rest {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (C : GKR.Circuit F inDim)
    (tr : (circuit F (.layer Q C)).Transcript (Fin.last (circuitLength F (.layer Q C))))
    (j : Fin (LayerSumcheck.schedule inDim).length) (x : F) :
    (circuitUpdate F (.layer Q C) tr (.inr (.inl j)) x).right.right = tr.right.right := by
  have h1 := right_update_right tr
    (((roundIndex F (2*inDim)).symm ((finCongr (LayerSumcheck.schedule_length inDim)) j)).1.castAdd _)
    (cast (circuitChallengeType F (.layer Q C) (.inr (.inl j))).symm x)
  exact (congrArg (fun t => t.right) h1).trans (right_update_left _ _ _)

theorem circuitUpdate_round_rounds {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2^outDim) (2^inDim) T)
    (C : GKR.Circuit F inDim)
    (tr : (circuit F (.layer Q C)).Transcript (Fin.last (circuitLength F (.layer Q C))))
    (j : Fin (LayerSumcheck.schedule inDim).length) (x : F) :
    (circuitUpdate F (.layer Q C) tr (.inr (.inl j)) x).right.left =
      roundUpdate F (2*inDim) tr.right.left ((finCongr (LayerSumcheck.schedule_length inDim)) j) x := by
  have h1 := right_update_right tr
    (((roundIndex F (2*inDim)).symm ((finCongr (LayerSumcheck.schedule_length inDim)) j)).1.castAdd _)
    (cast (circuitChallengeType F (.layer Q C) (.inr (.inl j))).symm x)
  refine (congrArg (fun t => t.left) h1).trans ?_
  refine (left_update_left _ _ _).trans ?_
  unfold roundUpdate
  refine Eq.trans ?_ (update_cast _ (congrArg Subtype.val (roundIndex_symm F _ _)) (by
    change F = (rounds F (2*inDim)).Challenge ((roundIndex F (2*inDim)).symm _)
    rw [roundIndex_symm, roundChallenge_type]) _ x)
  congr 1
  exact (cast_cast _ _ _).trans (cast_cast _ _ _)

/-- Decoding commutes with replacing precisely one verifier challenge. -/
theorem circuitTrace_update {d : ℕ} (C : GKR.Circuit F d)
    (tr : (circuit F C).Transcript (Fin.last (circuitLength F C)))
    (i : Index C) (x : Challenge C i) :
    circuitTrace F C (circuitUpdate F C tr i x) =
      CircuitEvents.update C (circuitTrace F C tr) i x := by
  induction C with
  | input d => rfl
  | @layer outDim inDim T Q tail ih =>
    rcases i with u | (j | j)
    · cases u
      have hh := circuitUpdate_begin_head F Q tail tr x
      have hr := circuitUpdate_begin_rest F Q tail tr x
      simp only [circuitTrace, CircuitEvents.update]
      rw [hh, hr]
    · have hh := circuitUpdate_round_head F Q tail tr j x
      have hr := circuitUpdate_round_rest F Q tail tr j x
      have hrr := circuitUpdate_round_rounds F Q tail tr j x
      simp only [circuitTrace, CircuitEvents.update, updateRound]
      have hm := roundMessages_update F (2*inDim) tr.right.left ((finCongr (LayerSumcheck.schedule_length inDim)) j) x
      rw [hh, hr, hrr, hm]
      congr 1
      funext k
      by_cases hk : k = j
      · subst k
        simp only [Function.update_self]
        exact Function.update_self ((finCongr (LayerSumcheck.schedule_length inDim)) j) _
          (roundMessages F (2*inDim) tr.right.left)
      · have hkj : (⟨k.val, by simpa only [LayerSumcheck.schedule_length] using k.isLt⟩ : Fin (2*inDim)) ≠
            (finCongr (LayerSumcheck.schedule_length inDim)) j := by
          intro he
          exact hk (Fin.ext (congrArg (fun z : Fin (2*inDim) => z.val) he))
        simp only [Function.update_of_ne hk, Function.update_of_ne hkj]
    · have hh := circuitUpdate_tail_head F Q tail tr j x
      have hr := circuitUpdate_tail_rounds F Q tail tr j x
      have hw := circuitUpdate_tail_wc F Q tail tr j x
      have ht := circuitUpdate_tail_tail F Q tail tr j x
      simp only [circuitTrace, CircuitEvents.update]
      rw [hh, hr, hw, ht]
      congr 1
      exact ih _ j x

/-- The exact recursive challenge count survives raw transcript decoding and
arbitrary fixed committed-pad translation. -/
theorem circuitEvent_count [Fintype F] (nodes : Sumcheck.Nodes F) {d : ℕ}
    (C : GKR.Circuit F d) (input : Fin (2^C.inputDim) → F)
    (pads : PadTranslation.Pads C) (g0 g1 : Fin d → F) (c0 c1 : F)
    (tr : (circuit F C).Transcript (Fin.last (circuitLength F C))) (i : Index C) :
    ((Finset.univ.filter fun x : (circuit F C).Challenge ((circuitIndex F C).symm i) =>
      Event nodes C input g0 g1 c0 c1
        (PadTranslation.unmask C pads (circuitTrace F C
          (Function.update tr ((circuitIndex F C).symm i).1 x))) i).card : NNReal) ≤
      error C i * Fintype.card ((circuit F C).Challenge ((circuitIndex F C).symm i)) := by
  apply card_le_of_mapsTo_cast (circuitChallengeType F C i) (t := Finset.univ.filter fun x =>
    Event nodes C input g0 g1 c0 c1
      (CircuitEvents.update C (PadTranslation.unmask C pads (circuitTrace F C tr)) i x) i)
  · intro x hx
    have he : Function.update tr ((circuitIndex F C).symm i).1 x =
        circuitUpdate F C tr i (cast (circuitChallengeType F C i) x) := by
      unfold circuitUpdate
      congr 1
      exact ((Equiv.cast (circuitChallengeType F C i)).symm_apply_apply x).symm
    have ht := congrArg (PadTranslation.unmask C pads)
      (circuitTrace_update F C tr i (cast (circuitChallengeType F C i) x))
    have hh := (Finset.mem_filter.mp hx).2
    rw [he] at hh
    rw [ht, unmask_update] at hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
  · exact event_count nodes C input g0 g1 c0 c1
      (PadTranslation.unmask C pads (circuitTrace F C tr)) i

end GordieHowe.GKR.ProtocolCounting
