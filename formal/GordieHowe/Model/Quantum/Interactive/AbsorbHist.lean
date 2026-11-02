-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.TranscriptAbsorb
public import GordieHowe.Model.Quantum.Interactive.MultiRelayPos
public import GordieHowe.Model.Quantum.Interactive.FreshCoins

@[expose] public section

/-!
# Transcripts of an absorbed adversary, with the responses

`Quantum.QueryBoundedAdversary.transcriptLaw_le_absorbQB`
(`GordieHowe/Model/RingSignature/TranscriptAbsorb.lean`) compares events of the output and the
requests of an adversary's transcript and of the absorbed adversary's. This file compares events
of the whole histories, responses included: at the coins `c` of the relaying challenger, its
history is `histAlong` of its replies along the requests (`KindAlg.history_stateAt_emb`,
`GordieHowe/Model/Quantum/Interactive/MultiRelayPos.lean`), and the main challenger's history is
`histAlong` of its replies at the corresponding coins along the relayed requests.

- `length_histAlong`, `getElem_histAlong`: a history along requests, entry by entry.
- `Quantum.QueryBoundedAdversary.transcriptLaw_le_absorbQB_hist`.
-/

namespace GordieHowe.Quantum

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Nonempty X] [AddGroup Y] [Nonempty Y] {Req' Resp' : Type} [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req'] {t : ℕ}


section HistAlong

variable {Req Resp : Type} (ans : List Req → Req → Option Resp)

/-- The history along `l` has one entry per request. -/
@[simp]
theorem length_histAlong (l : List Req) : (histAlong ans l).length = l.length := by
  rw [← List.length_map (f := HistoryEntry.request), map_request_histAlong]

/-- **Entry `j` of the history along `l`** is request `j` with its reply after the first `j`
requests. -/
theorem getElem_histAlong (l : List Req) (j : ℕ) (hj : j < (histAlong ans l).length) :
    (histAlong ans l)[j] =
      ⟨l[j]'(by simpa using hj), ans (l.take j) (l[j]'(by simpa using hj))⟩ := by
  induction l using List.reverseRecOn generalizing j with
  | nil => simp at hj
  | append_singleton l r ih =>
    simp only [histAlong_append_singleton] at hj ⊢
    by_cases hlt : j < l.length
    · have hlt' : j < (histAlong ans l).length := by simpa using hlt
      rw [List.getElem_append_left hlt', ih j hlt']
      simp [List.getElem_append_left hlt, List.take_append_of_le_length hlt.le]
    · have hj' : j = l.length := by simp at hj; omega
      subst hj'
      rw [List.getElem_append_right (by simp)]
      simp

end HistAlong

/-- **The transcript of an adversary against a relaying challenger, with the responses, is
dominated by that of the absorbed adversary against the main challenger**: as
`transcriptLaw_le_absorbQB`, for events `E` and `E'` of the output and the whole history, when at
every coins `c` of the relaying challenger `E` at the history of the requests `rs` implies `E'` at
the main challenger's history of the relayed requests at the coins `e c`. -/
theorem QueryBoundedAdversary.transcriptLaw_le_absorbQB_hist
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (F : SideRelay Req Resp Req' Resp')
    (hinj : ∀ c, Function.Injective (F.route c)) (C : Challenger X Y Req Resp)
    (C' : Challenger X Y Req' Resp') (e : C.Coins ≃ C'.Coins)
    (hcoins : ∀ c', C.coins (e.symm c') = C'.coins c')
    (hR : ∀ c', F.RelaysChallenger C (e.symm c') C' c') (H : X → Y)
    (E : O × List (HistoryEntry Req Resp) → Prop) (E' : O × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ c o rs, E (o, histAlong (C.toPureEnv.answerAfter (H, c)) (rs.take C.Q)) →
      E' (o, histAlong (C'.toPureEnv.answerAfter (H, e c)) ((F.relayList rs).take C'.Q))) :
    (𝒜.transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((𝒜.absorbQB F hinj).transcriptLaw C' H).toOuterMeasure {x | ∃ p ∈ x, E' p} := by
  simp only [QueryBoundedAdversary.transcriptLaw, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl ?_
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  refine le_of_le_of_eq ?_ (KindAlg.toOuterMeasure_outLaw_composeBothOut _ _ _ H _).symm
  have h := (𝒜.alg a).outLaw_absorb (C := C) (C' := C') (PMF.pure ()) (fun _ => F)
    (e.trans (Equiv.punitProd C'.Coins).symm)
    (fun _ c' => by simp [hcoins])
    (fun H _ c' => (hR c').relays H (𝒜.alg a).slots) (fun _ c => hinj c) H
    (fun d _ rlg c _ => E' ((𝒜.alg a).out d.1.1.1,
      histAlong (C'.toPureEnv.answerAfter (H, ((e.trans (Equiv.punitProd C'.Coins).symm) c).2))
        ((requests rlg).take C'.Q)))
  simp only [Fintype.univ_punit, Finset.sum_singleton, PMF.pure_apply, if_true, one_mul] at h
  -- the left event at the histories read along the requests
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut_congr_emb (𝒜.alg a).toKindAlg C H _
    (fun v : (𝒜.alg a).toKindAlg.CW C => E ((𝒜.alg a).output C v,
      histAlong (C.toPureEnv.answerAfter (H, v.chal.coins)) ((requests v.chal.logs).take C.Q)))
      fun c r => by
        change E (_, (AdaptiveIAlg.history _ _ _)) ↔ _
        rw [AdaptiveIAlg.history, KindAlg.history_stateAt_emb]
        rfl]
  refine le_of_le_of_eq (MeasureTheory.measure_mono ?_) (h.trans ?_)
  · rintro o ⟨v, hv, hE⟩
    refine ⟨v, hv, ?_⟩
    change E' ((𝒜.alg a).out v.adv.1.1.1, histAlong (C'.toPureEnv.answerAfter (H, e v.chal.coins))
      ((requests (F.logs v.chal.logs)).take C'.Q))
    rw [SideRelay.requests_logs]
    exact himp _ _ _ hE
  · refine KindAlg.toOuterMeasure_outLaw_composeBothOut_congr_emb
      ((𝒜.alg a).absorb F).toKindAlg C' H _ _ fun c r => ?_
    rw [Equiv.apply_symm_apply]
    exact iff_of_eq (congrArg (fun h => E' (_, h))
      (KindAlg.history_stateAt_emb ((𝒜.alg a).absorb F).toKindAlg C' H c r).symm)

end GordieHowe.Quantum
