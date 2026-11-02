-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Adversary
public import GordieHowe.Model.Quantum.Interactive.AbsorbRelay
public import GordieHowe.Model.Quantum.Interactive.MultiRelay

@[expose] public section

/-!
# Transcripts of an absorbed adversary

The absorption of an adversary's requests through a relay (`Quantum.AdaptiveIAlg.absorb`,
`GordieHowe/Model/Quantum/Interactive/Absorb.lean`) read on transcripts (output and history,
`Quantum.QueryBoundedAdversary.transcriptLaw`).

- `Quantum.AdaptiveIAlg.map_request_history`: the requests of an adversary's history are its first
  `Q` logged requests.
- `Quantum.QueryBoundedAdversary.absorbQB`: an adversary absorbed through a relay with injective
  routes is a query-bounded adversary with the same bound.
- `Quantum.QueryBoundedAdversary.transcriptLaw_le_absorbQB`: against a challenger that relays a
  main challenger at the coins along an equivalence (`SideRelay.RelaysChallenger`), the transcript
  of the adversary lies in an event of its output and requests with at most the probability that the
  transcript of the absorbed adversary against the main challenger lies in an event implied along
  the relay of the requests.
-/

namespace GordieHowe.Quantum

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

/-- **The requests of an adversary's history are its first `Q` logged requests.** -/
theorem AdaptiveIAlg.map_request_history {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)
    (C : Challenger X Y Req Resp) (v : A.toKindAlg.CW C) :
    (A.history C v).map HistoryEntry.request = (requests v.chal.logs).take C.Q :=
  Challenger.map_request_regStateOf C.Q C.respond v.chal.coins v.chal.logs
    (A.toKindAlg.ansOf C v.chal) A.toKindAlg.slots

variable [Nonempty X] [AddGroup Y] [Nonempty Y] {Req' Resp' : Type} [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req'] {t : ℕ}

/-- **An adversary absorbed through a relay with injective routes is a query-bounded adversary**
with the same bound. -/
noncomputable def QueryBoundedAdversary.absorbQB (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (F : SideRelay Req Resp Req' Resp') (hinj : ∀ c, Function.Injective (F.route c)) :
    QueryBoundedAdversary X Y Req' Resp' O t where
  Aux := 𝒜.Aux
  aux := 𝒜.aux
  sh a := (𝒜.sh a).absorbS (Req' := Req') (Resp' := Resp')
  alg a := (𝒜.alg a).absorb F
  tracePreserving a := AdaptiveIAlg.absorb_tracePreserving _ _ (𝒜.tracePreserving a)
  withinBudget a := AdaptiveIAlg.absorb_withinBudget _ F hinj (𝒜.withinBudget a)
  queries_le a := 𝒜.queries_le a

/-- **The transcript of an adversary against a relaying challenger is dominated by that of the
absorbed adversary against the main challenger**: for a challenger `C` at the coins `e.symm c'`
relaying the main challenger `C'` at `c'` through `F` (with `C.coins` the image of `C'.coins`
along `e.symm`), every event `E` of the output and the requests is at most the event `E'` of the
absorbed adversary, when `E o rs` implies `E' o` at the relay of `rs`. -/
theorem QueryBoundedAdversary.transcriptLaw_le_absorbQB
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (F : SideRelay Req Resp Req' Resp')
    (hinj : ∀ c, Function.Injective (F.route c)) (C : Challenger X Y Req Resp)
    (C' : Challenger X Y Req' Resp') (e : C.Coins ≃ C'.Coins)
    (hcoins : ∀ c', C.coins (e.symm c') = C'.coins c')
    (hR : ∀ c', F.RelaysChallenger C (e.symm c') C' c') (H : X → Y)
    (E : O → List Req → Prop) (E' : O → List Req' → Prop)
    (hE : ∀ o rs, E o (rs.take C.Q) → E' o ((F.relayList rs).take C'.Q)) :
    (𝒜.transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, E p.1 (p.2.map HistoryEntry.request)} ≤
      ((𝒜.absorbQB F hinj).transcriptLaw C' H).toOuterMeasure
        {x | ∃ p ∈ x, E' p.1 (p.2.map HistoryEntry.request)} := by
  simp only [QueryBoundedAdversary.transcriptLaw, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl ?_
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  refine le_of_le_of_eq ?_ (KindAlg.toOuterMeasure_outLaw_composeBothOut _ _ _ H _).symm
  have h := (𝒜.alg a).outLaw_absorb (C := C) (C' := C') (PMF.pure ()) (fun _ => F)
    (e.trans (Equiv.punitProd C'.Coins).symm)
    (fun _ c' => by simp [hcoins])
    (fun H _ c' => (hR c').relays H (𝒜.alg a).slots) (fun _ c => hinj c) H
    (fun d _ rlg _ _ => E' ((𝒜.alg a).out d.1.1.1) ((requests rlg).take C'.Q))
  simp only [Fintype.univ_punit, Finset.sum_singleton, PMF.pure_apply, if_true, one_mul] at h
  refine le_of_le_of_eq (MeasureTheory.measure_mono ?_) (h.trans ?_)
  · rintro o ⟨v, hv, hE'⟩
    refine ⟨v, hv, ?_⟩
    change E' ((𝒜.alg a).out v.adv.1.1.1) ((requests (F.logs v.chal.logs)).take C'.Q)
    rw [SideRelay.requests_logs]
    rw [AdaptiveIAlg.map_request_history] at hE'
    exact hE _ _ hE'
  · refine congrArg _ (Set.ext fun o => exists_congr fun v => and_congr_right fun _ => ?_)
    exact iff_of_eq (congrArg (E' _)
      (AdaptiveIAlg.map_request_history ((𝒜.alg a).absorb F) C' v).symm)

end GordieHowe.Quantum
