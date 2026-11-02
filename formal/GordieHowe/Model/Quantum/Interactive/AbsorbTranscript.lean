-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.MultiRelay

@[expose] public section

/-!
# Absorbing side requests, for transcripts

The output law of an adversary against a challenger that relays a main challenger with side coins
(`AdaptiveIAlg.outLaw_absorb`, `GordieHowe/Model/Quantum/Interactive/Absorb.lean`), read on the
transcript: the adversary's output with the requests of the answered history.

- `SideRelay.take_relayList`: relaying commutes with taking a prefix.
- `AdaptiveIAlg.toOuterMeasure_le_absorb`: against a challenger `C` whose coins are side coins `s`
  (law `σ`) and main coins, and which at side coins `s` relays the main challenger `C'` by `F' s`
  (`SideRelay.RelaysChallenger`), the adversary's output and history lie in an event `E` with at
  most the `σ`-average of the probability that the output and history of the absorbed adversary
  (`absorb (F' s)`) against `C'` lie in `E'`, when `E'` holds of the output with every history
  whose requests are the relayed requests of a history satisfying `E`.
- `QueryBoundedAdversary.absorbSide 𝒜 σ F'`: the `t`-query adversary whose auxiliary input is that
  of `𝒜` with side coins drawn from `σ`, and whose algorithm is `𝒜`'s with its requests absorbed
  through `F' s`. `QueryBoundedAdversary.transcriptLaw_le_absorbSide`: the transcript form of
  `toOuterMeasure_le_absorb`.
-/

open Finset

namespace GordieHowe.Quantum

namespace SideRelay

variable {Req Resp Req' Resp' : Type} (F : SideRelay Req Resp Req' Resp')

/-- **Relaying commutes with taking a prefix.** -/
theorem take_relayList (rs : List Req) (k : ℕ) :
    (F.relayList rs).take k = F.relayList (rs.take k) := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [relayList, List.getElem_take, List.getElem_mapIdx]

end SideRelay

namespace AdaptiveIAlg

variable {X Y Req Resp O Req' Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req'] [Nonempty X] [AddGroup Y]
  [Nonempty Y]

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
/-- **The requests of the answered history** are the first `Q` logged requests. -/
theorem map_request_history {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (C : Challenger X Y Req Resp)
    (v : A.toKindAlg.CW C) :
    (A.history C v).map HistoryEntry.request = (requests v.chal.logs).take C.Q :=
  Challenger.map_request_regStateOf C.Q C.respond _ _ _ _

/-- **Absorbing side requests, for transcripts** (module docstring). Hypotheses: the challenger's
coins are the side coins (law `σ`) and the main coins along `e` (`hcoins`); at the side coins `s`
it relays the main challenger by `F' s` (`hrel`); both answer the same number of requests (`hQ`);
each relay of requests is injective (`hinj`); and `E'` holds of the output with every history whose
requests are the relayed requests of a history satisfying `E` (`himp`). -/
theorem toOuterMeasure_le_absorb {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) {C : Challenger X Y Req Resp}
    {C' : Challenger X Y Req' Resp'} {S : Type} [Fintype S] (σ : PMF S)
    (F' : S → SideRelay Req Resp Req' Resp') (e : C.Coins ≃ S × C'.Coins)
    (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hrel : ∀ s c', (F' s).RelaysChallenger C (e.symm (s, c')) C' c') (hQ : C.Q = C'.Q)
    (hinj : ∀ s c, Function.Injective ((F' s).route c)) (H : X → Y)
    (E : O × List (HistoryEntry Req Resp) → Prop) (E' : O × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ s o (hist : List (HistoryEntry Req Resp)) (hist' : List (HistoryEntry Req' Resp')),
      E (o, hist) → hist'.map HistoryEntry.request =
        (F' s).relayList (hist.map HistoryEntry.request) → E' (o, hist')) :
    ((A.toKindAlg.composeBothOut C fun v => (A.output C v, A.history C v)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, E p} ≤
      ∑ s, σ s * (((A.absorb (F' s)).toKindAlg.composeBothOut C' fun v =>
        ((A.absorb (F' s)).output C' v, (A.absorb (F' s)).history C' v)).outLaw H).toOuterMeasure
          {x | ∃ p ∈ x, E' p} := by
  classical
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut,
    Finset.sum_congr rfl fun s _ => by rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]]
  let P : DReg A.toKindAlg.W A.width X Y Req Resp → LogReg Req A.slots → LogReg Req' A.slots →
      C.Coins → (X → Y) → Prop := fun adv _ lg' c _ =>
    ∃ hist, E (A.out adv.workspace.1, hist) ∧
      (F' (e c).1).relayList (hist.map HistoryEntry.request) = (requests lg').take C.Q
  have h := A.outLaw_absorb σ F' e hcoins (fun H s c' => (hrel s c').relays H _) hinj H P
  calc ((A.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, E (A.output C v, A.history C v)}
      ≤ ((A.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, P v.adv v.chal.logs ((F' (e v.chal.coins).1).logs v.chal.logs) v.chal.coins
            (H.reprogram (A.toKindAlg.postAss C v.chal))} := by
        refine PMF.toOuterMeasure_mono _ fun o ho => ?_
        obtain ⟨⟨v, hv, hE⟩, -⟩ := ho
        refine ⟨v, hv, A.history C v, hE, ?_⟩
        rw [A.map_request_history C v, SideRelay.requests_logs, SideRelay.take_relayList]
    _ = _ := h
    _ ≤ _ := by
        refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ zero_le
        refine PMF.toOuterMeasure_mono _ fun o ho => ?_
        obtain ⟨⟨v, hv, hist, hE, hrl⟩, -⟩ := ho
        refine ⟨v, hv, himp s _ hist _ hE ?_⟩
        rw [(A.absorb (F' s)).map_request_history C' v, ← hQ]
        simp only [Equiv.apply_symm_apply] at hrl
        exact hrl.symm

end AdaptiveIAlg

namespace QueryBoundedAdversary

variable {X Y Req Resp O Req' Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req'] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {t : ℕ}

/-- **The adversary with side coins and its requests absorbed**: auxiliary input that of `𝒜` and
side coins `s` drawn from `σ` independently, and on `(a, s)` the algorithm of `𝒜` at `a` with its
requests absorbed through `F' s` (`AdaptiveIAlg.absorb`). It has `𝒜`'s width, slots, post batches
and budget, so at most `t` queries on every branch. -/
noncomputable def absorbSide (𝒜 : QueryBoundedAdversary X Y Req Resp O t) {S : Type} (σ : PMF S)
    (F' : S → SideRelay Req Resp Req' Resp') (hinj : ∀ s c, Function.Injective ((F' s).route c)) :
    QueryBoundedAdversary X Y Req' Resp' O t where
  Aux := 𝒜.Aux × S
  aux := 𝒜.aux.bind fun a => σ.map fun s => (a, s)
  sh p := ((𝒜.alg p.1).absorb (F' p.2)).toShape
  alg p := (𝒜.alg p.1).absorb (F' p.2)
  tracePreserving p := AdaptiveIAlg.absorb_tracePreserving _ _ (𝒜.tracePreserving p.1)
  withinBudget p := AdaptiveIAlg.absorb_withinBudget _ _ (hinj p.2) (𝒜.withinBudget p.1)
  queries_le p := 𝒜.queries_le p.1

/-- **Absorbing side requests, for the transcripts of query-bounded adversaries**
(`AdaptiveIAlg.toOuterMeasure_le_absorb` at each auxiliary value): the transcript of `𝒜` against
`C` lies in `E` with at most the probability that the transcript of `absorbSide 𝒜 σ F'` against
`C'` lies in `E'`, under the hypotheses of `toOuterMeasure_le_absorb`. -/
theorem transcriptLaw_le_absorbSide (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    {C : Challenger X Y Req Resp} {C' : Challenger X Y Req' Resp'} {S : Type} [Fintype S]
    (σ : PMF S) (F' : S → SideRelay Req Resp Req' Resp') (e : C.Coins ≃ S × C'.Coins)
    (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hrel : ∀ s c', (F' s).RelaysChallenger C (e.symm (s, c')) C' c') (hQ : C.Q = C'.Q)
    (hinj : ∀ s c, Function.Injective ((F' s).route c)) (H : X → Y)
    (E : O × List (HistoryEntry Req Resp) → Prop) (E' : O × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ s o (hist : List (HistoryEntry Req Resp)) (hist' : List (HistoryEntry Req' Resp')),
      E (o, hist) → hist'.map HistoryEntry.request =
        (F' s).relayList (hist.map HistoryEntry.request) → E' (o, hist')) :
    (𝒜.transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((𝒜.absorbSide σ F' hinj).transcriptLaw C' H).toOuterMeasure {x | ∃ p ∈ x, E' p} := by
  rw [transcriptLaw, transcriptLaw, absorbSide, PMF.bind_bind, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.bind_map, PMF.toOuterMeasure_bind_apply, tsum_fintype]
  exact (𝒜.alg a).toOuterMeasure_le_absorb σ F' e hcoins hrel hQ hinj H E E' himp

end QueryBoundedAdversary

end GordieHowe.Quantum
