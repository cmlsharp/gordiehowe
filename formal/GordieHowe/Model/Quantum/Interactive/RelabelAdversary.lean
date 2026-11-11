-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.RecordReplies
public import GordieHowe.Model.Quantum.Interactive.ClassicalRelabel

@[expose] public section

/-!
# An adversary relabelled through equivalences of requests and responses

`AdaptiveIAlg.relabel A eq er`: for equivalences `eq : Req ≃ Req'` and `er : Resp ≃ Resp'`, the
adversary on requests `Req'` and responses `Resp'` that runs `A` and sends each request `r` of `A`
as `eq r`, returning each reply `a` as `a.map er.symm`. It is `A` absorbed through the relay
`SideRelay.relabelRelay eq er` (`AdaptiveIAlg.absorb`,
`GordieHowe/Model/Quantum/Interactive/Absorb.lean`). Against a challenger `C'` on `Req'` and
`Resp'`, it behaves as `A` against `C'.relabel eq er`
(`GordieHowe/Model/Quantum/Interactive/ClassicalRelabel.lean`).

## Results

- `SideRelay.relabelRelay`, `SideRelay.relabelRelay_route_injective`,
  `SideRelay.logs_relabelRelay`, `SideRelay.requestsBefore_logs_relabelRelay`,
  `SideRelay.requests_logs_relabelRelay`: the relay, its injective route, and its logs (the logs
  mapped by `eq`).
- `Challenger.answerAfter_relabel`, `Challenger.toOracle_oracleIn_relabel`: the replies and the
  oracle in force of `C'.relabel eq er` are those of `C'` at the relabelled requests.
- `SideRelay.relays_relabelRelay`: the pure game of `C'.relabel eq er` is the relay of `C'`'s.
- `AdaptiveIAlg.relabel`, `relabel_tracePreserving`, `withinBudget_relabel`: the same width,
  slots, post batches and budget as `A`.
- `AdaptiveIAlg.outLaw_relabel` (**the law**): against every challenger `C'` and at every oracle
  `H`, the output and history of `relabel A eq er` have the law of `A`'s output and history against
  `C'.relabel eq er`, with the history relabelled (`HistoryEntry.relabel`).
- `QueryBoundedAdversary.relabel`, `QueryBoundedAdversary.transcriptLaw_relabel`: the same for
  `t`-query adversaries; `RingSignature.GameAdversary.relabel`,
  `RingSignature.runLaw_relabel` for game adversaries and the law of a game's run.

The construction needs `Inhabited Req'` (the blank value of the outer request register of
`absorb`).
-/

open Finset

namespace GordieHowe.Quantum

/-! ### The relabelling relay -/

namespace SideRelay

variable {Req Resp Req' Resp' : Type}

/-- **The relabelling relay**: every request `r` is sent as `eq r` and every reply `a` returned
as `a.map er.symm`. -/
def relabelRelay (eq : Req ≃ Req') (er : Resp ≃ Resp') : SideRelay Req Resp Req' Resp' :=
  ⟨fun _ r => eq r, fun _ _ a => a.map er.symm⟩

/-- The relabelling relay sends requests injectively. -/
theorem relabelRelay_route_injective (eq : Req ≃ Req') (er : Resp ≃ Resp') (c : ℕ) :
    Function.Injective ((relabelRelay eq er).route c) :=
  eq.injective

/-- **The logs of the relabelling relay are the logs mapped by `eq`.** -/
@[simp] theorem logs_relabelRelay (eq : Req ≃ Req') (er : Resp ≃ Resp') {m : ℕ}
    (lg : LogReg Req m) : (relabelRelay eq er).logs lg = fun k => (lg k).map eq :=
  rfl

/-- The relabelled request list is the list mapped by `eq`. -/
theorem relayList_relabelRelay (eq : Req ≃ Req') (er : Resp ≃ Resp') (rs : List Req) :
    (relabelRelay eq er).relayList rs = rs.map eq := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [relayList_append_singleton, ih, List.map_append, List.map_singleton]
    rfl

/-- **The requests before slot `k` of the relabelled logs** are those of the logs mapped by
`eq`. -/
theorem requestsBefore_logs_relabelRelay (eq : Req ≃ Req') (er : Resp ≃ Resp') {m : ℕ}
    (lg : LogReg Req m) (k : ℕ) :
    requestsBefore ((relabelRelay eq er).logs lg) k = (requestsBefore lg k).map eq := by
  rw [requestsBefore_logs, relayList_relabelRelay]

/-- **The requests of the relabelled logs** are the requests mapped by `eq`. -/
theorem requests_logs_relabelRelay (eq : Req ≃ Req') (er : Resp ≃ Resp') {m : ℕ}
    (lg : LogReg Req m) :
    requests ((relabelRelay eq er).logs lg) = (requests lg).map eq :=
  requestsBefore_logs_relabelRelay eq er lg m

end SideRelay

/-! ### The relabelled challenger's pure game -/

namespace Challenger

variable {X Y Req Req' Resp Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (C' : Challenger X Y Req' Resp') (eq : Req ≃ Req') (er : Resp ≃ Resp')

/-- **The reply of the relabelled challenger** to `r` after `rs` is the reply of `C'` to `eq r`
after `rs.map eq`, mapped by `er.symm`. -/
theorem answerAfter_relabel (ω : (X → Y) × C'.Coins) (rs : List Req) (r : Req) :
    (C'.relabel eq er).toPureEnv.answerAfter ω rs r =
      (C'.toPureEnv.answerAfter ω (rs.map eq) (eq r)).map er.symm :=
  congrArg Prod.fst (C'.visReply_relabel eq er ω rs (some r))

/-- **The oracle in force of the relabelled challenger** after `rs` is that of `C'` after
`rs.map eq`. -/
theorem toOracle_oracleIn_relabel (ω : (X → Y) × C'.Coins) (rs : List Req) :
    (OracleState.toOracle ((C'.relabel eq er).toPureEnv.oracleIn ω rs) : X → Y) =
      OracleState.toOracle (C'.toPureEnv.oracleIn ω (rs.map eq)) :=
  congrArg Prod.snd (C'.visReply_relabel eq er ω rs none)

end Challenger

namespace SideRelay

/-- **The relabelled challenger is the relay of the challenger**: at every tape, the pure game of
`C'.relabel eq er` is the relay of `C'`'s through `relabelRelay eq er`. -/
theorem relays_relabelRelay {X Y Req Req' Resp Resp' : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [Nonempty Y] [AddGroup Y] (C' : Challenger X Y Req' Resp') (eq : Req ≃ Req')
    (er : Resp ≃ Resp') (ω : (X → Y) × C'.Coins) (m : ℕ) :
    (relabelRelay eq er).Relays (C'.relabel eq er).toPureEnv ω C'.toPureEnv ω m where
  answer_eq lg k r h := by
    have h' : (relabelRelay eq er).logs lg k = some (eq r) := by
      rw [logs_apply, h]
      rfl
    unfold Env.answer
    rw [h, h', Option.elim_some, Option.elim_some,
      requestsBefore_logs_relabelRelay, Challenger.answerAfter_relabel]
    rfl
  oracle_eq lg := by
    simp only [Env.oracle, requests_logs_relabelRelay]
    exact Challenger.toOracle_oracleIn_relabel C' eq er ω _

end SideRelay

/-! ### The relabelled adversary -/

namespace AdaptiveIAlg

variable {X Y Req Resp Req' Resp' O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req']
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (eq : Req ≃ Req') (er : Resp ≃ Resp')

/-- **The adversary relabelled through `eq` and `er`** (module docstring): `A` absorbed through
`relabelRelay eq er` (`absorb`), with `A`'s output. The width, the slots, the post batches, the
budget and the kinds are `A`'s.

Running time: that of `A`, plus a constant number of register exchanges and relabellings per
slot. This running time is argued here, not proved in Lean. -/
def relabel : AdaptiveIAlg (shA.absorbS (Req' := Req') (Resp' := Resp')) O where
  kind := (A.absorb (SideRelay.relabelRelay eq er)).kind
  init := (A.absorb (SideRelay.relabelRelay eq er)).init
  step := (A.absorb (SideRelay.relabelRelay eq er)).step
  out w := A.out w.work

/-- The width of `relabel A eq er` is `A`'s. -/
@[simp] theorem relabel_width : (A.relabel eq er).width = A.width := rfl

/-- The slots of `relabel A eq er` are `A`'s. -/
@[simp] theorem relabel_slots : (A.relabel eq er).slots = A.slots := rfl

/-- The post batches of `relabel A eq er` are `A`'s. -/
@[simp] theorem relabel_post : (A.relabel eq er).post = A.post := rfl

/-- The query budget of `relabel A eq er` is `A`'s. -/
@[simp] theorem relabel_budget : (A.relabel eq er).budget = A.budget := rfl

/-- **`relabel A eq er` is trace preserving** when `A` is (`absorb_tracePreserving`). -/
theorem relabel_tracePreserving (h : A.TracePreserving) : (A.relabel eq er).TracePreserving :=
  A.absorb_tracePreserving (SideRelay.relabelRelay eq er) h

variable [Nonempty X] [AddGroup Y] [Nonempty Y]

/-- **`relabel A eq er` stays within its budget** when `A` does (`absorb_withinBudget`). -/
theorem withinBudget_relabel (h : A.WithinBudget) : (A.relabel eq er).WithinBudget := by
  refine (withinBudget_iff _).2 fun C H => ?_
  have h0 := (withinBudget_iff _).1
    (A.absorb_withinBudget (SideRelay.relabelRelay eq er)
      (SideRelay.relabelRelay_route_injective eq er) h) C H
  rw [outLaw_compose_none_eq] at h0 ⊢
  exact h0

/-- **The law of the relabelled adversary** (main result): against every challenger `C'`, also
one that reprograms the oracle, and at every oracle `H`, the law of the output and the history of
`relabel A eq er` is the law of `A`'s output and history against `C'.relabel eq er`, with the
history relabelled by `HistoryEntry.relabel eq er`. -/
theorem outLaw_relabel (C' : Challenger X Y Req' Resp') (H : X → Y) :
    ((A.relabel eq er).toKindAlg.composeBothOut C' fun v =>
        ((A.relabel eq er).output C' v, (A.relabel eq er).history C' v)).outLaw H =
      (A.toKindAlg.composeBothOut (C'.relabel eq er) fun v =>
        (A.output (C'.relabel eq er) v,
          (A.history (C'.relabel eq er) v).map (HistoryEntry.relabel eq er))).outLaw H := by
  classical
  refine PMF.ext_of_apply_some fun o => ?_
  rw [KindAlg.outLaw_composeBothOut_some, KindAlg.outLaw_composeBothOut_some]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have hite : ∀ (p : Prop) [Decidable p] (x : ℝ), (if p then x else 0) = (if p then 1 else 0) * x :=
    fun p _ x => by split_ifs <;> simp
  rw [Finset.sum_congr rfl fun r' _ => hite _ _, Finset.sum_congr rfl fun r _ => hite _ _]
  refine (A.sum_diag_mgRun_absorb (SideRelay.relabelRelay eq er) C'.toPureEnv (H, c)
    (C'.relabel eq er).toPureEnv (H, c) (SideRelay.relays_relabelRelay C' eq er _ _)
    (SideRelay.relabelRelay_route_injective eq er) _).trans ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 2
  obtain ⟨⟨⟨w, k⟩, rq, rs, lg⟩, qs⟩ := r
  have e1 : (A.relabel eq er).output C' ((A.relabel eq er).toKindAlg.emb C' H c A.slots
      (A.placeClean (SideRelay.relabelRelay eq er) C'.toPureEnv (H, c) (A.slots + A.post)
        ((((w, k), rq, rs, lg), qs)))).1 = A.out w :=
    rfl
  have e2 : (A.relabel eq er).history C' ((A.relabel eq er).toKindAlg.emb C' H c A.slots
      (A.placeClean (SideRelay.relabelRelay eq er) C'.toPureEnv (H, c) (A.slots + A.post)
        ((((w, k), rq, rs, lg), qs)))).1 = (C'.stateAfter H c ((requests lg).map eq)).hist := by
    refine (KindAlg.stateAt_emb_history (A.relabel eq er).toKindAlg C' H c
      (A.placeClean (SideRelay.relabelRelay eq er) C'.toPureEnv (H, c) (A.slots + A.post)
        ((((w, k), rq, rs, lg), qs)))).trans ?_
    show (C'.stateAfter H c (requests ((SideRelay.relabelRelay eq er).logs lg))).hist = _
    rw [SideRelay.requests_logs_relabelRelay]
  have e3 : A.history (C'.relabel eq er)
      (A.toKindAlg.emb (C'.relabel eq er) H c A.slots ((((w, k), rq, rs, lg), qs))).1 =
      ((C'.relabel eq er).stateAfter H c (requests lg)).hist :=
    KindAlg.stateAt_emb_history A.toKindAlg (C'.relabel eq er) H c ((((w, k), rq, rs, lg), qs))
  have e4 : ((C'.relabel eq er).stateAfter H c (requests lg)).hist.map
      (HistoryEntry.relabel eq er) = (C'.stateAfter H c ((requests lg).map eq)).hist :=
    (C'.oracleIn_relabel eq er (H, c) (requests lg)).2.1
  have gen : ∀ (oo : O) (h₁ h₂ : List (HistoryEntry Req Resp))
      (h₃ : List (HistoryEntry Req' Resp')),
      oo = A.out w → h₃ = (C'.stateAfter H c ((requests lg).map eq)).hist →
      h₁ = ((C'.relabel eq er).stateAfter H c (requests lg)).hist → h₂ = h₁ →
      (oo, h₃) = (A.out w, h₂.map (HistoryEntry.relabel eq er)) := by
    rintro oo h₁ h₂ h₃ rfl rfl rfl rfl
    rw [e4]
  exact congrArg (· = o) (gen _ _ _ _ e1 e2 rfl e3)

end AdaptiveIAlg

/-! ### Query-bounded adversaries -/

namespace QueryBoundedAdversary

variable {X Y Req Resp Req' Resp' O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req'] [Nonempty X]
  [AddGroup Y] [Nonempty Y] {t : ℕ} (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
  (eq : Req ≃ Req') (er : Resp ≃ Resp')

/-- **The relabelled `t`-query adversary**: the same auxiliary input, and on each value `a` the
algorithm `relabel (𝒜.alg a) eq er`, with `𝒜`'s width, slots, post batches and budget, so at most
`t` queries on every branch.

Running time: that of `𝒜`, plus a constant number of register exchanges and relabellings per
slot. This running time is argued here, not proved in Lean. -/
def relabel : QueryBoundedAdversary X Y Req' Resp' O t where
  Aux := 𝒜.Aux
  aux := 𝒜.aux
  sh a := (𝒜.sh a).absorbS (Req' := Req') (Resp' := Resp')
  alg a := (𝒜.alg a).relabel eq er
  tracePreserving a := (𝒜.alg a).relabel_tracePreserving eq er (𝒜.tracePreserving a)
  withinBudget a := (𝒜.alg a).withinBudget_relabel eq er (𝒜.withinBudget a)
  queries_le a := 𝒜.queries_le a

/-- **The transcript law of the relabelled adversary**: against every challenger `C'`, also one
that reprograms the oracle, and at every oracle `H`, it is the transcript law of `𝒜` against
`C'.relabel eq er` with the history relabelled. -/
theorem transcriptLaw_relabel (C' : Challenger X Y Req' Resp') (H : X → Y) :
    (𝒜.relabel eq er).transcriptLaw C' H =
      (𝒜.transcriptLaw (C'.relabel eq er) H).map
        (Option.map fun p => (p.1, p.2.map (HistoryEntry.relabel eq er))) := by
  simp only [transcriptLaw, PMF.map_bind]
  refine congrArg 𝒜.aux.bind (funext fun a => ?_)
  rw [← KindAlg.outLaw_composeBothOut_map]
  exact (𝒜.alg a).outLaw_relabel eq er C' H

end QueryBoundedAdversary

end GordieHowe.Quantum

/-! ### Game adversaries -/

namespace GordieHowe.RingSignature

open GordieHowe.Quantum

variable {X Y Req Resp Req' Resp' In O : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req'] [Nonempty X]
  [AddGroup Y] [Nonempty Y] {t : ℕ} (eq : Req ≃ Req') (er : Resp ≃ Resp')

/-- **The relabelled game adversary**: on each start input, the `t`-query adversary
`QueryBoundedAdversary.relabel`. -/
def GameAdversary.relabel (A : GameAdversary X Y Req Resp In O t) :
    GameAdversary X Y Req' Resp' In O t :=
  fun inp => (A inp).relabel eq er

/-- **The run law of the relabelled adversaries**: against the challengers `C' k`, it is the run
law of `A` against the relabelled challengers `(C' k).relabel eq er`, with the history
relabelled. -/
theorem runLaw_relabel {K : Type} [Fintype K] [Nonempty K]
    (A : K → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (C' : K → Challenger X Y Req' Resp') :
    runLaw (fun k H => (A k H).relabel eq er) C' =
      (runLaw A fun k => (C' k).relabel eq er).map fun x =>
        (x.1, x.2.1, x.2.2.map fun p => (p.1, p.2.map (HistoryEntry.relabel eq er))) := by
  simp only [runLaw, PMF.map_bind, QueryBoundedAdversary.transcriptLaw_relabel, PMF.map_comp]
  rfl

end GordieHowe.RingSignature
