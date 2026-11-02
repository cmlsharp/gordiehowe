-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AbsorbTranscript
public import GordieHowe.Model.Quantum.Interactive.AbsorbBudget
public import GordieHowe.Model.Quantum.Interactive.SplitRestrict
public import GordieHowe.Model.Quantum.Interactive.Embed
public import GordieHowe.Model.Quantum.Interactive.ThenProgOut

@[expose] public section

/-!
# An adversary that records the replies it receives

`AdaptiveIAlg.recordReplies A`: the adversary with run-time kinds `A`, which besides its own run
writes each request it sends and the reply it receives into its workspace, and outputs the list of
these pairs with its output. It is `A` absorbed through the identity relay
(`AdaptiveIAlg.absorb`, `GordieHowe/Model/Quantum/Interactive/Absorb.lean`): its workspace holds
`A`'s registers, a copy of `A`'s logs and a store with the reply of each slot. Before step `k` the
reply of slot `k - 1`, written by the challenger into the outer response register, is moved into
the store and written into `A`'s response register; after step `k` the
request of slot `k` is copied into the copy of the logs and into the outer request register. The
output is `A`'s output and the stored pairs of the logged slots in slot order (`records`).

By the law below, an event of `A`'s output and history has the probability of an event of the
output of `recordReplies A` (`QueryBoundedAdversary.prob_transcriptLaw_recordReplies`).

## Results

- `recordsBefore`, `records`: the pairs `(r, st j)` of the slots `j` with a logged request `r`, in
  slot order; `length_recordsBefore`: as many as the logged requests.
- `HistoryEntry.toPair`, `HistoryEntry.ofPair`: a history entry as a pair and back.
- `Challenger.map_toPair_stateAfter_hist`: the challenger's history after the logged requests is,
  as pairs, the first `Q` records of the logs with the replies of the pure game
  (`Env.answer`).
- `SideRelay.idRelay`, `SideRelay.logs_idRelay`, `SideRelay.relays_idRelay`: the identity relay; it
  relays every environment to itself.
- `AdaptiveIAlg.recordReplies`, `recordReplies_tracePreserving`, `withinBudget_recordReplies`:
  the same width, slots, post batches and budget as `A`.
- `AdaptiveIAlg.outLaw_recordReplies` (**the law**): against every challenger `C` (also one that
  reprograms the oracle) and at every oracle `H`, the law of the output, the history and the first
  `C.Q` recorded pairs of `recordReplies A` is the law of `A`'s output, its history, and the
  history as pairs. The recorded pairs past the first `C.Q` (requests the challenger does not
  answer) are dropped by `take C.Q`.
- `QueryBoundedAdversary.recordReplies`, `QueryBoundedAdversary.transcriptLaw_recordReplies`: the
  same for `t`-query adversaries and their transcript laws;
  `QueryBoundedAdversary.prob_transcriptLaw_recordReplies`: an event of `A`'s output and history
  has the probability of the same event read on the output of `recordReplies A` (the history as the
  first `C.Q` recorded pairs). `RingSignature.GameAdversary.recordReplies` and
  `RingSignature.GameAdversary.prob_transcriptLaw_recordReplies` for game adversaries.

The construction needs `Inhabited Req` (the blank value of the outer request register of
`absorb`).
-/

open Finset

namespace GordieHowe.Quantum

/-! ### Records of the logged slots -/

section Records

variable {Req Resp : Type} {m : ℕ}

/-- **The records of the slots below `k`**: for each slot `j < k` with a logged request `r`, in
slot order, the pair `(r, st j)`. -/
def recordsBefore (lg : LogReg Req m) (st : Fin m → Option Resp) : ℕ → List (Req × Option Resp)
  | 0 => []
  | k + 1 => recordsBefore lg st k ++
      if h : k < m then ((lg ⟨k, h⟩).map fun r => (r, st ⟨k, h⟩)).toList else []

/-- **The records of all slots.** -/
def records (lg : LogReg Req m) (st : Fin m → Option Resp) : List (Req × Option Resp) :=
  recordsBefore lg st m

/-- **There are as many records below slot `k` as logged requests.** -/
theorem length_recordsBefore (lg : LogReg Req m) (st : Fin m → Option Resp) :
    ∀ k, (recordsBefore lg st k).length = (requestsBefore lg k).length
  | 0 => rfl
  | k + 1 => by
    rw [recordsBefore, requestsBefore, List.length_append, List.length_append,
      length_recordsBefore lg st k]
    by_cases h : k < m
    · rw [dif_pos h, dif_pos h]
      rcases lg ⟨k, h⟩ with _ | r <;> rfl
    · rw [dif_neg h, dif_neg h]
      simp

end Records

/-- A history entry as the pair of its request and its response. -/
def HistoryEntry.toPair {Req Resp : Type} (e : HistoryEntry Req Resp) : Req × Option Resp :=
  (e.request, e.response)

/-- The history entry of a pair of a request and a response. -/
def HistoryEntry.ofPair {Req Resp : Type} (p : Req × Option Resp) : HistoryEntry Req Resp :=
  ⟨p.1, p.2⟩

/-- **A history entry is the entry of its pair.** -/
@[simp] theorem HistoryEntry.ofPair_toPair {Req Resp : Type} (e : HistoryEntry Req Resp) :
    HistoryEntry.ofPair e.toPair = e :=
  rfl

/-! ### The history as records -/

namespace Challenger

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (C : Challenger X Y Req Resp)

/-- **The challenger's history after the logged requests is the first `Q` records**: after the
requests logged below slot `k`, the history, as pairs, is the first `Q` pairs of the logged
requests below `k` with the replies of the pure game at the logs (`Env.answer`). -/
theorem map_toPair_stateAfter_hist (H : X → Y) (c : C.Coins) {m : ℕ} (lg : LogReg Req m) :
    ∀ k, (C.stateAfter H c (requestsBefore lg k)).hist.map HistoryEntry.toPair =
      (recordsBefore lg (fun j => C.toPureEnv.answer (H, c) lg j) k).take C.Q
  | 0 => by simp [recordsBefore, requestsBefore, Env.oracleIn_nil, Challenger.toPureEnv]
  | k + 1 => by
    have ih := map_toPair_stateAfter_hist H c lg k
    have hlen := length_recordsBefore lg (fun j => C.toPureEnv.answer (H, c) lg j) k
    by_cases h : k < m
    · rw [requestsBefore_succ_of_lt lg h, recordsBefore, dif_pos h]
      rcases hr : lg ⟨k, h⟩ with _ | r
      · simpa using ih
      · simp only [Option.toList_some, Option.map_some]
        rw [stateAfter, Env.oracleIn_append_singleton, Env.update]
        have hans : C.toPureEnv.answer (H, c) lg ⟨k, h⟩ =
            C.toPureEnv.answerAfter (H, c) (requestsBefore lg k) r := by
          simp [Env.answer, hr]
        rw [hans]
        by_cases hQ : (requestsBefore lg k).length < C.Q
        · have ih' : (C.stateAfter H c (requestsBefore lg k)).hist.map HistoryEntry.toPair =
              recordsBefore lg (fun j => C.toPureEnv.answer (H, c) lg j) k :=
            ih.trans (List.take_of_length_le (by omega))
          obtain ⟨n, hn⟩ : ∃ n, C.Q -
              (recordsBefore lg (fun j => C.toPureEnv.answer (H, c) lg j) k).length = n + 1 :=
            ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
          rw [dif_pos hQ, toPureEnv_respond_state, List.take_append,
            List.take_of_length_le (by omega), hn, List.map_append, ← ih']
          simp [HistoryEntry.toPair, Env.answerAfter, hQ, toPureEnv_respond_response]
        · rw [dif_neg hQ, List.take_append_of_le_length (by omega)]
          exact ih
    · rw [requestsBefore, dif_neg h, List.append_nil, recordsBefore, dif_neg h, List.append_nil]
      exact ih

end Challenger

/-- **The history read from the placed registers after the last slot** is the challenger's
history after the logged requests. -/
theorem KindAlg.stateAt_emb_history {X Y Req Resp O : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    [Nonempty X] [AddGroup Y] [Nonempty Y] {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O)
    (C : Challenger X Y Req Resp) (H : X → Y) (c : C.Coins) (r : B.G) :
    (B.stateAt C (B.emb C H c B.slots r).1.chal B.slots).history =
      (C.stateAfter H c (requests (splitLogs r).2)).hist :=
  congrArg ChallengerRecord.history (B.regState_eq C H c (splitLogs r).2 (J := B.slots) B.slots le_rfl)

/-! ### The identity relay -/

namespace SideRelay

/-- **The identity relay**: every request is sent as itself and every reply returned as itself. -/
def idRelay (Req Resp : Type) : SideRelay Req Resp Req Resp :=
  ⟨fun _ r => r, fun _ _ a => a⟩

/-- **The identity relay keeps the logs.** -/
@[simp] theorem logs_idRelay {Req Resp : Type} {m : ℕ} (lg : LogReg Req m) :
    (idRelay Req Resp).logs lg = lg := by
  funext k
  simp [logs, idRelay]

/-- **The identity relay relays every environment to itself**, at every tape. -/
theorem relays_idRelay {X Y Req Resp : Type} [AddGroup Y] {Ω St : Type} {Q : ℕ}
    [OracleState St X Y] (E : Env Ω Req Resp X Y Q St) (ω : Ω) (m : ℕ) :
    (idRelay Req Resp).Relays E ω E ω m where
  answer_eq lg k r _ := by rw [logs_idRelay]; rfl
  oracle_eq lg := by rw [logs_idRelay]

/-- The identity relay sends requests injectively. -/
theorem idRelay_route_injective {Req Resp : Type} (c : ℕ) :
    Function.Injective ((idRelay Req Resp).route c) :=
  fun _ _ h => h

end SideRelay

/-! ### The adversary that records its replies -/

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Inhabited Req]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

/-- **The adversary that records the replies it receives** (module docstring): `A` absorbed
through the identity relay (`absorb`), whose output is `A`'s output with the recorded pairs of
request and reply of the logged slots, in slot order (`records` of the copy of the logs and the
store). The width, the slots, the post batches, the budget and the kinds are `A`'s.

Running time: that of `A`, plus a constant number of register exchanges per slot. This running time
is argued here, not proved in Lean. -/
def recordReplies :
    AdaptiveIAlg (shA.absorbS (Req' := Req) (Resp' := Resp)) (O × List (Req × Option Resp)) where
  kind := (A.absorb (SideRelay.idRelay Req Resp)).kind
  init := (A.absorb (SideRelay.idRelay Req Resp)).init
  step := (A.absorb (SideRelay.idRelay Req Resp)).step
  out w := (A.out w.work, records w.logs w.store)

/-- The width of `recordReplies A` is `A`'s. -/
@[simp] theorem recordReplies_width : A.recordReplies.width = A.width := rfl

/-- The slots of `recordReplies A` are `A`'s. -/
@[simp] theorem recordReplies_slots : A.recordReplies.slots = A.slots := rfl

/-- The post batches of `recordReplies A` are `A`'s. -/
@[simp] theorem recordReplies_post : A.recordReplies.post = A.post := rfl

/-- The query budget of `recordReplies A` is `A`'s. -/
@[simp] theorem recordReplies_budget : A.recordReplies.budget = A.budget := rfl

/-- **`recordReplies A` is trace preserving** when `A` is (`absorb_tracePreserving`). -/
theorem recordReplies_tracePreserving (h : A.TracePreserving) :
    A.recordReplies.TracePreserving :=
  A.absorb_tracePreserving (SideRelay.idRelay Req Resp) h

variable [Nonempty X] [AddGroup Y] [Nonempty Y]

/-- **`recordReplies A` stays within its budget** when `A` does (`absorb_withinBudget`). -/
theorem withinBudget_recordReplies (h : A.WithinBudget) : A.recordReplies.WithinBudget := by
  refine (withinBudget_iff _).2 fun C H => ?_
  have h0 := (withinBudget_iff _).1
    (A.absorb_withinBudget (SideRelay.idRelay Req Resp) SideRelay.idRelay_route_injective h) C H
  rw [outLaw_compose_none_eq] at h0 ⊢
  exact h0

-- TODO(unbundle-M4): `refine gen` instead of restated `have`s (fresh instances); restore once
-- M1b's named register types and shape-indexed AdaptiveIAlg make both sides one instance path
/-- **The law of the recorded replies** (main result): against every challenger `C`, also one
that reprograms the oracle, and at every oracle `H`, the law of the output of `A`, the history,
and the first `C.Q` recorded pairs of `recordReplies A` is the law of `A`'s output, its history,
and its history as pairs (`HistoryEntry.toPair`). -/
theorem outLaw_recordReplies (C : Challenger X Y Req Resp) (H : X → Y) :
    (A.recordReplies.toKindAlg.composeBothOut C fun v =>
        (((A.recordReplies.output C v).1, A.recordReplies.history C v),
          (A.recordReplies.output C v).2.take C.Q)).outLaw H =
      (A.toKindAlg.composeBothOut C fun v =>
        ((A.output C v, A.history C v), (A.history C v).map HistoryEntry.toPair)).outLaw H := by
  classical
  refine PMF.ext_of_apply_some fun o => ?_
  rw [KindAlg.outLaw_composeBothOut_some, KindAlg.outLaw_composeBothOut_some]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have hite : ∀ (p : Prop) [Decidable p] (x : ℝ), (if p then x else 0) = (if p then 1 else 0) * x :=
    fun p _ x => by split_ifs <;> simp
  rw [Finset.sum_congr rfl fun r' _ => hite _ _, Finset.sum_congr rfl fun r _ => hite _ _]
  refine (A.sum_diag_mgRun_absorb (SideRelay.idRelay Req Resp) C.toPureEnv (H, c) C.toPureEnv (H, c)
    (SideRelay.relays_idRelay _ _ _) SideRelay.idRelay_route_injective _).trans ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 2
  obtain ⟨⟨⟨w, k⟩, rq, rs, lg⟩, qs⟩ := r
  have hst : A.storeBelow (SideRelay.idRelay Req Resp) C.toPureEnv (H, c) (A.slots + A.post) lg =
      fun j => C.toPureEnv.answer (H, c) lg j := by
    funext j
    simp only [storeBelow, mainAns, SideRelay.logs_idRelay]
    rw [if_pos (by omega)]
  have e4 : (records lg fun j => C.toPureEnv.answer (H, c) lg j).take C.Q =
      (C.stateAfter H c (requests lg)).hist.map HistoryEntry.toPair :=
    (C.map_toPair_stateAfter_hist H c lg A.slots).symm
  have gen : ∀ (oo : O × List (Req × Option Resp)) (o₁ : O) (h₁ h₂ : List (HistoryEntry Req Resp)),
      oo = (A.out w, records lg fun j => C.toPureEnv.answer (H, c) lg j) → o₁ = A.out w →
      h₁ = (C.stateAfter H c (requests lg)).hist → h₂ = (C.stateAfter H c (requests lg)).hist →
      ((oo.1, h₁), oo.2.take C.Q) = ((o₁, h₂), h₂.map HistoryEntry.toPair) := by
    rintro oo o₁ h₁ h₂ rfl rfl rfl rfl
    rw [e4]
  refine congrArg (· = o) (gen _ _ _ _ ?_ rfl ?_ ?_)
  · show (A.out w, records lg (A.storeBelow (SideRelay.idRelay Req Resp) C.toPureEnv (H, c)
      (A.slots + A.post) lg)) = _
    rw [hst]
  · refine (KindAlg.stateAt_emb_history _ C H c _).trans ?_
    show (C.stateAfter H c (requests ((SideRelay.idRelay Req Resp).logs lg))).hist = _
    rw [SideRelay.logs_idRelay]
  · exact KindAlg.stateAt_emb_history _ C H c _

end AdaptiveIAlg

/-! ### Query-bounded adversaries -/

namespace QueryBoundedAdversary

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Inhabited Req] [Nonempty X]
  [AddGroup Y] [Nonempty Y] {t : ℕ} (𝒜 : QueryBoundedAdversary X Y Req Resp O t)

/-- **The `t`-query adversary that records the replies it receives**: the same auxiliary input,
and on each value `a` the algorithm `recordReplies (𝒜.alg a)`, with `𝒜`'s width, slots, post
batches and budget, so at most `t` queries on every branch.

Running time: that of `𝒜`, plus a constant number of register exchanges per slot. This running
time is argued here, not proved in Lean. -/
def recordReplies : QueryBoundedAdversary X Y Req Resp (O × List (Req × Option Resp)) t where
  Aux := 𝒜.Aux
  aux := 𝒜.aux
  sh a := (𝒜.sh a).absorbS (Req' := Req) (Resp' := Resp)
  alg a := (𝒜.alg a).recordReplies
  tracePreserving a := (𝒜.alg a).recordReplies_tracePreserving (𝒜.tracePreserving a)
  withinBudget a := (𝒜.alg a).withinBudget_recordReplies (𝒜.withinBudget a)
  queries_le a := 𝒜.queries_le a

/-- **The transcript law of the adversary that records its replies**: against every challenger
`C`, also one that reprograms the oracle, and at every oracle `H`, its output with its history and
the first `C.Q` recorded pairs have the law of `𝒜`'s transcript with the history as pairs. -/
theorem transcriptLaw_recordReplies (C : Challenger X Y Req Resp) (H : X → Y) :
    (𝒜.recordReplies.transcriptLaw C H).map
        (Option.map fun p => ((p.1.1, p.2), p.1.2.take C.Q)) =
      (𝒜.transcriptLaw C H).map (Option.map fun p => (p, p.2.map HistoryEntry.toPair)) := by
  simp only [transcriptLaw, PMF.map_bind]
  refine congrArg 𝒜.aux.bind (funext fun a => ?_)
  rw [← KindAlg.outLaw_composeBothOut_map, ← KindAlg.outLaw_composeBothOut_map]
  exact (𝒜.alg a).outLaw_recordReplies C H

/-- **An event of the transcript as an event of the recorded output**: against every challenger
`C`, also one that reprograms the oracle, and at every oracle `H`, the transcript of `𝒜` lies in
`E` with the probability that the output `(o, l)` of `recordReplies 𝒜` satisfies `E` at `o` and the
history of the first `C.Q` pairs of `l` (`HistoryEntry.ofPair`). -/
theorem prob_transcriptLaw_recordReplies (C : Challenger X Y Req Resp) (H : X → Y)
    (E : O × List (HistoryEntry Req Resp) → Prop) :
    (𝒜.transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, E p} =
      (𝒜.recordReplies.transcriptLaw C H).toOuterMeasure
        {x | ∃ p ∈ x, E (p.1.1, (p.1.2.take C.Q).map HistoryEntry.ofPair)} := by
  have h := congrArg (fun μ => PMF.toOuterMeasure μ
    {x : Option ((O × List (HistoryEntry Req Resp)) × List (Req × Option Resp)) |
      ∃ q ∈ x, E (q.1.1, q.2.map HistoryEntry.ofPair)}) (𝒜.transcriptLaw_recordReplies C H)
  simp only [PMF.toOuterMeasure_map_apply] at h
  convert h.symm using 2
  · ext x
    rcases x with _ | p <;> simp [Function.comp_def]
  · ext x
    rcases x with _ | p
    · simp
    · simp only [Set.mem_preimage, Set.mem_setOf_eq, Option.map_some, Option.mem_def,
        Option.some.injEq, List.map_take]
      constructor
      · rintro ⟨q, rfl, he⟩
        exact ⟨_, rfl, by simpa [List.map_take] using he⟩
      · rintro ⟨q, rfl, he⟩
        exact ⟨p, rfl, by simpa [List.map_take] using he⟩

end QueryBoundedAdversary

end GordieHowe.Quantum

/-! ### Game adversaries -/

namespace GordieHowe.RingSignature.GameAdversary

open GordieHowe.Quantum

variable {X Y Req Resp In O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Inhabited Req] [Nonempty X]
  [AddGroup Y] [Nonempty Y] {t : ℕ}

/-- **The game adversary that records the replies it receives**: on each start input, the
`t`-query adversary `QueryBoundedAdversary.recordReplies`. -/
def recordReplies (A : GameAdversary X Y Req Resp In O t) :
    GameAdversary X Y Req Resp In (O × List (Req × Option Resp)) t :=
  fun inp => (A inp).recordReplies

/-- **An event of a game adversary's transcript as an event of the recorded output**
(`QueryBoundedAdversary.prob_transcriptLaw_recordReplies` at the start input `inp`). -/
theorem prob_transcriptLaw_recordReplies (A : GameAdversary X Y Req Resp In O t) (inp : In)
    (C : Challenger X Y Req Resp) (H : X → Y) (E : O × List (HistoryEntry Req Resp) → Prop) :
    ((A inp).transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, E p} =
      ((A.recordReplies inp).transcriptLaw C H).toOuterMeasure
        {x | ∃ p ∈ x, E (p.1.1, (p.1.2.take C.Q).map HistoryEntry.ofPair)} :=
  (A inp).prob_transcriptLaw_recordReplies C H E

end GordieHowe.RingSignature.GameAdversary
