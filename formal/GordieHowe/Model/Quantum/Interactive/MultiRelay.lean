-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.FromDistinguisher
public import GordieHowe.Model.Quantum.Interactive.SplitHybrid
public import GordieHowe.Model.Quantum.Interactive.QueryBoundedZK
public import GordieHowe.Model.Quantum.Pure.MultiRelayOrigin
public import GordieHowe.Model.Quantum.Pure.MultiRelaySim
public import GordieHowe.Model.Quantum.Interactive.AbsorbRelay
public import GordieHowe.Model.RingSignature.Adversary

@[expose] public section

/-!
# The multi-request relay of an adversary

An adversary `A` (`AdaptiveIAlg`) plays against a challenger `Cout` whose replies are computed by
relay programs `F` (`MultiRelay`): each of the first `Cout.Q` requests is answered by a classical
program that adaptively makes at most `K` requests to a main challenger `C` and at most `qR` oracle
queries, and computes the reply from their answers (main requests need not determine the request;
the relay of a request may repeat or share main requests). The relayed adversary
`A.relayAdv F Cout.Q out'` plays against `C` itself.

- `MultiRelay.RelaysChallenger F Cout C κ` (the hypotheses): the coins of `Cout` are the image of
  `C`'s along `κ`; neither challenger reprograms the oracle; at the oracle `H` and the main coins
  `c'`, `Cout` at the coins `κ c'` answers its request after `rs`, while `|rs| < Cout.Q`, by
  `F.runReply` against `C`'s replies after the main requests `F.mainReqs` of `rs` (`K · |rs|` of
  them, `MultiRelay.length_mainReqs`).
- `AdaptiveIAlg.pureD`: the adversary's pure distinguisher (the dilation of its trace-preserving
  form `toTPKindAlg true`, frozen on the ended branches, the post batches as `post` further query
  slots), with a budget of
  `budget + post` query slots (`pureD_budget`, from `dilTPBudget`; `tp_step_op_eq_zero` is the
  counting step). `AdaptiveIAlg.toOuterMeasure_outLaw_pureD`: every event of the trace-preserving
  form's composed registers has the coin average of the probability, in the pure distinguisher's
  final state, of the running branches satisfying it. The model's law is at most the
  trace-preserving form's (`toOuterMeasure_outLaw_composeBothOut_le`), and equal to it when the
  model's mixed game keeps the trace (`toOuterMeasure_outLaw_composeBothOut_eq`).
  `AdaptiveIAlg.trace_mgRun_toTPKindAlg`: the trace-preserving form's mixed game keeps the trace;
  `AdaptiveIAlg.prob_compl_dilSet_univ`: so its dilated game has no weight off the running
  branches.
- `AdaptiveIAlg.relayAdv A F Q out'` (the relayed adversary, explicit): the relay of `pureD`
  (`Distinguisher.relay`) as an adversary with run-time kinds of width `1`, no post batches and the
  budget `relayBudget = width · (budget + post) + Q · qR + Q · qP`, completed to abort an
  over-budget call
  (`abortAlg`), with the output `out'` read from the relay's workspace. It is trace preserving and
  within its budget (`relayAdv_tracePreserving`, `relayAdv_withinBudget`), and
  `width' · (budget' + post') = width · (budget + post) + Q · qR + Q · qP` (`relayAdv_queries`),
  and `width · (budget + post) + Q · qR` for a relay without pad sub-slots
  (`relayAdv_queries_of_qP`).
  `AdaptiveIAlg.relayD`: the relayed distinguisher; `AdaptiveIAlg.prob_run_relayD`: under
  `RelaysChallenger`, an event of its run against `C` has the probability, in the dilated
  trace-preserving form's final state against `Cout`, of the basis states whose placement lies in it.
- `AdaptiveIAlg.toOuterMeasure_le_relayAdv` (**the relay, event form**): under `RelaysChallenger`,
  at every oracle `H`, an event `P` of `A`'s composed registers against `Cout` has at most the
  probability of an event `P'` of the relayed adversary's composed registers against `C` that holds
  at the placement (`relayPlace`) of every running branch of the dilated trace-preserving form's
  game satisfying `P`.
  `AdaptiveIAlg.toOuterMeasure_eq_relayAdv`: the two are equal when the dilated adversary's mixed
  game against the challenger has trace 1 (`htr`, as for every adversary within its budget) and
  `P'` at the placement of a running branch implies `P`.
- `AdaptiveIAlg.output_relayPlace`, `AdaptiveIAlg.history_relayPlace`: at a placement, the relayed
  adversary with the output `relayOut` outputs `A`'s output, and every request of its history is
  the idle request or one that the program of a request of `A`'s history can make
  (`MultiRelay.CanAsk`).
- `QueryBoundedAdversary.relay 𝒜 F Q` (a `t`-query adversary to a `(t + Q · qR + Q · qP)`-query
  adversary)
  and `QueryBoundedAdversary.transcriptLaw_le_relay` (**the relay for transcripts**): under
  `RelaysChallenger`, at every oracle `H`, the transcript of `𝒜` against `Cout` lies in an event
  `E` with at most the probability that the transcript of `𝒜.relay F Cout.Q` against `C` lies in
  `E'`, when `E'` holds of `(o, hist')` whenever `E` holds of `(o, hist)` and every request of
  `hist'` is the idle request or one that the program of a request of `hist` can make.
  `QueryBoundedAdversary.mono`, `QueryBoundedAdversary.transcriptLaw_mono`: a larger query bound,
  with the same transcript law.
- `RingSignature.GameAdversary.relay A F qR hF Q` and
  `RingSignature.GameAdversary.transcriptLaw_le_relay`: the same for game adversaries, with relay
  programs depending on the start input and at most `qR` queries each.
- `Challenger.NoAssign` (a challenger without assignments): its oracle in force is the base oracle
  and its replies are its reply programs run on it (`Challenger.NoAssign.oracleIn`,
  `Challenger.NoAssign.oracle_eq`, `Challenger.NoAssign.answerAfter_eq`).
  `Challenger.map_request_regStateOf`: the requests of a challenger's history are its first `Q`
  logged requests.
- `prob_mono`, `prob_union_le`, `prob_compl`, `sum_toReal_map_mul`,
  `KindAlg.toOuterMeasure_outLaw_composeBothOut`: monotonicity, the union bound and the complement
  for the probability of a set of basis states, coin averages along a map of the coins, and events
  of a composition's output as events of its composed registers.
-/

open Finset Matrix
open scoped BigOperators ENNReal ComplexOrder

namespace GordieHowe.Quantum

/-- **A larger event has a larger probability.** -/
theorem prob_mono {ι : Type*} [Fintype ι] {S T : Set ι} (h : S ⊆ T) (v : QState ι) :
    prob S v ≤ prob T v := by
  classical
  rw [prob, prob, norm_mask_sq, norm_mask_sq, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hS : i ∈ S
  · rw [if_pos hS, if_pos (h hS)]
  · rw [if_neg hS]
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

/-- **The probability of a union is at most the sum.** -/
theorem prob_union_le {ι : Type*} [Fintype ι] (S T : Set ι) (v : QState ι) :
    prob (S ∪ T) v ≤ prob S v + prob T v := by
  classical
  rw [prob, prob, prob, norm_mask_sq, norm_mask_sq, norm_mask_sq, Finset.sum_filter,
    Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h0 := sq_nonneg ‖v i‖
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, h0]

/-- **The probability of a complement** is the squared norm minus the probability. -/
theorem prob_compl {ι : Type*} [Fintype ι] (S : Set ι) (v : QState ι) :
    prob Sᶜ v = ‖v‖ ^ 2 - prob S v := by
  classical
  rw [← prob_univ, prob, prob, prob, norm_mask_sq, norm_mask_sq, norm_mask_sq, Finset.sum_filter,
    Finset.sum_filter, Finset.sum_filter, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hS : i ∈ S
  · simp [hS]
  · simp [hS]

/-- **A coin average along a map of the coins**: if the coins `μ` are the image of the coins `ν`
along `κ`, a `μ`-average is the `ν`-average of the values at `κ`. -/
theorem sum_toReal_map_mul {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (ν : PMF α)
    (κ : α → β) (f : β → ℝ) :
    ∑ b, ((ν.map κ) b).toReal * f b = ∑ a, (ν a).toReal * f (κ a) := by
  have hmap : ∀ b, ((ν.map κ) b).toReal = ∑ a, if κ a = b then (ν a).toReal else 0 := by
    intro b
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum fun a _ => by
      split_ifs
      · exact PMF.apply_ne_top _ _
      · exact ENNReal.zero_ne_top]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl
  simp only [hmap, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (κ a) (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])
    (by simp)]
  rw [if_pos rfl]

/-- **The requests of a challenger's history are its first `Q` logged requests**, in slot order. -/
theorem Challenger.map_request_regStateOf {X Y Req Resp Coins : Type} (Q : ℕ)
    (respond : Coins → List (HistoryEntry Req Resp) → Req → OracleProg X Y (Reply X Y Resp))
    {m : ℕ} (ω : Coins) (lg : LogReg Req m) (ans : Fin m → List Y) : ∀ j,
    (Challenger.regStateOf Q respond ω lg ans j).history.map HistoryEntry.request =
      (requestsBefore lg j).take Q
  | 0 => by simp [Challenger.regStateOf, requestsBefore]
  | j + 1 => by
    have ih := Challenger.map_request_regStateOf Q respond ω lg ans j
    have hlen : (Challenger.regStateOf Q respond ω lg ans j).history.length =
        min (requestsBefore lg j).length Q := by
      rw [← List.length_map (f := HistoryEntry.request), ih, List.length_take, min_comm]
    rw [Challenger.regStateOf]
    dsimp only
    by_cases hj : j < m
    · rw [dif_pos hj, requestsBefore, dif_pos hj]
      rcases hl : lg ⟨j, hj⟩ with _ | r
      · simpa using ih
      · simp only
        split_ifs with hq
        · rw [List.map_append, ih, List.map_singleton, Option.toList_some]
          have : (requestsBefore lg j).length < Q := by omega
          rw [List.take_of_length_le this.le, List.take_of_length_le (by simp; omega)]
        · rw [ih, Option.toList_some, List.take_append_of_le_length (by omega)]
    · rw [dif_neg hj, requestsBefore, dif_neg hj, List.append_nil]
      exact ih

/-- **A challenger that never reprograms**: every reply program has no assignments. -/
def Challenger.NoAssign {X Y Req Resp : Type} (C : Challenger X Y Req Resp) : Prop :=
  ∀ (c : C.Coins) (hist : List (HistoryEntry Req Resp)) (r : Req) (G : X → Y),
    ((C.respond c hist r).run G).assignments = []

section NoAssign

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  {C : Challenger X Y Req Resp}

/-- **The state of a challenger that never reprograms** after the requests `rs`: the base oracle,
no assignments, and a history of `min |rs| Q` entries. -/
theorem Challenger.NoAssign.oracleIn (hC : C.NoAssign) (H : X → Y) (c : C.Coins) (rs : List Req) :
    (C.toPureEnv.oracleIn (H, c) rs).base = H ∧ (C.toPureEnv.oracleIn (H, c) rs).ass = [] ∧
      (C.toPureEnv.oracleIn (H, c) rs).hist.length = min rs.length C.Q := by
  induction rs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, by simp [Env.oracleIn, Challenger.toPureEnv]⟩
  | append_singleton rs r ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Env.oracleIn_append_singleton]
    by_cases hq : rs.length < C.Q
    · rw [C.update_toPureEnv_of_lt _ _ _ hq]
      refine ⟨h1, ?_, ?_⟩
      · simp only [h2, List.nil_append]
        exact hC _ _ _ _
      · simp only [List.length_append, List.length_singleton, h3]
        omega
    · rw [C.update_toPureEnv_of_le _ _ _ (not_lt.1 hq)]
      refine ⟨h1, h2, ?_⟩
      rw [h3]
      simp only [List.length_append, List.length_singleton]
      omega

/-- **A challenger that never reprograms keeps the oracle** at every logs. -/
theorem Challenger.NoAssign.oracle_eq (hC : C.NoAssign) (H : X → Y) (c : C.Coins) {k : ℕ}
    (lg : LogReg Req k) : C.toPureEnv.oracle (H, c) lg = H := by
  obtain ⟨h1, h2, -⟩ := hC.oracleIn H c (requests lg)
  change (C.toPureEnv.oracleIn (H, c) (requests lg)).base.reprogram
    (C.toPureEnv.oracleIn (H, c) (requests lg)).ass = H
  rw [h1, h2]
  rfl

/-- **The reply of a challenger that never reprograms** to a request numbered below `Q`: its reply
program after a history of `|rs|` entries, run on the oracle. -/
theorem Challenger.NoAssign.answerAfter_eq (hC : C.NoAssign) (H : X → Y) (c : C.Coins)
    (rs : List Req) (r : Req) (hi : rs.length < C.Q) :
    C.toPureEnv.answerAfter (H, c) rs r =
      ((C.respond c (C.toPureEnv.oracleIn (H, c) rs).hist r).run H).response := by
  obtain ⟨h1, h2, -⟩ := hC.oracleIn H c rs
  rw [C.answerAfter_toPureEnv_of_lt _ _ _ hi, h1, h2]
  rfl

end NoAssign

/-- **A challenger whose replies are the relay `F` of a main challenger's** (the hypotheses of the
multi-request relay): along the map `κ` of the main coins to the challenger's coins, the
challenger's coins are the image of the main coins (`coins_eq`); neither challenger reprograms the
oracle (`oracle_eq`, `oracle_eq'`); at the oracle `H` and the main coins `c'`, the challenger at
the coins `κ c'` answers its request after the requests `rs`, while fewer than `Cout.Q` came before,
by the relay's reply against the main replies after the main requests of `rs`
(`MultiRelay.runReply`, `MultiRelay.mainReqs`). -/
structure MultiRelay.RelaysChallenger {X Y Req Resp Req' Resp' : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Nonempty Y]
    [Inhabited X] [Zero Y] [Inhabited Req'] {Xs Ys : Type} [Zero Ys]
    (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (Cout : Challenger X Y Req Resp)
    (C : Challenger X Y Req' Resp') (κ : C.Coins → Cout.Coins) : Prop where
  /-- The challenger's coins are the image of the main coins. -/
  coins_eq : Cout.coins = C.coins.map κ
  /-- The challenger does not reprogram the oracle. -/
  oracle_eq : ∀ (H : X → Y) (c : Cout.Coins) {k : ℕ} (lg : LogReg Req k),
    Cout.toPureEnv.oracle (H, c) lg = H
  /-- The main challenger does not reprogram the oracle. -/
  oracle_eq' : ∀ (H : X → Y) (c' : C.Coins) {k : ℕ} (lg : LogReg Req' k),
    C.toPureEnv.oracle (H, c') lg = H
  /-- The challenger's replies are the relay's against the main replies. -/
  answer_eq : ∀ (H : X → Y) (c' : C.Coins) (rs : List Req) (r : Req), rs.length < Cout.Q →
    Cout.toPureEnv.answerAfter (H, κ c') rs r = F.runReply (C.toPureEnv.answerAfter (H, c')) H r
      (F.mainReqs Cout.Q (C.toPureEnv.answerAfter (H, c')) H rs)

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) [AddGroup Y]

/-! ### The trace-preserving form, step by step -/

/-- **A step of the trace-preserving form before a slot** moves a branch that has ended, or one
with `c ≤ budget` query slots, to an ended branch or to one with the count advanced on a query
branch and still within the budget (`step_op_eq_zero`, `tp_hl`, `tp_hr`, `tp_habs`). -/
theorem tp_step_op_eq_zero {freeze : Bool} {k : StepIdx A.slots A.post} (hk : (k : ℕ) < A.slots)
    {c : ℕ}
    (z : (A.toTPKindAlg freeze).R) (y x : DReg A.toKindAlg.W A.width X Y Req Resp)
    (hx : x.workspace.2 = A.ended ∨ (A.wcnt x.workspace = c ∧ c ≤ A.budget))
    (hy : ¬ (y.workspace.2 = A.ended ∨ (A.wcnt y.workspace = c + (if A.kind y.workspace.1 then 0 else 1) ∧
      A.wcnt y.workspace ≤ A.budget))) :
    ((A.toTPKindAlg freeze).step k).op z y x = 0 := by
  rw [not_or] at hy
  have hya : y ∈ A.aliveD := hy.1
  rcases hx with hx | ⟨hx, hc⟩
  · by_contra h
    exact A.tp_habs k z y x h (fun hm => hm hx) hya
  · have hxa : x ∈ A.aliveD := by
      intro he
      simp only [wcnt] at hx
      rw [he, val_ended] at hx
      omega
    rcases z with r | t
    · have h := A.tp_hl (freeze := freeze) k r y x hxa
      split_ifs at h with hh
      · rw [h]
        exact A.step_op_eq_zero hk hc r y x hx hy.2
      · exact absurd hya hh
    · exact A.tp_hr k t y x hya

/-- The post batches of the dilated trace-preserving form as unitaries. -/
noncomputable def dilPostU (j : ℕ) :
    QState (DReg shA.tpKindS.DW shA.width X Y Req Resp) ≃ₗᵢ[ℂ]
      QState (DReg shA.tpKindS.DW shA.width X Y Req Resp) :=
  (A.toTPKindAlg true).unitOut.uStepD (A.slots + 1 + j)

/-- **The pure distinguisher of an adversary**: the dilation (`KindAlg.dilate`, the output
forgotten) of its frozen trace-preserving form (`toTPKindAlg true`), with the post batches as
`post` further query slots (`Distinguisher.withPostSlots`). It is the dilation of the
trace-preserving form, not of the model's semantics `toKindAlg`. It is frozen because an ended
branch would otherwise keep requesting and leave its replies unstored, which breaks the relation
between the relay's blocks and the adversary's requests; frozen, it keeps its registers and sends
its request register again. -/
@[irreducible, no_expose] noncomputable def pureD :
    Distinguisher (shA.tpKindS.DW × Bool) X Y Req Resp shA.width (shA.slots + shA.post) :=
  ((A.toTPKindAlg true).unitOut.dilate ()).withPostSlots A.dilPostU A.post

/-- The pure distinguisher (`pureD` is sealed). -/
theorem pureD_eq : A.pureD = ((A.toTPKindAlg true).unitOut.dilate ()).withPostSlots A.dilPostU A.post := by
  unfold pureD; rfl

/-- The post phase of the dilated trace-preserving form is `post` query batches of `dilPostU`
(`Distinguisher.postN`). -/
theorem postOp_unitOut (H : X → Y) :
    (A.toTPKindAlg true).unitOut.postOp H = Distinguisher.postN A.dilPostU H A.post :=
  (A.toTPKindAlg true).unitOut.postOpN_eq_postN H _

/-- The final state of the pure distinguisher: that of the dilated trace-preserving form with its
post phase, placed with the flag of the post slots. -/
theorem final_pureD {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St)
    (ω : Ω) :
    A.pureD.final E noPost ω = embV (embR A.post true)
      (((A.toTPKindAlg true).unitOut.dilate ()).final E (A.toTPKindAlg true).unitOut.postOp ω) := by
  have hpo : (fun H => Distinguisher.postN A.dilPostU H A.post) =
      (A.toTPKindAlg true).unitOut.postOp :=
    funext fun H => (A.postOp_unitOut H).symm
  rw [pureD_eq, Distinguisher.final_withPostSlots, hpo]

/-- The kind of the pure distinguisher: the trace-preserving form's kind or the halting flag,
with the post flag clear. -/
theorem pureD_kind (w : shA.tpKindS.DW × Bool) :
    A.pureD.kind w = (((A.toTPKindAlg true).unitOut.kind w.1.1 || w.1.2.1) && !w.2) := by
  rw [pureD_eq]
  simp only [Distinguisher.withPostSlots, KindAlg.dilate_kind]

variable [Nonempty X] [Nonempty Y]

/-- **The dilated trace-preserving form has a budget of `budget` query slots**: the invariant of
`dilBudget`, where a branch may also have ended; an ended branch requests, so it makes no query
of its own. -/
noncomputable def dilTPBudget : ((A.toTPKindAlg true).unitOut.dilate ()).Budget A.budget where
  inv k c := {w | MixedAlg.Clean (k + 1) w.2.2 ∧ (w.2.1 = true ∨ (w.1.2 = A.ended ∨
    (A.wcnt w.1 = c + (if A.kind w.1.1 then 0 else 1) ∧ A.wcnt w.1 ≤ A.budget)))}
  init hm := by
    have h0 := (A.toTPKindAlg true).unitOut.dilate_init_supported () (P := fun w => A.wcnt w = 0)
      A.suppIn_mgInit_wcnt
    rw [(A.toTPKindAlg true).unitOut.dilate_step ()]
    exact (A.toTPKindAlg true).unitOut.uStepD_supported (k := 0) (by omega)
      (P := fun w => A.wcnt w = 0)
      (Q := fun w => w.2 = A.ended ∨ (A.wcnt w = 0 + (if A.kind w.1 then 0 else 1) ∧
        A.wcnt w ≤ A.budget))
      (fun r y x hx hy => A.tp_step_op_eq_zero (k := ⟨0, by omega⟩) hm r y x
        (Or.inr ⟨hx, Nat.zero_le _⟩) hy) h0
  step k hk c b v hv := by
    have hks : k + 1 < A.slots := hk
    set c' := if b then c else c + 1
    have hv' : Supported {d : DReg (A.toTPKindAlg true).unitOut.DW A.width X Y Req Resp |
        MixedAlg.Clean (k + 1) d.workspace.2.2 ∧ (d.workspace.2.1 = true ∨
          (d.workspace.1.2 = A.ended ∨
            (A.wcnt d.workspace.1 = c' ∧ A.wcnt d.workspace.1 ≤ A.budget)))} v := by
      refine Supported.mono hv fun d hd => ?_
      obtain ⟨⟨hc, hh⟩, hkind⟩ := hd
      rw [(A.toTPKindAlg true).unitOut.dilate_kind ()] at hkind
      refine ⟨hc, ?_⟩
      rcases hh with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · by_cases hhalt : d.workspace.2.1 = true
        · exact Or.inl hhalt
        · by_cases hend : d.workspace.1.2 = A.ended
          · exact Or.inr (Or.inl hend)
          · right
            right
            rw [Bool.not_eq_true] at hhalt
            have hb : A.kind d.workspace.1.1 = b := by
              have : ((A.kind d.workspace.1.1 || decide (d.workspace.1.2 = A.ended)) ||
                  d.workspace.2.1) = b := hkind
              rwa [hhalt, Bool.or_false, decide_eq_false hend, Bool.or_false] at this
            subst hb
            refine ⟨?_, h.2⟩
            rw [h.1]
            by_cases hkd : A.kind d.workspace.1.1 = true <;> simp [c', hkd]
    rw [(A.toTPKindAlg true).unitOut.dilate_step ()]
    exact (A.toTPKindAlg true).unitOut.uStepD_supported (k := k + 1)
      (by change k + 1 < A.slots + A.post + 1; omega)
      (P := fun w => w.2 = A.ended ∨ (A.wcnt w = c' ∧ A.wcnt w ≤ A.budget))
      (Q := fun w => w.2 = A.ended ∨ (A.wcnt w = c' + (if A.kind w.1 then 0 else 1) ∧
        A.wcnt w ≤ A.budget))
      (fun r y x hx hy => A.tp_step_op_eq_zero (k := ⟨k + 1, by omega⟩) (c := c') hks r y x
        (by rcases hx with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h.1, h.1 ▸ h.2⟩) hy) hv'
  cap k hk c w hw hkind := by
    obtain ⟨-, hw⟩ := hw
    rw [(A.toTPKindAlg true).unitOut.dilate_kind ()] at hkind
    change ((A.kind w.1.1 || decide (w.1.2 = A.ended)) || w.2.1) = false at hkind
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hkind
    rcases hw with h | h | ⟨h1, h2⟩
    · rw [hkind.2] at h
      exact absurd h Bool.false_ne_true
    · exact absurd h hkind.1.2
    · rw [hkind.1.1] at h1
      simp only [Bool.false_eq_true, ↓reduceIte] at h1
      omega

/-- **The mixed game of the trace-preserving form keeps the trace** against every environment at
every tape: the environment at the tape is that of a challenger with one coin
(`Env.toChallenger`), against which the composition has trace one (`StepsTP.trace_final`). -/
theorem trace_mgRun_toTPKindAlg {freeze : Bool} {Ω St : Type} {Q : ℕ} [OracleState St X Y]
    (E : Env Ω Req Resp X Y Q St) (ω : Ω) : ((A.toTPKindAlg freeze).mgRun E ω true).trace = 1 := by
  have h1 := A.stepsTP_toTPKindAlg.trace_final (E.toChallenger ω)
    (id : (A.toTPKindAlg freeze).CW (E.toChallenger ω) → _) (E.baseOracle ω)
  have h0 : (((A.toTPKindAlg freeze).composeBothOut (E.toChallenger ω) id).final
      (E.baseOracle ω)).trace.re =
      ∑ c, ((E.toChallenger ω).coins c).toReal *
        ((A.toTPKindAlg freeze).mgRun (E.toChallenger ω).toPureEnv
          (E.baseOracle ω, c) true).trace.re := by
    rw [KindAlg.composeBothOut_final, KindAlg.composeBoth_final, KindAlg.trace_withAnc,
      Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
      re_trace_embed ((A.toTPKindAlg freeze).emb_injective _ _ c _)]
  have hs : ∀ f : (E.toChallenger ω).Coins → ℝ, ∑ c, f c = f () := fun f =>
    Fintype.sum_eq_single _ fun x hx => (hx rfl).elim
  have hc : ((E.toChallenger ω).coins ()).toReal = 1 := by
    change ((PMF.pure ()) ()).toReal = 1
    simp
  rw [h1, Complex.one_re, hs, hc, one_mul, (A.toTPKindAlg freeze).mgRun_congr _ E
    (E.toChallenger_answer ω)
    (E.toChallenger_oracle ω)] at h0
  have hpsd := Circuit.posSemidef_run (Equiv.refl _) ((A.toTPKindAlg freeze).mgCirc E ω true)
    (A.toTPKindAlg freeze).mgInitM.posSemidef
  have him := (Complex.nonneg_iff.1 hpsd.trace_nonneg).2
  exact Complex.ext (by rw [Complex.one_re]; exact h0.symm)
    (by rw [Complex.one_im]; exact him.symm)

/-- **The model's law of an event of the composed registers is at most the trace-preserving
form's** (`outLaw_composeBothOut_le`). -/
theorem toOuterMeasure_outLaw_composeBothOut_le {freeze : Bool} (C : Challenger X Y Req Resp)
    (H : X → Y)
    (P : (A.toTPKindAlg freeze).CW C → Prop) :
    ((A.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} ≤
      (((A.toTPKindAlg freeze).composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v} := by
  classical
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun o => ?_
  rcases o with _ | v
  · have hn : (none : Option ((A.toTPKindAlg freeze).CW C)) ∉ {o | ∃ v ∈ o, P v} := by simp
    rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn]
  · by_cases hm : (some v : Option ((A.toTPKindAlg freeze).CW C)) ∈ {o | ∃ v ∈ o, P v}
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]
      exact A.outLaw_composeBothOut_le C id H v
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]

/-- **When the model's mixed game keeps the trace, the two laws agree**: at every coins of
positive weight the mixed game against the challenger has trace 1 (`htr`), so the model's law has
no weight on `none`, is at most the trace-preserving form's at every output
(`outLaw_composeBothOut_le`), and so equals it. -/
theorem toOuterMeasure_outLaw_composeBothOut_eq {freeze : Bool} (C : Challenger X Y Req Resp)
    (H : X → Y)
    (htr : ∀ c, C.coins c ≠ 0 → (A.toKindAlg.mgRun C.toPureEnv (H, c) true).trace = 1)
    (P : (A.toTPKindAlg freeze).CW C → Prop) :
    ((A.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} =
      (((A.toTPKindAlg freeze).composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v} := by
  classical
  have hnone : (A.toKindAlg.composeBothOut C id).outLaw H none = 0 := by
    have h1 : (A.toKindAlg.composeBothOut C id).outLaw H none = (A.compose C).outLaw H none := by
      rw [Alg.outLaw_none, Alg.outLaw_none]
      rfl
    have hsum : ∑ c, (C.coins c).toReal * (A.toKindAlg.mgRun C.toPureEnv (H, c) true).trace.re =
        ∑ c, (C.coins c).toReal := by
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : C.coins c = 0
      · rw [hc, ENNReal.toReal_zero, zero_mul]
      · rw [htr c hc, Complex.one_re, mul_one]
    have hone : ∑ c, (C.coins c).toReal = 1 := by
      have h := PMF.tsum_coe C.coins
      rw [tsum_fintype] at h
      rw [← ENNReal.toReal_sum (fun c _ => PMF.apply_ne_top _ _), h, ENNReal.toReal_one]
    rw [h1, outLaw_compose_none_eq, hsum, hone, sub_self, ENNReal.ofReal_zero]
  have hle : ∀ o, (A.toKindAlg.composeBothOut C id).outLaw H o ≤
      ((A.toTPKindAlg freeze).composeBothOut C id).outLaw H o := by
    rintro (_ | v)
    · rw [hnone]
      exact bot_le
    · exact A.outLaw_composeBothOut_le C id H v
  have hpq : (A.toKindAlg.composeBothOut C id).outLaw H =
      ((A.toTPKindAlg freeze).composeBothOut C id).outLaw H := by
    ext o
    refine le_antisymm (hle o) (not_lt.1 fun hlt => ?_)
    have h := ENNReal.tsum_lt_tsum
      (((A.toKindAlg.composeBothOut C id).outLaw H).tsum_coe ▸ ENNReal.one_ne_top) hle hlt
    rw [PMF.tsum_coe, PMF.tsum_coe] at h
    exact lt_irrefl _ h
  rw [hpq]

/-- **The pure distinguisher of an adversary has a budget of `budget + post` query slots**
(`AdaptiveIAlg.dilTPBudget`, `Distinguisher.Budget.withPostSlots`). -/
noncomputable def pureD_budget : A.pureD.Budget (A.budget + A.post) := by
  rw [pureD_eq]
  exact Distinguisher.Budget.withPostSlots _ _ _ A.dilTPBudget

variable (C : Challenger X Y Req Resp)

/-- **The events of the trace-preserving form's composed registers as events of the pure
distinguisher**: the coin average of the probability, in the final state of the pure distinguisher
against the challenger's environment, of the running branches whose game registers satisfy the
event, placed with the flag of the post slots. The pure distinguisher dilates the frozen
trace-preserving form, which keeps the trace, so the relay sees no halted branch; an ended branch
keeps its registers and sends its request register again. The model's law is at most this one
(`toOuterMeasure_outLaw_composeBothOut_le`), and equal to it when
the model's mixed game keeps the trace (`toOuterMeasure_outLaw_composeBothOut_eq`). -/
theorem toOuterMeasure_outLaw_pureD (H : X → Y) (P : (A.toTPKindAlg true).CW C → Prop) :
    (((A.toTPKindAlg true).composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} =
      ENNReal.ofReal (∑ c, (C.coins c).toReal *
        prob (embR A.post true ''
          (A.toTPKindAlg true).unitOut.dilSet {r | P ((A.toTPKindAlg true).emb C H c A.slots r).1})
          (A.pureD.final C.toPureEnv noPost (H, c))) := by
  classical
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut_id]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have h1 : prob (embR A.post true ''
      (A.toTPKindAlg true).unitOut.dilSet {r | P ((A.toTPKindAlg true).emb C H c A.slots r).1})
      (A.pureD.final C.toPureEnv noPost (H, c)) = ∑ r : (A.toTPKindAlg true).G,
        if r ∈ {r | P ((A.toTPKindAlg true).emb C H c A.slots r).1} then
          ((A.toTPKindAlg true).unitOut.mgRun C.toPureEnv (H, c) false r r).re else 0 := by
    rw [A.final_pureD, prob_embV (embR_injective _ _),
      Set.preimage_image_eq _ (embR_injective _ _)]
    exact KindAlg.prob_final_dilate _ C.toPureEnv () _ (H, c)
  rw [h1]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h2 : ((A.toTPKindAlg true).mgRun C.toPureEnv (H, c) true r r).re =
      ((A.toTPKindAlg true).unitOut.mgRun C.toPureEnv (H, c) false r r).re := by
    rw [KindAlg.mgRun_deph, dephase_apply_self]
    rfl
  split_ifs with h3 h4 h4
  · exact h2
  · exact absurd h3 h4
  · exact absurd h4 h3
  · rfl

/-- **The dilated trace-preserving form has no weight off the running branches**: its mixed game
keeps the trace (`trace_mgRun_toTPKindAlg`). -/
theorem prob_compl_dilSet_univ {freeze : Bool} {Ω St : Type} {Q : ℕ} [OracleState St X Y]
    (E : Env Ω Req Resp X Y Q St) (ω : Ω) :
    prob ((A.toTPKindAlg freeze).unitOut.dilSet Set.univ)ᶜ
      (((A.toTPKindAlg freeze).unitOut.dilate ()).final E
        (A.toTPKindAlg freeze).unitOut.postOp ω) = 0 := by
  classical
  have htr := A.trace_mgRun_toTPKindAlg (freeze := freeze) E ω
  have hn : ‖((A.toTPKindAlg freeze).unitOut.dilate ()).final E
      (A.toTPKindAlg freeze).unitOut.postOp ω‖ = 1 := by
    rw [Distinguisher.final, LinearIsometryEquiv.norm_map, Distinguisher.run, Distinguisher.stage,
      norm_hybrid, Distinguisher.norm_gameInit]
  rw [prob_compl, hn, KindAlg.prob_final_dilate]
  rw [KindAlg.mgRun_deph] at htr
  have h1 : ∑ r : (A.toTPKindAlg freeze).unitOut.G, (if r ∈ (Set.univ : Set (A.toTPKindAlg freeze).unitOut.G) then
      ((A.toTPKindAlg freeze).unitOut.mgRun E ω false r r).re else 0) = 1 := by
    have := congrArg Complex.re htr
    rw [Matrix.trace, Complex.re_sum, Complex.one_re] at this
    simp only [Matrix.diag, dephase_apply_self] at this
    simp only [Set.mem_univ, ↓reduceIte]
    exact this
  rw [h1]
  norm_num

/-! ### The relayed adversary -/

section Relay


variable {Req' Resp' O' Xs Ys : Type} [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)

omit [Inhabited X] in
/-- **The dilated workspace of the trace-preserving form, at a shape**, is finite, as one instance
built in steps: one instance search for it exceeds the default size limit of instance search. The
adversary's instance (`instFintypeRelayDW`) is this one at its shape, so the adversary and its shape
(`AlgShape.relayAdvS`) read the same instance. -/
noncomputable instance _root_.GordieHowe.Quantum.AlgShape.instFintypeRelayDWS
    (s : AlgShape X Y Req Resp) : Fintype s.tpKindS.DW :=
  haveI : Fintype (GameReg s.tpKindS.W s.width X Y Req Resp s.slots × Bool) := inferInstance
  haveI : Fintype (MixedAlg.Anc (GameReg s.tpKindS.W s.width X Y Req Resp s.slots × Bool)
    (s.slots + s.post) (s.tpKindS.R ⊕ Bool) Unit) := inferInstance
  inferInstance

omit [Inhabited X] in
/-- The workspace the relay is built over, at a shape (the dilated workspace with the post flag), is
finite (`AlgShape.instFintypeRelayDWS`). -/
noncomputable instance _root_.GordieHowe.Quantum.AlgShape.instFintypeRelayBaseS
    (s : AlgShape X Y Req Resp) : Fintype (s.tpKindS.DW × Bool) :=
  haveI := s.instFintypeRelayDWS
  inferInstance

omit [Inhabited X] in
/-- **Decidable equality of the workspace the relay is built over, at a shape**, as one instance:
the ancilla's Kraus index has no decidable equality of its own, so it is decided classically, here
only. One instance search over the relay's registers also exceeds the default size limit of
instance search. The adversary's instance (`instDecidableEqRelayBase`) is this one at its shape. -/
noncomputable instance _root_.GordieHowe.Quantum.AlgShape.instDecidableEqRelayBaseS
    (s : AlgShape X Y Req Resp) : DecidableEq (s.tpKindS.DW × Bool) :=
  haveI : DecidableEq (MixedAlg.Anc (GameReg s.tpKindS.W s.width X Y Req Resp s.slots × Bool)
    (s.slots + s.post) (s.tpKindS.R ⊕ Bool) Unit) := Classical.decEq _
  inferInstance

omit [Inhabited X] in
/-- The workspace the relay is built over is finite (`AlgShape.instFintypeRelayBaseS` at `A`'s
shape). -/
noncomputable instance instFintypeRelayBase : Fintype ((A.toTPKindAlg true).unitOut.DW × Bool) :=
  A.toShape.instFintypeRelayBaseS

omit [Inhabited X] in
/-- The dilated workspace of the trace-preserving form is finite (`AlgShape.instFintypeRelayDWS`
at `A`'s shape). -/
noncomputable instance instFintypeRelayDW : Fintype (A.toTPKindAlg true).unitOut.DW :=
  A.toShape.instFintypeRelayDWS

omit [Inhabited X] in
/-- Decidable equality of the workspace the relay is built over
(`AlgShape.instDecidableEqRelayBaseS` at `A`'s shape). -/
noncomputable instance instDecidableEqRelayBase :
    DecidableEq ((A.toTPKindAlg true).unitOut.DW × Bool) :=
  A.toShape.instDecidableEqRelayBaseS

/-- **The query budget of the relayed adversary**: `width · (budget + post)` query slots of the
adversary, split into single queries, and for each of the `Q` answered requests its `qR` oracle
queries and its `qP` pad sub-slots (queries of the fixed point `default`, since every step of the
dilated distinguisher ends in a query). -/
def relayBudget : ℕ := A.width * (A.budget + A.post) + Q * F.qR + Q * F.qP

omit [AddGroup Y] [Nonempty X] [Nonempty Y] [Inhabited X] [Inhabited Req'] [AddGroup Ys] in
variable (Ys) in
/-- **The workspace of the relayed adversary at a shape** `s`, through a relay with `K` main
requests, `qR` oracle queries, `qP` pad sub-slots and `qS` side reads per relayed request: the
relay's workspace (`RelayW`) over the registers of the dilated trace-preserving form with the
post flag, with `Distinguisher.relaySlotsS` slots. -/
@[reducible] def _root_.GordieHowe.Quantum.AlgShape.RelayWS (s : AlgShape X Y Req Resp)
    (K qR qP qS : ℕ) : Type :=
  RelayW (DReg (s.tpKindS.DW × Bool) s.width X Y Req Resp) Req Resp' X Y (s.slots + s.post)
    (Distinguisher.relaySlotsS s.width (s.slots + s.post) K qR qP) (Fin qS → Ys)

/-- The workspace of the relayed distinguisher: the shape's (`AlgShape.RelayWS`). -/
abbrev RelayWS (_ : AdaptiveIAlg shA O) : Type := shA.RelayWS (Resp' := Resp') Ys F.K F.qR F.qP F.qS

/-- **The relayed distinguisher** of an adversary: the relay (`Distinguisher.relay`) of its pure
distinguisher with the budget `budget + post`, answering the first `Q` requests.

Running time: that of `Distinguisher.relay` on the pure distinguisher of `A`. This running time
is argued here, not proved in Lean. -/
@[irreducible, no_expose] noncomputable def relayD :
    Distinguisher (A.RelayWS F) X Y Req' Resp' 1
      (Distinguisher.relaySlotsS shA.width (shA.slots + shA.post) F.K F.qR F.qP) :=
  A.pureD.relay F (A.budget + A.post) Q

omit [Nonempty X] [Nonempty Y] [DecidableEq Ys] in
/-- The relayed distinguisher (`relayD` is sealed). -/
theorem relayD_eq : A.relayD F Q = A.pureD.relay F (A.budget + A.post) Q := by
  unfold relayD; rfl

omit [Nonempty X] [Nonempty Y] [DecidableEq Ys] in
theorem relayD_kind : (A.relayD F Q).kind = (A.pureD.relay F (A.budget + A.post) Q).kind := by
  rw [relayD_eq]

omit [Nonempty X] [Nonempty Y] [DecidableEq Ys] in
theorem relayD_init : (A.relayD F Q).init = (A.pureD.relay F (A.budget + A.post) Q).init := by
  rw [relayD_eq]

omit [Nonempty X] [Nonempty Y] [DecidableEq Ys] in
theorem relayD_step : (A.relayD F Q).step = (A.pureD.relay F (A.budget + A.post) Q).step := by
  rw [relayD_eq]

open Classical in
omit [AddGroup Y] [Nonempty X] [Nonempty Y] [Inhabited X] [Inhabited Req'] [AddGroup Ys] in
variable (Ys) in
/-- **The shape of the relayed adversary** (`relayAdv`) of an adversary of shape `s`, through a
relay with `K` main requests, `qR` oracle queries, `qP` pad sub-slots and `qS` side reads per
relayed request, answering `Q` requests: the aborting completion (`AlgShape.abortS`) of the
shape of a distinguisher (`AlgShape.toAdaptiveS`) whose workspace is the relay's (`RelayW`) over
the registers of the dilated trace-preserving form with the post flag, of width `1`, with
`Distinguisher.relaySlotsS` slots and the budget
`relayBudget`. -/
@[reducible] noncomputable def _root_.GordieHowe.Quantum.AlgShape.relayAdvS (s : AlgShape X Y Req Resp)
    (K qR qP qS Q : ℕ) : AlgShape X Y Req' Resp' :=
  (AlgShape.toAdaptiveS (X := X) (Y := Y) (Req := Req') (Resp := Resp')
    (s.RelayWS (Resp' := Resp') Ys K qR qP qS)
    1 (Distinguisher.relaySlotsS s.width (s.slots + s.post) K qR qP) Nat.one_pos
    (s.width * (s.budget + s.post) + Q * qR + Q * qP)).abortS

/-- **The relayed adversary** of `A` with the output `out'` read from the relay's workspace: the
relayed distinguisher as an adversary with run-time kinds (`Distinguisher.toAdaptive`, width `1`,
budget `relayBudget`), completed to abort over-budget calls (`abortAlg`).

Running time: that of `relayD` (`Distinguisher.relay`), with the query counter of
`Distinguisher.toAdaptive` and the abort on an over-budget call. This running time is argued
here, not proved in Lean. -/
noncomputable def relayAdv (out' : A.RelayWS F → O') :
    AdaptiveIAlg (shA.relayAdvS (Req' := Req') (Resp' := Resp') Ys F.K F.qR F.qP F.qS Q) O' :=
  ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').abortAlg

omit [Nonempty Y] in
/-- **The relayed adversary** as its definition: the aborting completion of the relayed
distinguisher as an adversary with run-time kinds. -/
theorem relayAdv_eq (out' : A.RelayWS F → O') :
    A.relayAdv F Q out' = ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').abortAlg :=
  rfl

variable (out' : A.RelayWS F → O')

/-- **The shape of the relayed adversary** is `AlgShape.relayAdvS` at the relay's numbers. -/
theorem relayAdv_toShape :
    (A.relayAdv F Q out').toShape = A.toShape.relayAdvS Ys F.K F.qR F.qP F.qS Q :=
  rfl

/-- The relayed adversary is trace preserving. -/
theorem relayAdv_tracePreserving : (A.relayAdv F Q out').TracePreserving :=
  tracePreserving_abortAlg _

/-- The relayed adversary stays within its budget. -/
theorem relayAdv_withinBudget : (A.relayAdv F Q out').WithinBudget :=
  withinBudget_abortAlg _

/-- **The queries of the relayed adversary**: `width · (budget + post) + Q · qR + Q · qP`. -/
theorem relayAdv_queries :
    (A.relayAdv F Q out').width * ((A.relayAdv F Q out').budget + (A.relayAdv F Q out').post) =
      A.width * (A.budget + A.post) + Q * F.qR + Q * F.qP := by
  change 1 * (A.relayBudget F Q + 0) = _
  rw [one_mul, add_zero, relayBudget]

/-- **The queries of the relayed adversary for a relay without pad sub-slots**:
`width · (budget + post) + Q · qR`. -/
theorem relayAdv_queries_of_qP (hP : F.qP = 0) :
    (A.relayAdv F Q out').width * ((A.relayAdv F Q out').budget + (A.relayAdv F Q out').post) =
      A.width * (A.budget + A.post) + Q * F.qR := by
  rw [relayAdv_queries, hP, Nat.mul_zero, Nat.add_zero]

/-- **The placement of a basis state of the dilated trace-preserving form's game in the composed
registers of the relayed adversary** against the main challenger `C` at the oracle `H` and the coins `c'`:
the post slots' flag set, the relay's final placement against the main replies and its set-up,
the query counter, the challenger's registers, and the aborting completion's counter. -/
noncomputable def relayPlace (C : Challenger X Y Req' Resp') (H : X → Y) (c' : C.Coins)
    (y : GameReg (A.toTPKindAlg true).unitOut.DW (A.toTPKindAlg true).unitOut.width X Y Req Resp
      (A.toTPKindAlg true).unitOut.slots) : (A.relayAdv F Q out').toKindAlg.CW C :=
  ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').liftCW C
    (((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').toKindAlg.emb C H c'
      (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width ((A.toTPKindAlg true).unitOut.slots + A.post) F)
      (Distinguisher.fMid (A.relayBudget F Q)
        (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width ((A.toTPKindAlg true).unitOut.slots + A.post) F)
        (liftL (Distinguisher.setupPerm F (A.budget + A.post) Q)
          (A.pureD.place F (A.budget + A.post) Q (C.toPureEnv.answerAfter (H, c')) H
            (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width ((A.toTPKindAlg true).unitOut.slots + A.post) F)
            ((A.toTPKindAlg true).unitOut.slots + A.post) (embR A.post true y))))).1

/-- **The relayed distinguisher keeps the budget** at every stage against the main challenger
(`Distinguisher.relay_stage_count` at the pure distinguisher's budget `pureD_budget`). -/
theorem relayD_stage_count (Cout : Challenger X Y Req Resp) (C : Challenger X Y Req' Resp')
    (κ : C.Coins → Cout.Coins) (hF : F.RelaysChallenger Cout C κ) (H : X → Y) (c' : C.Coins)
    (j : ℕ) (hj : j < Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width
      ((A.toTPKindAlg true).unitOut.slots + A.post) F) :
    Supported ((A.relayD F Cout.Q).BudgetAt (A.relayBudget F Cout.Q) j)
      ((A.relayD F Cout.Q).stage C.toPureEnv (H, c') j) := by
  rw [A.relayD_eq]
  exact A.pureD.relay_stage_count F (A.budget + A.post) Cout.Q H C.toPureEnv (H, c') Cout.toPureEnv
    (H, κ c') A.width_pos A.pureD_budget (fun lg => hF.oracle_eq H (κ c') lg)
    (fun lg => hF.oracle_eq' H c' lg) (hF.answer_eq H c') j hj.le

/-- **The multi-request relay, event form** (module docstring). The adversary `A` runs against the
challenger `Cout`, whose replies are those of the relay programs `F` run against the main
challenger `C`: at the oracle `H` and the main coins `c'`, `Cout` at the coins `κ c'` answers
its first `Cout.Q` requests as `F.runReply` against the main replies, the coins of `Cout` are
the image of `C`'s along `κ`, and neither challenger reprograms (`MultiRelay.RelaysChallenger`).
Then every event `P` of `A`'s composed registers has at most the probability of every event `P'`
of the relayed adversary's composed registers against `C` that holds at the placement
(`relayPlace`) of each running branch of the dilated trace-preserving form's game satisfying `P`
(`himp`). -/
theorem toOuterMeasure_le_relayAdv (Cout : Challenger X Y Req Resp) (C : Challenger X Y Req' Resp')
    (κ : C.Coins → Cout.Coins) (hF : F.RelaysChallenger Cout C κ)
    (H : X → Y) (P : A.toKindAlg.CW Cout → Prop)
    (P' : (A.relayAdv F Cout.Q out').toKindAlg.CW C → Prop)
    (himp : ∀ c' y, y ∈ (A.toTPKindAlg true).unitOut.dilSet {r | P (A.toKindAlg.emb Cout H (κ c') A.slots r).1} →
      P' (A.relayPlace F Cout.Q out' C H c' y)) :
    ((A.toKindAlg.composeBothOut Cout id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} ≤
      (((A.relayAdv F Cout.Q out').toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P' v} := by
  classical
  have hn : 0 < (A.toTPKindAlg true).unitOut.width := A.width_pos
  have hB : ∀ c' : C.Coins, ∀ j < Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width
      ((A.toTPKindAlg true).unitOut.slots + A.post) F,
      Supported ((A.relayD F Cout.Q).BudgetAt (A.relayBudget F Cout.Q) j)
        ((A.relayD F Cout.Q).stage C.toPureEnv (H, c') j) := fun c' j hj =>
    A.relayD_stage_count F Cout C κ hF H c' j hj
  have hA := (A.relayD F Cout.Q).toOuterMeasure_outLaw_abortAlg_toAdaptive Nat.one_pos
    (A.relayBudget F Cout.Q) out' C H hB P'
  refine (A.toOuterMeasure_outLaw_composeBothOut_le (freeze := true) Cout H P).trans ?_
  rw [A.toOuterMeasure_outLaw_pureD Cout H P]
  refine le_of_le_of_eq ?_ hA.symm
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hF.coins_eq, sum_toReal_map_mul]
  refine Finset.sum_le_sum fun c' _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  have hfin := A.pureD.prob_final_relay F (A.budget + A.post) Cout.Q H C.toPureEnv (H, c')
    Cout.toPureEnv (H, κ c') hn A.pureD_budget (fun lg => hF.oracle_eq H (κ c') lg)
    (fun lg => hF.oracle_eq' H c' lg) (hF.answer_eq H c')
    {g | P' (((A.relayD F Cout.Q).toAdaptive Nat.one_pos (A.relayBudget F Cout.Q) out').liftCW C
      (((A.relayD F Cout.Q).toAdaptive Nat.one_pos (A.relayBudget F Cout.Q) out').toKindAlg.emb C H c'
        (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width ((A.toTPKindAlg true).unitOut.slots + A.post) F)
        (Distinguisher.fMid (A.relayBudget F Cout.Q)
          (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width ((A.toTPKindAlg true).unitOut.slots + A.post) F)
          g)).1)}
  have hrun : (A.relayD F Cout.Q).run C.toPureEnv (H, c') =
      (A.pureD.relay F (A.budget + A.post) Cout.Q).final C.toPureEnv noPost (H, c') := by
    rw [A.relayD_eq]
    simp only [Distinguisher.final, noPost, logControlled_refl]
  refine le_of_le_of_eq ?_ ((congrArg _ hrun).trans hfin).symm
  refine prob_mono ?_ _
  rintro x ⟨y, hy, rfl⟩
  exact himp c' y hy

/-- **An event of the relayed distinguisher's run against the main challenger** has the
probability, in the final state of the dilated trace-preserving form (`toTPKindAlg`) against the
challenger, of the basis states
whose placement lies in it. -/
theorem prob_run_relayD (Cout : Challenger X Y Req Resp) (C : Challenger X Y Req' Resp')
    (κ : C.Coins → Cout.Coins) (hF : F.RelaysChallenger Cout C κ) (H : X → Y) (c' : C.Coins)
    (S : Set (GameReg (A.RelayWS F) 1 X Y Req' Resp'
      (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width ((A.toTPKindAlg true).unitOut.slots + A.post) F))) :
    prob S ((A.relayD F Cout.Q).run C.toPureEnv (H, c')) =
      prob ((fun y => liftL (Distinguisher.setupPerm F (A.budget + A.post) Cout.Q)
        (A.pureD.place F (A.budget + A.post) Cout.Q (C.toPureEnv.answerAfter (H, c')) H
          (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width ((A.toTPKindAlg true).unitOut.slots + A.post) F)
          ((A.toTPKindAlg true).unitOut.slots + A.post) (embR A.post true y))) ⁻¹' S)
        (((A.toTPKindAlg true).unitOut.dilate ()).final Cout.toPureEnv
            (A.toTPKindAlg true).unitOut.postOp (H, κ c')) := by
  classical
  have hn : 0 < (A.toTPKindAlg true).unitOut.width := A.width_pos
  have hrun : (A.relayD F Cout.Q).run C.toPureEnv (H, c') =
      (A.relayD F Cout.Q).final C.toPureEnv noPost (H, c') := by
    simp only [Distinguisher.final, noPost, logControlled_refl]
  rw [hrun, A.relayD_eq, A.pureD.prob_final_relay F (A.budget + A.post) Cout.Q H C.toPureEnv (H, c')
    Cout.toPureEnv (H, κ c') hn A.pureD_budget (fun lg => hF.oracle_eq H (κ c') lg)
    (fun lg => hF.oracle_eq' H c' lg) (hF.answer_eq H c') S, A.final_pureD,
    prob_embV (embR_injective _ _)]
  rfl

/-- **The multi-request relay, equality form** (module docstring): when the dilated adversary's
mixed game against the challenger has trace 1 at every coins (`htr`; every adversary within its
budget, `WithinBudget.trace_mgRun_eq_one`), an event `P` of its composed registers against `Cout` and an event `P'` of the relayed
adversary's composed registers against `C` that agree at the placement (`relayPlace`) of every
running branch of the dilated trace-preserving form's game (`himp`, `hrev`) have the same
probability. -/
theorem toOuterMeasure_eq_relayAdv (Cout : Challenger X Y Req Resp)
    (C : Challenger X Y Req' Resp') (κ : C.Coins → Cout.Coins) (hF : F.RelaysChallenger Cout C κ)
    (H : X → Y) (htr : ∀ c', (A.toKindAlg.mgRun Cout.toPureEnv (H, κ c') true).trace = 1)
    (P : A.toKindAlg.CW Cout → Prop)
    (P' : (A.relayAdv F Cout.Q out').toKindAlg.CW C → Prop)
    (himp : ∀ c' y, y ∈ (A.toTPKindAlg true).unitOut.dilSet {r | P (A.toKindAlg.emb Cout H (κ c') A.slots r).1} →
      P' (A.relayPlace F Cout.Q out' C H c' y))
    (hrev : ∀ c' y, ((A.toTPKindAlg true).unitOut.relG y).1.2 = false →
      P' (A.relayPlace F Cout.Q out' C H c' y) →
        P (A.toKindAlg.emb Cout H (κ c') A.slots ((A.toTPKindAlg true).unitOut.relG y).1.1).1) :
    ((A.toKindAlg.composeBothOut Cout id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} =
      (((A.relayAdv F Cout.Q out').toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P' v} := by
  classical
  refine le_antisymm (A.toOuterMeasure_le_relayAdv F out' Cout C κ hF H P P' himp) ?_
  have hn : 0 < (A.toTPKindAlg true).unitOut.width := A.width_pos
  have hB : ∀ c' : C.Coins, ∀ j < Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width
      ((A.toTPKindAlg true).unitOut.slots + A.post) F,
      Supported ((A.relayD F Cout.Q).BudgetAt (A.relayBudget F Cout.Q) j)
        ((A.relayD F Cout.Q).stage C.toPureEnv (H, c') j) := fun c' j hj =>
    A.relayD_stage_count F Cout C κ hF H c' j hj
  have hA' := (A.relayD F Cout.Q).toOuterMeasure_outLaw_abortAlg_toAdaptive Nat.one_pos
    (A.relayBudget F Cout.Q) out' C H hB P'
  have htr' : ∀ c, Cout.coins c ≠ 0 →
      (A.toKindAlg.mgRun Cout.toPureEnv (H, c) true).trace = 1 := fun c hc => by
    rw [hF.coins_eq] at hc
    obtain ⟨c', -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ((PMF.mem_support_iff _ _).2 hc)
    exact htr c'
  rw [A.toOuterMeasure_outLaw_composeBothOut_eq (freeze := true) Cout H htr' P,
    A.toOuterMeasure_outLaw_pureD Cout H P]
  refine le_of_eq_of_le hA' ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hF.coins_eq, sum_toReal_map_mul]
  refine Finset.sum_le_sum fun c' _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  refine le_of_eq_of_le (A.prob_run_relayD F Cout C κ hF H c' _) ?_
  rw [A.final_pureD, prob_embV (embR_injective _ _),
    Set.preimage_image_eq _ (embR_injective _ _)]
  set T := (A.toTPKindAlg true).unitOut.dilSet {r | P (A.toKindAlg.emb Cout H (κ c') A.slots r).1}
  set w := ((A.toTPKindAlg true).unitOut.dilate ()).final Cout.toPureEnv
      (A.toTPKindAlg true).unitOut.postOp (H, κ c')
  have hsub : (fun y => liftL (Distinguisher.setupPerm F (A.budget + A.post) Cout.Q)
        (A.pureD.place F (A.budget + A.post) Cout.Q (C.toPureEnv.answerAfter (H, c')) H
          (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width ((A.toTPKindAlg true).unitOut.slots + A.post) F)
          ((A.toTPKindAlg true).unitOut.slots + A.post) (embR A.post true y))) ⁻¹'
        {g | P' (((A.relayD F Cout.Q).toAdaptive Nat.one_pos (A.relayBudget F Cout.Q) out').liftCW C
          (((A.relayD F Cout.Q).toAdaptive Nat.one_pos (A.relayBudget F Cout.Q) out').toKindAlg.emb
            C H c' (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width
              ((A.toTPKindAlg true).unitOut.slots + A.post) F)
            (Distinguisher.fMid (A.relayBudget F Cout.Q)
              (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width
                ((A.toTPKindAlg true).unitOut.slots + A.post) F) g)).1)} ⊆
      T ∪ ((A.toTPKindAlg true).unitOut.dilSet Set.univ)ᶜ := by
    intro y hy
    by_cases hr : y ∈ (A.toTPKindAlg true).unitOut.dilSet Set.univ
    · exact Or.inl ⟨hr.1, hrev c' y hr.1 hy⟩
    · exact Or.inr hr
  calc _ ≤ prob (T ∪ ((A.toTPKindAlg true).unitOut.dilSet Set.univ)ᶜ) w := prob_mono hsub w
    _ ≤ prob T w + prob ((A.toTPKindAlg true).unitOut.dilSet Set.univ)ᶜ w := prob_union_le _ _ _
    _ = prob T w := by rw [A.prob_compl_dilSet_univ _ _, add_zero]

/-! ### Reading the placed registers -/

/-- **The output of the relayed adversary for the transcript**: the adversary's output, read from
its workspace inside the relay's. -/
def relayOut (w : A.RelayWS F) : O := A.out w.inner.1.1.1.1.1

/-- **The relayed adversary outputs the adversary's output** at every placed basis state. -/
theorem output_relayPlace (C : Challenger X Y Req' Resp') (H : X → Y) (c' : C.Coins)
    (y : GameReg (A.toTPKindAlg true).unitOut.DW (A.toTPKindAlg true).unitOut.width X Y Req Resp
      (A.toTPKindAlg true).unitOut.slots) (Cout : Challenger X Y Req Resp) (c : Cout.Coins) :
    (A.relayAdv F Q (A.relayOut F)).output C (A.relayPlace F Q (A.relayOut F) C H c' y) =
      A.output Cout (A.toKindAlg.emb Cout H c A.slots ((A.toTPKindAlg true).unitOut.relG y).1.1).1 := by
  have h := Distinguisher.setupFun_inner_fst F (A.budget + A.post) Q
    ((splitLogs (A.pureD.place F (A.budget + A.post) Q (C.toPureEnv.answerAfter (H, c')) H
      (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width ((A.toTPKindAlg true).unitOut.slots + A.post) F)
      ((A.toTPKindAlg true).unitOut.slots + A.post) (embR A.post true y))).1)
  change A.out (Distinguisher.setupFun F (A.budget + A.post) Q
    ((splitLogs (A.pureD.place F (A.budget + A.post) Q (C.toPureEnv.answerAfter (H, c')) H
      (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width ((A.toTPKindAlg true).unitOut.slots + A.post) F)
      ((A.toTPKindAlg true).unitOut.slots + A.post) (embR A.post true y))).1)).1.1.inner.1.1.1.1.1 = _
  rw [h]
  rfl

/-- **Every request of the relayed adversary's history** at a placed basis state is the idle
request or one that the program of a request of the adversary's history can make. -/
theorem history_relayPlace (Cout : Challenger X Y Req Resp) (c : Cout.Coins)
    (C : Challenger X Y Req' Resp') (H : X → Y) (c' : C.Coins)
    (y : GameReg (A.toTPKindAlg true).unitOut.DW (A.toTPKindAlg true).unitOut.width X Y Req Resp
      (A.toTPKindAlg true).unitOut.slots) :
    ∀ e' ∈ (A.relayAdv F Cout.Q out').history C (A.relayPlace F Cout.Q out' C H c' y),
      e'.request = F.idle ∨ ∃ e ∈ A.history Cout
        (A.toKindAlg.emb Cout H c A.slots ((A.toTPKindAlg true).unitOut.relG y).1.1).1,
        F.CanAsk e.request e'.request := by
  intro e' he'
  have hm := Challenger.map_request_regStateOf C.Q C.respond
    (A.relayPlace F Cout.Q out' C H c' y).chal.coins
    (A.relayPlace F Cout.Q out' C H c' y).chal.logs
    ((A.relayAdv F Cout.Q out').toKindAlg.ansOf C (A.relayPlace F Cout.Q out' C H c' y).chal)
    (A.relayAdv F Cout.Q out').toKindAlg.slots
  have h1 : e'.request ∈ requests (splitLogs (A.pureD.place F (A.budget + A.post) Cout.Q
      (C.toPureEnv.answerAfter (H, c')) H
      (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width ((A.toTPKindAlg true).unitOut.slots + A.post) F)
      ((A.toTPKindAlg true).unitOut.slots + A.post) (embR A.post true y))).2 := by
    have h2 : e'.request ∈ (requestsBefore (A.relayPlace F Cout.Q out' C H c' y).chal.logs
        (A.relayAdv F Cout.Q out').toKindAlg.slots).take C.Q := by
      rw [← hm]
      exact List.mem_map_of_mem he'
    exact List.mem_of_mem_take h2
  rcases A.pureD.origin_place F (A.budget + A.post) Cout.Q (C.toPureEnv.answerAfter (H, c')) H
    (embR A.post true y) h1 with h | ⟨r, hr, hc⟩
  · exact Or.inl h
  · right
    have hlogs : (splitLogs (embR A.post true y)).2 = extLogs A.post (splitLogs y).2 := rfl
    rw [hlogs, requests_extLogs] at hr
    have hA := Challenger.map_request_regStateOf Cout.Q Cout.respond c (splitLogs y).2
      (A.toKindAlg.ansOf Cout
        (A.toKindAlg.emb Cout H c A.slots ((A.toTPKindAlg true).unitOut.relG y).1.1).1.chal) A.slots
    have hr' : r ∈ (A.history Cout
        (A.toKindAlg.emb Cout H c A.slots ((A.toTPKindAlg true).unitOut.relG y).1.1).1).map
          HistoryEntry.request := by
      rw [AdaptiveIAlg.history]
      exact hA ▸ hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr'
    exact ⟨e, he, hc⟩

end Relay

end AdaptiveIAlg

/-- **An event of a composition's output** is the event of the composed registers read through the
output. -/
theorem KindAlg.toOuterMeasure_outLaw_composeBothOut {X Y Req Resp O O' : Type} [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
    [DecidableEq Resp] [Nonempty X] [AddGroup Y] [Nonempty Y] {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O)
    (C : Challenger X Y Req Resp) (f : B.CW C → O') (H : X → Y) (E : O' → Prop) :
    ((B.composeBothOut C f).outLaw H).toOuterMeasure {o | ∃ x ∈ o, E x} =
      ((B.composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, E (f v)} := by
  classical
  rw [Alg.toOuterMeasure_outLaw_eq, Alg.toOuterMeasure_outLaw_eq]
  rfl

namespace QueryBoundedAdversary


variable {X Y Req Resp O Req' Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  [Inhabited X] [Inhabited Req'] {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {t : ℕ}

/-- **The relayed adversary of a `t`-query adversary** (the class `def:adversary`): the relay
(`AdaptiveIAlg.relayAdv`) of each of its algorithms, answering `Q` requests by the programs `F`,
outputting the adversary's output. It makes at most `t + Q · qR + Q · qP` queries on every
branch. -/
noncomputable def relay (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ) :
    QueryBoundedAdversary X Y Req' Resp' O (t + Q * F.qR + Q * F.qP) where
  Aux := 𝒜.Aux
  aux := 𝒜.aux
  sh a := (𝒜.sh a).relayAdvS (Req' := Req') (Resp' := Resp') Ys F.K F.qR F.qP F.qS Q
  alg a := (𝒜.alg a).relayAdv F Q ((𝒜.alg a).relayOut F)
  tracePreserving a := (𝒜.alg a).relayAdv_tracePreserving F Q _
  withinBudget a := (𝒜.alg a).relayAdv_withinBudget F Q _
  queries_le a := by
    rw [(𝒜.alg a).relayAdv_queries]
    have := 𝒜.queries_le a
    omega

/-- **The multi-request relay for transcripts** (module docstring). Against a challenger `Cout`
whose replies are the relay `F` of a main challenger `C` (`MultiRelay.RelaysChallenger`), the
transcript of a `t`-query adversary at the oracle `H` lies in an event `E` with at most the
probability that the transcript of its relayed adversary (at most `t + Cout.Q · qR` queries,
against `C`) lies in `E'`, when `E'` holds of every output with every history `hist'` each of
whose requests is the idle request or one that the program of a request of a history `hist` can
make, if `E` holds of the output with `hist`. -/
theorem transcriptLaw_le_relay (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (Cout : Challenger X Y Req Resp)
    (C : Challenger X Y Req' Resp') (κ : C.Coins → Cout.Coins) (hF : F.RelaysChallenger Cout C κ)
    (H : X → Y) (E : O × List (HistoryEntry Req Resp) → Prop)
    (E' : O × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ (o : O) (hist : List (HistoryEntry Req Resp)) (hist' : List (HistoryEntry Req' Resp')),
      E (o, hist) → (∀ e' ∈ hist', e'.request = F.idle ∨ ∃ e ∈ hist, F.CanAsk e.request e'.request) →
        E' (o, hist')) :
    (𝒜.transcriptLaw Cout H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((𝒜.relay F Cout.Q).transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, E' p} := by
  rw [transcriptLaw, transcriptLaw, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  conv_rhs => rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  refine (𝒜.alg a).toOuterMeasure_le_relayAdv F ((𝒜.alg a).relayOut F) Cout C κ hF H _ _ ?_
  intro c' y hy
  have ho := (𝒜.alg a).output_relayPlace F Cout.Q C H c' y Cout (κ c')
  have hh := (𝒜.alg a).history_relayPlace F ((𝒜.alg a).relayOut F) Cout (κ c') C H c' y
  have h := himp _ _ _ hy.2 hh
  rw [← ho] at h
  exact h

/-- **A larger query bound**: a `t`-query adversary is a `t'`-query adversary for `t ≤ t'`. -/
def mono (𝒜 : QueryBoundedAdversary X Y Req Resp O t) {t' : ℕ} (h : t ≤ t') :
    QueryBoundedAdversary X Y Req Resp O t' where
  Aux := 𝒜.Aux
  aux := 𝒜.aux
  sh := 𝒜.sh
  alg := 𝒜.alg
  tracePreserving := 𝒜.tracePreserving
  withinBudget := 𝒜.withinBudget
  queries_le a := (𝒜.queries_le a).trans h

/-- A larger query bound keeps the transcript law. -/
theorem transcriptLaw_mono (𝒜 : QueryBoundedAdversary X Y Req Resp O t) {t' : ℕ} (h : t ≤ t')
    (C : Challenger X Y Req Resp) (H : X → Y) : (𝒜.mono h).transcriptLaw C H = 𝒜.transcriptLaw C H :=
  rfl

end QueryBoundedAdversary

end GordieHowe.Quantum

namespace GordieHowe.RingSignature.GameAdversary

open GordieHowe.Quantum Classical

variable {X Y Req Resp O Req' Resp' In : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  [Inhabited X] [Inhabited Req'] {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {t : ℕ}

/-- **The relayed game adversary**: on each start input `inp`, the relay
(`QueryBoundedAdversary.relay`) of `A inp` by the programs `F inp`, answering `Q` requests, each
with at most `qR` oracle queries and `qP` pad sub-slots. It makes at most `t + Q · qR + Q · qP`
queries on every branch. -/
noncomputable def relay (A : GameAdversary X Y Req Resp In O t)
    (F : In → MultiRelay X Y Req Resp Req' Resp' Xs Ys) (qR : ℕ)
    (hF : ∀ inp, (F inp).qR ≤ qR) (qP : ℕ) (hP : ∀ inp, (F inp).qP ≤ qP) (Q : ℕ) :
    GameAdversary X Y Req' Resp' In O (t + Q * qR + Q * qP) := fun inp =>
  ((A inp).relay (F inp) Q).mono (Nat.add_le_add (Nat.add_le_add_left
    (Nat.mul_le_mul_left Q (hF inp)) t) (Nat.mul_le_mul_left Q (hP inp)))

/-- **The multi-request relay for game adversaries** (module docstring): on every start input
`inp` whose challenger `Cout` relays a main challenger `C` by the programs `F inp`
(`MultiRelay.RelaysChallenger`), the transcript of `A inp` lies in `E` with at most the
probability that the transcript of the relayed adversary lies in `E'`, under the condition of
`QueryBoundedAdversary.transcriptLaw_le_relay`. -/
theorem transcriptLaw_le_relay (A : GameAdversary X Y Req Resp In O t)
    (F : In → MultiRelay X Y Req Resp Req' Resp' Xs Ys) (qR : ℕ)
    (hF : ∀ inp, (F inp).qR ≤ qR) (qP : ℕ) (hP : ∀ inp, (F inp).qP ≤ qP)
    (inp : In) (Cout : Challenger X Y Req Resp) (C : Challenger X Y Req' Resp')
    (κ : C.Coins → Cout.Coins) (hFC : (F inp).RelaysChallenger Cout C κ) (H : X → Y)
    (E : O × List (HistoryEntry Req Resp) → Prop) (E' : O × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ (o : O) (hist : List (HistoryEntry Req Resp)) (hist' : List (HistoryEntry Req' Resp')),
      E (o, hist) → (∀ e' ∈ hist', e'.request = (F inp).idle ∨
        ∃ e ∈ hist, (F inp).CanAsk e.request e'.request) → E' (o, hist')) :
    ((A inp).transcriptLaw Cout H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((A.relay F qR hF qP hP Cout.Q inp).transcriptLaw C H).toOuterMeasure
        {x | ∃ p ∈ x, E' p} :=
  (A inp).transcriptLaw_le_relay (F inp) Cout C κ hFC H E E' himp

end GordieHowe.RingSignature.GameAdversary
