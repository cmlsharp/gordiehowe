-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.MultiRelay

@[expose] public section

/-!
# The multi-request relay for transcripts, positional form

`QueryBoundedAdversary.transcriptLaw_le_relay` (`MultiRelay.lean`) relates the adversary's history
`hist` against `Cout` and the relayed adversary's history `hist'` against `C` by membership only.
This file states both histories as explicit functions of the adversary's requests and the coins.

- `histAlong ans rs`: the history along the requests `rs` with the replies `ans`, each request
  answered by `ans` after the requests before it (`map_request_histAlong`,
  `histAlong_append_singleton`). `Challenger.hist_stateAfter`: a challenger's history after the
  requests `rs` is `histAlong` of its replies (`toPureEnv.answerAfter`) along `rs.take Q`.
  `KindAlg.history_stateAt_emb`: the same for the history read from the placed game registers.
- `exists_of_mem_histAlong`, `histAlong_prefix`: an entry of `histAlong ans rs` is a request of
  `rs` with its reply after the requests before it; the history along a prefix is a prefix.
- `MultiRelay.filterMap_tailEntries`, `MultiRelay.mainReqs_eq_take`, `MultiRelay.mainReqs_prefix`:
  trailing idle sub-slots ask idle requests; the main requests of `rs` are those of `rs.take Q`,
  then idle requests; those of a prefix are a prefix.
  `Distinguisher.requests_place`: within the budget, the main requests in the logs of the final
  placement are the main requests of the requests in the logs, then idle requests.
- `prob_le_of_supported`: an event of a vector supported in `B` is bounded by every event
  containing its part in `B`.
- `AdaptiveIAlg.toOuterMeasure_le_relayAdv_budget`,
  `AdaptiveIAlg.toOuterMeasure_eq_relayAdv_budget`:
  `toOuterMeasure_le_relayAdv` and `toOuterMeasure_eq_relayAdv`, with `himp` (and `hrev`) needed
  only at the running branches within the budget `budget + post`.
  `AdaptiveIAlg.history_relayPlace_eq`, `AdaptiveIAlg.history_emb_relG`: the two histories at a
  placement, positionally.
- `QueryBoundedAdversary.transcriptLaw_le_relay_pos` (**the relay for transcripts, positional
  form**) and `RingSignature.GameAdversary.transcriptLaw_le_relay_pos`: at the main coins `c'`,
  `hist = histAlong (Cout.toPureEnv.answerAfter (H, κ c')) rs` for the requests `rs` (at most
  `Cout.Q`), and `hist' = histAlong (C.toPureEnv.answerAfter (H, c')) ((F.mainReqs Cout.Q
  (C.toPureEnv.answerAfter (H, c')) H rs ++ List.replicate k F.idle).take C.Q)` for some `k`: the
  relayed adversary's requests are the main requests of `rs`, then idle requests (the relay of the
  requests numbered `Cout.Q` or later, and the trailing sub-slots), cut at `C.Q`.
-/

open Finset Matrix
open scoped BigOperators ENNReal ComplexOrder

namespace GordieHowe.Quantum

/-- **The history along the requests `rs`** with the replies `ans`: each request with its reply
`ans` after the requests before it. -/
def histAlong {Req Resp : Type} (ans : List Req → Req → Option Resp) (rs : List Req) :
    List (HistoryEntry Req Resp) :=
  rs.foldl (fun h r => h ++ [⟨r, ans (h.map HistoryEntry.request) r⟩]) []

section HistAlong

variable {Req Resp : Type} (ans : List Req → Req → Option Resp)

private theorem foldl_histAlong (rs : List Req) :
    ∀ h : List (HistoryEntry Req Resp),
      ((rs.foldl (fun h r => h ++ [⟨r, ans (h.map HistoryEntry.request) r⟩]) h).map
        HistoryEntry.request) = h.map HistoryEntry.request ++ rs := by
  induction rs with
  | nil => simp
  | cons r rs ih => intro h; rw [List.foldl_cons, ih]; simp

/-- The requests of the history along `rs` are `rs`. -/
theorem map_request_histAlong (rs : List Req) :
    (histAlong ans rs).map HistoryEntry.request = rs := by
  rw [histAlong, foldl_histAlong]
  rfl

theorem histAlong_append_singleton (rs : List Req) (r : Req) :
    histAlong ans (rs ++ [r]) = histAlong ans rs ++ [⟨r, ans rs r⟩] := by
  conv_lhs => rw [histAlong, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [← histAlong, map_request_histAlong]

/-- **An entry of the history along `rs`** is a request of `rs` with its reply after the
requests before it. -/
theorem exists_of_mem_histAlong
    (rs : List Req) (e : HistoryEntry Req Resp) (he : e ∈ histAlong ans rs) :
    ∃ pre r, pre ++ [r] <+: rs ∧ e = ⟨r, ans pre r⟩ := by
  induction rs using List.reverseRecOn with
  | nil => simp [histAlong] at he
  | append_singleton rs r ih =>
    rw [histAlong_append_singleton, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · obtain ⟨pre, r', hp, rfl⟩ := ih he
      exact ⟨pre, r', hp.trans (List.prefix_append _ _), rfl⟩
    · exact ⟨rs, r, List.prefix_refl _, rfl⟩

/-- **The history along a prefix is a prefix of the history.** -/
theorem histAlong_prefix {rs rs' : List Req} (h : rs <+: rs') :
    histAlong ans rs <+: histAlong ans rs' := by
  obtain ⟨t, rfl⟩ := h
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t r ih =>
    rw [← List.append_assoc, histAlong_append_singleton]
    exact ih.trans (List.prefix_append _ _)

end HistAlong

namespace Challenger

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (C : Challenger X Y Req Resp)

/-- **The history of a challenger after the requests `rs`** is the history along its first `Q`
requests with its replies. -/
theorem hist_stateAfter (H : X → Y) (c : C.Coins) (rs : List Req) :
    (C.stateAfter H c rs).hist = histAlong (C.toPureEnv.answerAfter (H, c)) (rs.take C.Q) := by
  induction rs using List.reverseRecOn with
  | nil => simp [stateAfter, Env.oracleIn_nil, Challenger.toPureEnv, histAlong]
  | append_singleton rs r ih =>
    rw [stateAfter, Env.oracleIn_append_singleton, Env.update]
    simp only [stateAfter] at ih
    split_ifs with h
    · have h' : rs.length < C.Q := h
      rw [toPureEnv_respond_state]
      simp only
      rw [List.take_of_length_le (by simp; omega), histAlong_append_singleton,
        ← List.take_of_length_le h'.le, ← ih, List.take_of_length_le h'.le]
      simp only [Env.answerAfter, h', ↓reduceDIte]
      rfl
    · rw [ih, List.take_append_of_le_length (by omega)]

end Challenger

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O) (C : Challenger X Y Req Resp)

/-- **The history at the placed game registers** (`emb`) after all slots is the history along the
first `Q` logged requests with the challenger's replies at the oracle and the coins. -/
theorem history_stateAt_emb (H : X → Y) (c : C.Coins) (r : A.G) :
    (A.stateAt C (A.emb C H c A.slots r).1.chal A.slots).history =
      histAlong (C.toPureEnv.answerAfter (H, c)) ((requests (splitLogs r).2).take C.Q) := by
  change (C.regState c (splitLogs r).2
    (A.ansOf C ⟨(splitLogs r).2, A.garFill C H c (splitLogs r).2 A.slots, c⟩) A.slots).history = _
  rw [A.regState_eq C H c _ A.slots le_rfl]
  exact C.hist_stateAfter H c _

end KindAlg

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] (n b Q : ℕ) (ansM : List Req' → Req' → Option
      Resp') (H : X → Y)

omit [Inhabited Req'] [Zero Ys] in
/-- The main requests of trailing idle sub-slots are idle requests. -/
theorem filterMap_tailEntries (out : List (Option Req' × (Option Resp' × (X × Y)))) :
    ∀ k, (F.tailEntries ansM out k).filterMap Prod.fst =
      out.filterMap Prod.fst ++ List.replicate k F.idle
  | 0 => by simp [tailEntries]
  | k + 1 => by
    rw [tailEntries, List.filterMap_append, filterMap_tailEntries out k, List.replicate_succ',
      List.append_assoc]
    rfl

/-- **The main requests of the requests `rs`** are those of its first `Q`, then idle requests. -/
theorem mainReqs_eq_take (rs : List Req) :
    F.mainReqs Q ansM H rs =
      F.mainReqs Q ansM H (rs.take Q) ++ List.replicate (rs.length - Q) F.idle := by
  induction rs using List.reverseRecOn with
  | nil => simp
  | append_singleton rs r ih =>
    rw [F.mainReqs_append]
    split_ifs with h
    · rw [List.take_of_length_le (by simp; omega), F.mainReqs_append]
      simp only [h, ↓reduceIte, List.length_append, List.length_singleton]
      rw [show rs.length + 1 - Q = 0 by omega, List.replicate_zero, List.append_nil]
    · rw [ih, List.take_append_of_le_length (by omega), List.append_assoc,
        List.length_append, List.length_singleton, show rs.length + 1 - Q = rs.length - Q + 1 by
          omega, List.replicate_succ']


/-- **The main requests of a prefix are a prefix of the main requests.** -/
theorem mainReqs_prefix {rs rs' : List Req} (h : rs <+: rs') :
    F.mainReqs Q ansM H rs <+: F.mainReqs Q ansM H rs' := by
  obtain ⟨l, rfl⟩ := h
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l r ih =>
    rw [← List.append_assoc, F.mainReqs_append]
    split_ifs <;> exact ih.trans (List.prefix_append _ _)

/-- **After a run of its program, the relay pads with idle requests up to `K` main requests**: after
the run's sub-slots and `k` more, the main requests are the run's followed by `min k (K - a)` idle
requests, `a` the run's number of main requests. -/
theorem filterMap_runAux_add_progRun {r : Req} {rs : List Req'} {res : Option Resp}
    (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res) (hK : (asksOf S.acts).length ≤ F.K)
    (hq : ((qryOf S.acts).filter Sum.isLeft).length ≤ F.qR)
    (hs : ((qryOf S.acts).filter Sum.isRight).length ≤ F.qS) (hp : padOf S.acts ≤ F.qP) :
    ∀ k, (F.runAux ansM H r rs (padOf S.acts + nsOf S.acts + k)).2.filterMap Prod.fst =
        asksOf S.acts ++ List.replicate (min k (F.K - (asksOf S.acts).length)) F.idle ∧
      (F.runAux ansM H r rs (padOf S.acts + nsOf S.acts + k)).1.na =
        (asksOf S.acts).length + min k (F.K - (asksOf S.acts).length)
  | 0 => by
    obtain ⟨h1, h2⟩ := F.runAux_end_progRun S hK hq hs hp
    simp only [Nat.add_zero]
    rw [h2, h1]
    simp [runSt]
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := filterMap_runAux_add_progRun S hK hq hs hp k
    obtain ⟨h1, h2⟩ := F.runAux_add_progRun S hK hq hs hp k
    have hpa : F.progAct r (F.runAux ansM H r rs (padOf S.acts + nsOf S.acts + k)).1 = none := by
      simp only [progAct, h2, ↓reduceIte, h1, S.after_fed]
    rw [← Nat.add_assoc]
    simp only [runAux, act, hpa, next]
    have hc : ∀ st : RelaySt Y Resp' Ys, st.ans = S.fed → F.close F.sideSa r st = st :=
      fun st ha => F.close_of_ans_fed S _ st ha
    by_cases hlt : (F.runAux ansM H r rs (padOf S.acts + nsOf S.acts + k)).1.na < F.K
    · simp only [hlt, ↓reduceIte, List.filterMap_append, ih1]
      rw [hc]
      · have hm : min (k + 1) (F.K - (asksOf S.acts).length) =
            min k (F.K - (asksOf S.acts).length) + 1 := by omega
        refine ⟨?_, by rw [ih2, hm]; ring⟩
        rw [hm, List.replicate_succ', List.append_assoc]
        rfl
      · exact h1
    · simp only [hlt, ↓reduceIte, List.filterMap_append, ih1]
      rw [hc]
      · have hm : min (k + 1) (F.K - (asksOf S.acts).length) =
            min k (F.K - (asksOf S.acts).length) := by omega
        refine ⟨?_, by rw [ih2, hm]⟩
        rw [hm]
        simp
      · exact h1

/-- **The main requests of a relayed request whose program runs within the budgets** (oracle
queries answered by `H`, side reads by the side function): the run's main requests, then idle
requests up to `K`. -/
theorem filterMap_runEntries_of_progRun {r : Req} {rs : List Req'} {res : Option Resp}
    (S : ProgRun ansM (sideOracle H F.side) rs (F.prog r) res) (hK : (asksOf S.acts).length ≤ F.K)
    (hq : ((qryOf S.acts).filter Sum.isLeft).length ≤ F.qR)
    (hs : ((qryOf S.acts).filter Sum.isRight).length ≤ F.qS) (hp : padOf S.acts ≤ F.qP) :
    (F.runEntries ansM H r rs).filterMap Prod.fst =
      asksOf S.acts ++ List.replicate (F.K - (asksOf S.acts).length) F.idle := by
  have hT : padOf S.acts + nsOf S.acts ≤ F.len := by
    rw [nsOf_eq, len]
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hT
  have hkK : F.K - (asksOf S.acts).length ≤ k := by
    have := nsOf_eq S.acts
    simp only [len] at hk
    omega
  obtain ⟨h1, -⟩ := F.filterMap_runAux_add_progRun ansM H S hK hq hs hp k
  rw [runEntries, hk, h1, min_eq_right hkK]

/-- **The main requests of a relayed request whose side-read-free program runs within the
budgets**: the run's main requests, then idle requests up to `K`. -/
theorem filterMap_runEntries_of_runsWith {r : Req}
    {p : Req → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Option Resp)} (hp : F.prog = plainProg p)
    {rs : List Req'} {res : Option Resp}
    {asks : List Req'} {q : ℕ} (h : RunsWith ansM H rs (p r) res asks q)
    (hK : asks.length ≤ F.K) (hq : q ≤ F.qR) :
    (F.runEntries ansM H r rs).filterMap Prod.fst =
      asks ++ List.replicate (F.K - asks.length) F.idle := by
  obtain ⟨S, hS1, hS2⟩ := h
  have hacts := ProgRun.acts_cast (p' := F.prog r) rfl (by rw [hp]; rfl) (S.plain F.side)
  rw [F.filterMap_runEntries_of_progRun ansM H ((S.plain F.side).cast (p' := F.prog r) rfl
      (by rw [hp]; rfl)) ?_ ?_ ?_ ?_, hacts]
  · change asksOf (S.acts.map _) ++ List.replicate (F.K - (asksOf (S.acts.map _)).length) _ = _
    rw [asksOf_map_inl, hS1]
  · rw [hacts]
    exact (asksOf_map_inl _).trans hS1 ▸ hK
  · rw [hacts]
    change ((qryOf (S.acts.map _)).filter Sum.isLeft).length ≤ _
    rw [qryOf_map_inl, List.filter_map, List.length_map]
    exact le_trans (List.length_filter_le _ _) (hS2.trans hq)
  · rw [hacts]
    change ((qryOf (S.acts.map _)).filter Sum.isRight).length ≤ _
    rw [qryOf_map_inl, List.filter_map]
    simp [Function.comp_def]
  · rw [hacts]
    change padOf (S.acts.map _) ≤ _
    rcases S.acts with _ | ⟨x | r', l⟩ <;> simp [padOf]

end MultiRelay

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (D : Distinguisher W X Y Req Resp n m) (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)
      (ansM : List Req' → Req' → Option Resp')
  (H : X → Y)

/-- **The main requests in the logs of the final placement** of a basis state `g` within the budget
`b`: the main requests (`MultiRelay.mainReqs`) of the requests in `g`'s logs, then idle
requests. -/
theorem requests_place (g : GameReg W n X Y Req Resp m)
    (hg : MultiRelay.NoIdleQ b (D.stEntries m g.1)) :
    ∃ k, requests (splitLogs (D.place F b Q ansM H (relaySlots n m F) m g)).2 =
      F.mainReqs Q ansM H (requests (splitLogs g).2) ++ List.replicate k F.idle := by
  have hl : (splitLogs (D.place F b Q ansM H (relaySlots n m F) m g)).2 =
      fun t : Fin (relaySlots n m F) =>
        ((D.subEntries F b Q ansM H (relaySlots n m F) m g.1).getD t blankEntry).1 := by
    simp only [place, Equiv.apply_symm_apply]
  rw [hl, requests, requestsBefore_ofList _ _ rfl _ le_rfl,
    List.take_of_length_le (D.length_subEntries F b Q H ansM _ m g.1).le]
  set out := (F.sched n b Q ansM H (D.stEntries m g.1)).out with hout
  have hle : out.length ≤ relaySlots n m F := by
    rw [hout, F.length_sched, D.length_stEntries le_rfl]
    simp only [lt_irrefl, ↓reduceIte]
    exact F.startAt_le n b Q _ m
  refine ⟨relaySlots n m F - out.length, ?_⟩
  unfold subEntries MultiRelay.subEntriesL
  rw [← hout]
  conv_lhs => rw [show relaySlots n m F = out.length + (relaySlots n m F - out.length) by omega]
  rw [F.take_tailEntries ansM out (i := relaySlots n m F - out.length)
      (k := out.length + (relaySlots n m F - out.length)) (by omega), F.filterMap_tailEntries, hout,
    F.filterMap_sched n b Q ansM H _ hg, requests, requestsBefore_eq_logEntries _ m le_rfl,
    D.stEntries_self]
  rfl

end Distinguisher

/-- **An event of a vector supported in `B`** has at most the probability of every event
containing its part in `B`. -/
theorem prob_le_of_supported {ι : Type*} [Fintype ι] {B S T : Set ι} {v : QState ι}
    (hv : Supported B v) (h : ∀ x ∈ S, x ∈ B → x ∈ T) : prob S v ≤ prob T v := by
  refine (prob_mono (T := T ∪ Bᶜ) (fun x hx => ?_) v).trans ((prob_union_le T Bᶜ v).trans ?_)
  · by_cases hb : x ∈ B
    · exact Or.inl (h x hx hb)
    · exact Or.inr hb
  · rw [hv.prob_eq_zero (C := Bᶜ) (fun r hr => hr), add_zero]

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) [AddGroup Y] [Nonempty X] [Nonempty Y]

section Relay

open Classical

variable {Req' Resp' O' Xs Ys : Type} [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (out' : A.RelayWS F → O')

/-- **The multi-request relay, event form within the budget**: `toOuterMeasure_le_relayAdv`, with
`himp` needed only at the running branches whose pure distinguisher's logs hold at most
`budget + post` query slots. -/
theorem toOuterMeasure_le_relayAdv_budget (Cout : Challenger X Y Req Resp)
    (C : Challenger X Y Req' Resp') (κ : C.Coins → Cout.Coins) (hF : F.RelaysChallenger Cout C κ)
    (H : X → Y) (P : A.toKindAlg.CW Cout → Prop)
    (P' : (A.relayAdv F Cout.Q out').toKindAlg.CW C → Prop)
    (himp : ∀ c' y, y ∈ (A.toTPKindAlg true).unitOut.dilSet {r | P (A.toKindAlg.emb Cout H (κ c') A.slots r).1} →
      queriesBefore (embR A.post true y).1.2.2.2 ((A.toTPKindAlg true).unitOut.slots + A.post) ≤
        A.budget + A.post →
      P' (A.relayPlace F Cout.Q out' C H c' y)) :
    ((A.toKindAlg.composeBothOut Cout id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} ≤
      (((A.relayAdv F Cout.Q out').toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P' v} := by
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
  have hsupp : Supported {r | queriesBefore r.1.2.2.2 ((A.toTPKindAlg true).unitOut.slots + A.post) ≤
      A.budget + A.post} (A.pureD.final Cout.toPureEnv noPost (H, κ c')) := by
    simp only [Distinguisher.final, noPost, logControlled_refl]
    exact A.pureD.stage_supported_last (A.budget + A.post) Cout.Q Cout.toPureEnv (H, κ c')
      A.pureD_budget
  refine le_of_le_of_eq ?_ ((congrArg _ hrun).trans hfin).symm
  refine prob_le_of_supported hsupp ?_
  rintro x ⟨y, hy, rfl⟩ hb
  exact himp c' y hy hb

/-- **The multi-request relay, equality form within the budget**: `toOuterMeasure_eq_relayAdv`,
with `himp` and `hrev` needed only at the running branches whose pure distinguisher's logs hold
at most `budget + post` query slots. -/
theorem toOuterMeasure_eq_relayAdv_budget (Cout : Challenger X Y Req Resp)
    (C : Challenger X Y Req' Resp') (κ : C.Coins → Cout.Coins) (hF : F.RelaysChallenger Cout C κ)
    (H : X → Y) (htr : ∀ c', (A.toKindAlg.mgRun Cout.toPureEnv (H, κ c') true).trace = 1)
    (P : A.toKindAlg.CW Cout → Prop)
    (P' : (A.relayAdv F Cout.Q out').toKindAlg.CW C → Prop)
    (himp : ∀ c' y,
      y ∈ (A.toTPKindAlg true).unitOut.dilSet {r | P (A.toKindAlg.emb Cout H (κ c') A.slots r).1} →
      queriesBefore (embR A.post true y).1.2.2.2 ((A.toTPKindAlg true).unitOut.slots + A.post) ≤
        A.budget + A.post →
      P' (A.relayPlace F Cout.Q out' C H c' y))
    (hrev : ∀ c' y, ((A.toTPKindAlg true).unitOut.relG y).1.2 = false →
      queriesBefore (embR A.post true y).1.2.2.2 ((A.toTPKindAlg true).unitOut.slots + A.post) ≤
        A.budget + A.post →
      P' (A.relayPlace F Cout.Q out' C H c' y) →
        P (A.toKindAlg.emb Cout H (κ c') A.slots ((A.toTPKindAlg true).unitOut.relG y).1.1).1) :
    ((A.toKindAlg.composeBothOut Cout id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} =
      (((A.relayAdv F Cout.Q out').toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P' v} := by
  classical
  refine le_antisymm (A.toOuterMeasure_le_relayAdv_budget F out' Cout C κ hF H P P' himp) ?_
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
  set w := ((A.toTPKindAlg true).unitOut.dilate ()).final Cout.toPureEnv (A.toTPKindAlg true).unitOut.postOp (H, κ c')
  set Bad := {y : GameReg (A.toTPKindAlg true).unitOut.DW (A.toTPKindAlg true).unitOut.width X Y Req Resp
      (A.toTPKindAlg true).unitOut.slots | ¬ queriesBefore (embR A.post true y).1.2.2.2
        ((A.toTPKindAlg true).unitOut.slots + A.post) ≤ A.budget + A.post}
  have hbad : prob Bad w = 0 := by
    have hsupp : Supported {r | queriesBefore r.1.2.2.2 ((A.toTPKindAlg true).unitOut.slots + A.post) ≤
        A.budget + A.post} (A.pureD.final Cout.toPureEnv noPost (H, κ c')) := by
      simp only [Distinguisher.final, noPost, logControlled_refl]
      exact A.pureD.stage_supported_last (A.budget + A.post) Cout.Q Cout.toPureEnv (H, κ c')
        A.pureD_budget
    have h0 := hsupp.prob_eq_zero (C := {r : GameReg _ _ X Y Req Resp _ | ¬ queriesBefore
      r.1.2.2.2 ((A.toTPKindAlg true).unitOut.slots + A.post) ≤ A.budget + A.post}) (fun r hr => hr)
    rw [A.final_pureD, prob_embV (embR_injective _ _)] at h0
    exact h0
  have hsub : (fun y => liftL (Distinguisher.setupPerm F (A.budget + A.post) Cout.Q)
        (A.pureD.place F (A.budget + A.post) Cout.Q (C.toPureEnv.answerAfter (H, c')) H
          (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width
            ((A.toTPKindAlg true).unitOut.slots + A.post) F)
          ((A.toTPKindAlg true).unitOut.slots + A.post) (embR A.post true y))) ⁻¹'
        {g | P' (((A.relayD F Cout.Q).toAdaptive Nat.one_pos (A.relayBudget F Cout.Q) out').liftCW C
          (((A.relayD F Cout.Q).toAdaptive Nat.one_pos (A.relayBudget F Cout.Q) out').toKindAlg.emb
            C H c' (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width
              ((A.toTPKindAlg true).unitOut.slots + A.post) F)
            (Distinguisher.fMid (A.relayBudget F Cout.Q)
              (Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width
                ((A.toTPKindAlg true).unitOut.slots + A.post) F) g)).1)} ⊆
      (T ∪ ((A.toTPKindAlg true).unitOut.dilSet Set.univ)ᶜ) ∪ Bad := by
    intro y hy
    by_cases hb : queriesBefore (embR A.post true y).1.2.2.2 ((A.toTPKindAlg true).unitOut.slots + A.post) ≤
        A.budget + A.post
    · by_cases hr : y ∈ (A.toTPKindAlg true).unitOut.dilSet Set.univ
      · exact Or.inl (Or.inl ⟨hr.1, hrev c' y hr.1 hb hy⟩)
      · exact Or.inl (Or.inr hr)
    · exact Or.inr hb
  calc _ ≤ prob ((T ∪ ((A.toTPKindAlg true).unitOut.dilSet Set.univ)ᶜ) ∪ Bad) w := prob_mono hsub w
    _ ≤ prob (T ∪ ((A.toTPKindAlg true).unitOut.dilSet Set.univ)ᶜ) w + prob Bad w := prob_union_le _ _ _
    _ ≤ prob T w + prob ((A.toTPKindAlg true).unitOut.dilSet Set.univ)ᶜ w + prob Bad w :=
        add_le_add (prob_union_le _ _ _) le_rfl
    _ = prob T w := by rw [A.prob_compl_dilSet_univ _ _, hbad, add_zero, add_zero]

/-- **The relayed adversary's history at a placed basis state within the budget**, positionally:
the history, with the main challenger's replies at the oracle `H` and the coins `c'`, along the
first `C.Q` of the main requests (`MultiRelay.mainReqs`) of the first `Cout.Q` requests of the
adversary's logs, followed by `k` idle requests. -/
theorem history_relayPlace_eq (Cout : Challenger X Y Req Resp) (C : Challenger X Y Req' Resp')
    (H : X → Y) (c' : C.Coins)
    (y : GameReg (A.toTPKindAlg true).unitOut.DW (A.toTPKindAlg true).unitOut.width X Y Req Resp
      (A.toTPKindAlg true).unitOut.slots)
    (hb : queriesBefore (embR A.post true y).1.2.2.2 ((A.toTPKindAlg true).unitOut.slots + A.post) ≤
      A.budget + A.post) :
    ∃ k, (A.relayAdv F Cout.Q out').history C (A.relayPlace F Cout.Q out' C H c' y) =
      histAlong (C.toPureEnv.answerAfter (H, c'))
        ((F.mainReqs Cout.Q (C.toPureEnv.answerAfter (H, c')) H
          ((requests (splitLogs y).2).take Cout.Q) ++ List.replicate k F.idle).take C.Q) := by
  have hg := A.pureD.noIdleQ_of_count (A.budget + A.post) le_rfl (embR A.post true y).1 hb
    (fun h => absurd h (lt_irrefl _))
  obtain ⟨k, hk⟩ := A.pureD.requests_place F (A.budget + A.post) Cout.Q
    (C.toPureEnv.answerAfter (H, c')) H (embR A.post true y) hg
  have hlogs : (splitLogs (embR A.post true y)).2 = extLogs A.post (splitLogs y).2 := rfl
  rw [hlogs, requests_extLogs, F.mainReqs_eq_take, List.append_assoc, ← List.replicate_add] at hk
  refine ⟨(requests (splitLogs y).2).length - Cout.Q + k,
    (KindAlg.history_stateAt_emb _ C H c' _).trans ?_⟩
  exact congrArg (fun l => histAlong (C.toPureEnv.answerAfter (H, c')) (l.take C.Q)) hk

omit [Inhabited X] in
/-- **The adversary's history at a placed basis state** is the history, with the challenger's
replies at the oracle `H` and the coins `c`, along the first `Q` requests of its logs. -/
theorem history_emb_relG (Cout : Challenger X Y Req Resp) (H : X → Y) (c : Cout.Coins)
    (y : GameReg (A.toTPKindAlg true).unitOut.DW (A.toTPKindAlg true).unitOut.width X Y Req Resp
      (A.toTPKindAlg true).unitOut.slots) :
    A.history Cout (A.toKindAlg.emb Cout H c A.slots ((A.toTPKindAlg true).unitOut.relG y).1.1).1 =
      histAlong (Cout.toPureEnv.answerAfter (H, c)) ((requests (splitLogs y).2).take Cout.Q) :=
  KindAlg.history_stateAt_emb _ Cout H c _

end Relay

end AdaptiveIAlg

namespace QueryBoundedAdversary

open Classical

variable {X Y Req Resp O Req' Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  [Inhabited X] [Inhabited Req'] {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {t : ℕ}

/-- **The multi-request relay for transcripts, positional form** (module docstring). Under
`MultiRelay.RelaysChallenger`, the transcript of a `t`-query adversary against `Cout` at the
oracle `H` lies in `E` with at most the probability that the transcript of its relayed adversary
against `C` lies in `E'`, when, at every main coins `c'`, `E'` holds of an output with the history
along the first `C.Q` of the main requests of `rs`, followed by idle requests, with the replies of
`C` at `(H, c')`, whenever `E` holds of the output with the history along the requests `rs`
(at most `Cout.Q` of them) with the replies of `Cout` at `(H, κ c')`. -/
theorem transcriptLaw_le_relay_pos (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (Cout : Challenger X Y Req Resp)
    (C : Challenger X Y Req' Resp') (κ : C.Coins → Cout.Coins) (hF : F.RelaysChallenger Cout C κ)
    (H : X → Y) (E : O × List (HistoryEntry Req Resp) → Prop)
    (E' : O × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ (c' : C.Coins) (o : O) (rs : List Req) (k : ℕ), rs.length ≤ Cout.Q →
      E (o, histAlong (Cout.toPureEnv.answerAfter (H, κ c')) rs) →
      E' (o, histAlong (C.toPureEnv.answerAfter (H, c'))
        ((F.mainReqs Cout.Q (C.toPureEnv.answerAfter (H, c')) H rs ++
          List.replicate k F.idle).take C.Q))) :
    (𝒜.transcriptLaw Cout H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((𝒜.relay F Cout.Q).transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, E' p} := by
  rw [transcriptLaw, transcriptLaw, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  conv_rhs => rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  refine (𝒜.alg a).toOuterMeasure_le_relayAdv_budget F ((𝒜.alg a).relayOut F) Cout C κ hF H _ _ ?_
  intro c' y hy hb
  have ho := (𝒜.alg a).output_relayPlace F Cout.Q C H c' y Cout (κ c')
  obtain ⟨k, hk⟩ := (𝒜.alg a).history_relayPlace_eq F ((𝒜.alg a).relayOut F) Cout C H c' y hb
  have hh := (𝒜.alg a).history_emb_relG Cout H (κ c') y
  have hE : E (_, _) := hy.2
  rw [hh] at hE
  have h := himp c' _ _ k (List.length_take_le _ _) hE
  rw [← ho, ← hk] at h
  exact h

end QueryBoundedAdversary

end GordieHowe.Quantum

namespace GordieHowe.RingSignature.GameAdversary

open GordieHowe.Quantum Classical

variable {X Y Req Resp O Req' Resp' In : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  [Inhabited X] [Inhabited Req'] {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {t : ℕ}

/-- **The multi-request relay for game adversaries, positional form**: on every start input `inp`
whose challenger `Cout` relays `C` by the programs `F inp`, the condition of
`QueryBoundedAdversary.transcriptLaw_le_relay_pos`. -/
theorem transcriptLaw_le_relay_pos (A : GameAdversary X Y Req Resp In O t)
    (F : In → MultiRelay X Y Req Resp Req' Resp' Xs Ys) (qR : ℕ)
    (hF : ∀ inp, (F inp).qR ≤ qR) (qP : ℕ) (hP : ∀ inp, (F inp).qP ≤ qP)
    (inp : In) (Cout : Challenger X Y Req Resp) (C : Challenger X Y Req' Resp')
    (κ : C.Coins → Cout.Coins) (hFC : (F inp).RelaysChallenger Cout C κ) (H : X → Y)
    (E : O × List (HistoryEntry Req Resp) → Prop) (E' : O × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ (c' : C.Coins) (o : O) (rs : List Req) (k : ℕ), rs.length ≤ Cout.Q →
      E (o, histAlong (Cout.toPureEnv.answerAfter (H, κ c')) rs) →
      E' (o, histAlong (C.toPureEnv.answerAfter (H, c'))
        (((F inp).mainReqs Cout.Q (C.toPureEnv.answerAfter (H, c')) H rs ++
          List.replicate k (F inp).idle).take C.Q))) :
    ((A inp).transcriptLaw Cout H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((A.relay F qR hF qP hP Cout.Q inp).transcriptLaw C H).toOuterMeasure
        {x | ∃ p ∈ x, E' p} :=
  (A inp).transcriptLaw_le_relay_pos (F inp) Cout C κ hFC H E E' himp

end GordieHowe.RingSignature.GameAdversary
