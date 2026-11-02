-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AbsorbBudget

@[expose] public section

/-!
# Challengers that relay a main challenger

A sufficient condition for the environment of a challenger to be the relay of a main challenger's
(`SideRelay.Relays`, the hypothesis of `AdaptiveIAlg.outLaw_absorb`), stated on the challengers'
reply programs.

- `SideRelay.RelaysChallenger F C c C' c'`: at the coins `c` and `c'`, the two challengers answer the
  same number of requests; request number `i < Q` with request `r` runs, under every oracle, as the
  main challenger's reply program on `route i r`, its response relayed by `answer i r` and its
  assignments kept, after a history `hist` and a main history `hist'` whose requests are the relayed
  requests of `hist`; and `answer i r none = none` for `i ≥ Q`.
- `SideRelay.RelaysChallenger.relays`: the condition gives `Relays` at every base oracle.
- `Challenger.KeepsView C f`: the assignments of each reply keep the view `f` of the oracle in
  force; `KeepsView.oracleIn`, `KeepsView.oracle`: then every state's oracle in force has the view
  of the base oracle.
-/

namespace GordieHowe.Quantum

namespace Challenger

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- The state update of a challenger's environment on a request numbered below `Q`. -/
theorem update_toPureEnv_of_lt
    (C : Challenger X Y Req Resp) (ω : (X → Y) × C.Coins) (s : ChallengerState X Y Req Resp)
    (r : Req) {i : ℕ} (hi : i < C.Q) :
    C.toPureEnv.update ω s (r, i) =
      ⟨s.base, s.hist ++ [⟨r, ((C.respond ω.2 s.hist r).run (s.base.reprogram s.ass)).response⟩],
        s.ass ++ ((C.respond ω.2 s.hist r).run (s.base.reprogram s.ass)).assignments⟩ := by
  simp only [Env.update, hi, dite_true]
  rfl

/-- A request numbered `Q` or later leaves the state of a challenger's environment unchanged. -/
theorem update_toPureEnv_of_le
    (C : Challenger X Y Req Resp) (ω : (X → Y) × C.Coins) (s : ChallengerState X Y Req Resp)
    (r : Req) {i : ℕ} (hi : C.Q ≤ i) : C.toPureEnv.update ω s (r, i) = s := by
  simp only [Env.update, not_lt.2 hi, dite_false]

/-- The reply of a challenger's environment to a request numbered below `Q`. -/
theorem answerAfter_toPureEnv_of_lt (C : Challenger X Y Req Resp) (ω : (X → Y) × C.Coins)
    (rs : List Req) (r : Req) (hi : rs.length < C.Q) :
    C.toPureEnv.answerAfter ω rs r =
      ((C.respond ω.2 (C.toPureEnv.oracleIn ω rs).hist r).run
        ((C.toPureEnv.oracleIn ω rs).base.reprogram (C.toPureEnv.oracleIn ω rs).ass)).response := by
  simp only [Env.answerAfter, hi, dite_true]
  rfl

/-- A request numbered `Q` or later gets no reply from a challenger's environment. -/
theorem answerAfter_toPureEnv_of_le (C : Challenger X Y Req Resp) (ω : (X → Y) × C.Coins)
    (rs : List Req) (r : Req) (hi : C.Q ≤ rs.length) : C.toPureEnv.answerAfter ω rs r = none := by
  simp only [Env.answerAfter, not_lt.2 hi, dite_false]

/-! ### A view of the oracle kept by a challenger -/

section KeepsView

variable {X Y Req Resp Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (C : Challenger X Y Req Resp) (f : (X → Y) → Z)

/-- **The challenger keeps the view `f` of the oracle**: the assignments of each reply, at the
oracle in force, do not change `f` of it. -/
def KeepsView : Prop :=
  ∀ c hist r (G : X → Y), f (G.reprogram ((C.respond c hist r).run G).assignments) = f G

variable {C f}

/-- **A challenger keeping a view keeps it in every state**: after any requests the state's base
oracle is `H` and the oracle in force has the view of `H`. -/
theorem KeepsView.oracleIn (hC : C.KeepsView f) (H : X → Y) (c : C.Coins) (rs : List Req) :
    (C.toPureEnv.oracleIn (H, c) rs).base = H ∧
      f ((C.toPureEnv.oracleIn (H, c) rs).base.reprogram (C.toPureEnv.oracleIn (H, c) rs).ass) =
        f H := by
  induction rs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton rs r ih =>
    rw [Env.oracleIn_append_singleton]
    by_cases hq : rs.length < C.Q
    · rw [update_toPureEnv_of_lt C _ _ _ hq]
      refine ⟨ih.1, ?_⟩
      simp only
      rw [QROM.reprogram_append, hC, ih.2]
    · rw [update_toPureEnv_of_le C _ _ _ (not_lt.1 hq)]
      exact ih

/-- **A challenger keeping a view keeps it in the oracle in force** after any logs. -/
theorem KeepsView.oracle (hC : C.KeepsView f) (H : X → Y) (c : C.Coins) {m : ℕ}
    (lg : LogReg Req m) : f (C.toPureEnv.oracle (H, c) lg) = f H :=
  (hC.oracleIn H c (requests lg)).2

end KeepsView

end Challenger

namespace SideRelay

variable {X Y Req Resp Req' Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (F : SideRelay Req Resp Req' Resp')

/-- **A challenger relays a main challenger at fixed coins** (`SideRelay`): the two answer the
same number `Q` of requests (`Q_eq`); after a history `hist` with `i < Q` requests and a main
history `hist'` whose requests are the relayed requests of `hist` (`F.relayList`), the challenger's
reply program on `r` runs, under every oracle, as the main challenger's reply program on
`route i r` with its response relayed by `answer i r` and its assignments kept (`run_eq`); and the
relay answers `none` to requests numbered `Q` or later when the main challenger does
(`answer_none`). A stateful main challenger may read its history; only the relayed histories
arise. -/
structure RelaysChallenger (C : Challenger X Y Req Resp) (c : C.Coins)
    (C' : Challenger X Y Req' Resp') (c' : C'.Coins) : Prop where
  /-- The two challengers answer the same number of requests. -/
  Q_eq : C.Q = C'.Q
  /-- The reply programs run as the relayed main reply programs. -/
  run_eq : ∀ (hist : List (HistoryEntry Req Resp)) (hist' : List (HistoryEntry Req' Resp'))
    (r : Req) (G : X → Y),
    hist'.map HistoryEntry.request = F.relayList (hist.map HistoryEntry.request) →
    hist.length < C.Q →
    (C.respond c hist r).run G =
      ⟨F.answer hist.length r ((C'.respond c' hist' (F.route hist.length r)).run G).response,
        ((C'.respond c' hist' (F.route hist.length r)).run G).assignments⟩
  /-- Requests numbered `Q` or later are answered by `none`. -/
  answer_none : ∀ i r, C.Q ≤ i → F.answer i r none = none

variable {F} {C : Challenger X Y Req Resp} {c : C.Coins} {C' : Challenger X Y Req' Resp'}
  {c' : C'.Coins}

/-- **The states after a request list and after its relay**: both have the base oracle `H`, the
same assignments, and histories of length `min |rs| Q`, the requests of the main history being the
relayed requests of the history. -/
theorem RelaysChallenger.oracleIn (h : F.RelaysChallenger C c C' c') (H : X → Y) (rs : List Req) :
    (C.toPureEnv.oracleIn (H, c) rs).base = H ∧
      (C'.toPureEnv.oracleIn (H, c') (F.relayList rs)).base = H ∧
      (C.toPureEnv.oracleIn (H, c) rs).ass = (C'.toPureEnv.oracleIn (H, c') (F.relayList rs)).ass ∧
      (C.toPureEnv.oracleIn (H, c) rs).hist.length = min rs.length C.Q ∧
      (C'.toPureEnv.oracleIn (H, c') (F.relayList rs)).hist.length = min rs.length C.Q ∧
      (C'.toPureEnv.oracleIn (H, c') (F.relayList rs)).hist.map HistoryEntry.request =
        F.relayList ((C.toPureEnv.oracleIn (H, c) rs).hist.map HistoryEntry.request) := by
  induction rs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, rfl, by simp [Env.oracleIn_nil, Challenger.toPureEnv],
      by simp [relayList_nil, Env.oracleIn_nil, Challenger.toPureEnv],
      by simp [relayList_nil, Env.oracleIn_nil, Challenger.toPureEnv]⟩
  | append_singleton rs r ih =>
    rw [Env.oracleIn_append_singleton, relayList_append_singleton, Env.oracleIn_append_singleton,
      length_relayList]
    generalize C.toPureEnv.oracleIn (H, c) rs = s at ih ⊢
    generalize C'.toPureEnv.oracleIn (H, c') (F.relayList rs) = s' at ih ⊢
    obtain ⟨hb, hb', ha, hl, hl', hrq⟩ := ih
    by_cases hq : rs.length < C.Q
    · have hq' : rs.length < C'.Q := h.Q_eq ▸ hq
      have hlen : s.hist.length = rs.length := by rw [hl]; exact min_eq_left hq.le
      have hlen' : s'.hist.length = rs.length := by rw [hl']; exact min_eq_left hq.le
      have hrun := h.run_eq s.hist s'.hist r (s.base.reprogram s.ass) hrq (hlen ▸ hq)
      rw [hlen] at hrun
      have horc : s'.base.reprogram s'.ass = s.base.reprogram s.ass := by rw [hb, hb', ha]
      rw [C.update_toPureEnv_of_lt _ _ _ hq, C'.update_toPureEnv_of_lt _ _ _ hq']
      refine ⟨hb, hb', ?_, ?_, ?_, ?_⟩
      · change s.ass ++ ((C.respond c s.hist r).run (s.base.reprogram s.ass)).assignments =
          s'.ass ++ ((C'.respond c' s'.hist (F.route rs.length r)).run
            (s'.base.reprogram s'.ass)).assignments
        rw [hrun, horc, ha]
      · simp only [List.length_append, List.length_singleton, hlen]
        omega
      · simp only [List.length_append, List.length_singleton, hlen']
        omega
      · simp only [List.map_append, List.map_cons, List.map_nil, hrq, relayList_append_singleton,
          List.length_map, hlen]
    · have hq' : C'.Q ≤ rs.length := h.Q_eq ▸ not_lt.1 hq
      rw [C.update_toPureEnv_of_le _ _ _ (not_lt.1 hq), C'.update_toPureEnv_of_le _ _ _ hq']
      refine ⟨hb, hb', ha, ?_, ?_, hrq⟩
      · rw [hl, List.length_append, List.length_singleton]; omega
      · rw [hl', List.length_append, List.length_singleton]; omega

/-- **The relay condition on the challengers gives the relay of their environments**
(`SideRelay.Relays`) at every base oracle `H` and every number of slots. -/
theorem RelaysChallenger.relays [AddGroup Y] (h : F.RelaysChallenger C c C' c')
    (H : X → Y) (m : ℕ) : F.Relays C.toPureEnv (H, c) C'.toPureEnv (H, c') m where
  answer_eq lg k r hk := by
    simp only [Env.answer, logs_apply, hk, Option.map_some, Option.elim, requestsBefore_logs]
    obtain ⟨hb, hb', ha, hl, hl', hrq⟩ := h.oracleIn H (requestsBefore lg k)
    by_cases hq : (requestsBefore lg k).length < C.Q
    · have hq' : (F.relayList (requestsBefore lg k)).length < C'.Q := by
        rw [length_relayList]; exact h.Q_eq ▸ hq
      rw [C.answerAfter_toPureEnv_of_lt _ _ _ hq,
        C'.answerAfter_toPureEnv_of_lt _ _ _ hq']
      generalize C.toPureEnv.oracleIn (H, c) (requestsBefore lg k) = s at hb ha hl hrq ⊢
      generalize C'.toPureEnv.oracleIn (H, c') (F.relayList (requestsBefore lg k)) = s' at hb' ha hl' hrq ⊢
      have hlen : s.hist.length = (requestsBefore lg k).length := by rw [hl]; exact min_eq_left hq.le
      have hlen' : s'.hist.length = (requestsBefore lg k).length := by
        rw [hl']; exact min_eq_left hq.le
      have hrun := h.run_eq s.hist s'.hist r (s.base.reprogram s.ass) hrq (hlen ▸ hq)
      rw [hlen] at hrun
      change ((C.respond c s.hist r).run (s.base.reprogram s.ass)).response = _
      rw [hrun, hb, hb', ha]
    · have hq' : C'.Q ≤ (F.relayList (requestsBefore lg k)).length := by
        rw [length_relayList]; exact h.Q_eq ▸ not_lt.1 hq
      rw [C.answerAfter_toPureEnv_of_le _ _ _ (not_lt.1 hq),
        C'.answerAfter_toPureEnv_of_le _ _ _ hq']
      exact (h.answer_none _ r (not_lt.1 hq)).symm
  oracle_eq lg := by
    obtain ⟨hb, hb', ha, -, -, -⟩ := h.oracleIn H (requests lg)
    simp only [Env.oracle, requests_logs, Quantum.OracleState.toOracle_fun]
    change (C.toPureEnv.oracleIn (H, c) (requests lg)).base.reprogram
        (C.toPureEnv.oracleIn (H, c) (requests lg)).ass =
      (C'.toPureEnv.oracleIn (H, c') (F.relayList (requests lg))).base.reprogram
        (C'.toPureEnv.oracleIn (H, c') (F.relayList (requests lg))).ass
    rw [hb, hb', ha]

end SideRelay

end GordieHowe.Quantum
