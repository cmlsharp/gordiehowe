-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AssignRelayEnv

@[expose] public section

/-!
# An outer challenger that relays a main challenger through an assigning relay

- `AssignRelay.stripEntry`: an entry of `chalD`'s history read as an outer entry (the request
  without its number, the outer response).
- `AssignRelay.RelaysChallenger G C c C' c'` (the hypothesis of the absorption of an assigning
  challenger): at the coins `c` of the outer challenger `C` and `c'` of the main challenger `C'`,
  after an outer history read from a history `histD` of `chalD` with fewer than `C.Q` entries, each
  with a response, that `chalD` reaches at `c'` on the relay of some outer requests, the
  reply program of `C` on the request `r` runs, under every oracle, as `G`'s program of number
  `|histD|` with the main request answered by `C'` after the main history recorded in `histD`,
  with its response and its assignments.
- `AssignRelay.RelaysChallenger.relays`: the condition gives the relay of environments
  (`SideRelay.Relays`) of `chalD` by `sideRelay`, at every base oracle.
-/

open Finset


namespace GordieHowe.Quantum

open GordieHowe.OracleProg

namespace AssignRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [AddGroup Ys]

/-- **An entry of `chalD`'s history as an outer entry**: the request without its number, the outer
response. -/
def stripEntry {Q : ℕ} (e : HistoryEntry (Req × Fin (Q + 1)) (RespD X Y Resp Req' Resp')) :
    HistoryEntry Req Resp :=
  ⟨e.request.1, e.response.bind fun x => x.1⟩

/-- **The outer challenger relays the main challenger through `G`** at the coins `c` and `c'`
(module docstring). -/
structure RelaysChallenger (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys)
    (C : Challenger X Y Req Resp)
    (c : C.Coins) (C' : Challenger X Y Req' Resp') (c' : C'.Coins) : Prop where
  /-- The outer reply programs run as `G`'s programs. -/
  run_eq : ∀ (histD : List (HistoryEntry (Req × Fin (C.Q + 1)) (RespD X Y Resp Req' Resp')))
    (r : Req) (H' : X → Y), histD.length < C.Q → (∀ e ∈ histD, e.response.isSome) →
    ∀ {reach : ∃ (H : X → Y) (rs : List Req), histD =
      ((chalD C' G C.Q).toPureEnv.oracleIn (H, c') ((sideRelay X Y Req Resp Req' Resp'
          C.Q).relayList rs)).hist},
    (C.respond c (histD.map stripEntry) r).run H' =
      ⟨((relayProg C' G c' histD (fun _ => none) (histTab histD) histD.length r).run
          H').1.response,
        ((relayProg C' G c' histD (fun _ => none) (histTab histD) histD.length r).run
          H').1.assignments⟩

variable {G : AssignRelay X Y Req Resp Req' Resp' Xs Ys} {C : Challenger X Y Req Resp} {c : C.Coins}
  {C' : Challenger X Y Req' Resp'} {c' : C'.Coins}

/-- **The states after a request list and after its relay**: the base oracle, the same
assignments, and the outer history read from `chalD`'s, of length `min |rs| Q`. -/
theorem RelaysChallenger.oracleIn (h : G.RelaysChallenger C c C' c') (H : X → Y) (rs : List Req) :
    (C.toPureEnv.oracleIn (H, c) rs).base = H ∧
      ((chalD C' G C.Q).toPureEnv.oracleIn (H, c') ((sideRelay X Y Req Resp Req' Resp'
          C.Q).relayList rs)).base = H ∧
      (C.toPureEnv.oracleIn (H, c) rs).ass =
        ((chalD C' G C.Q).toPureEnv.oracleIn (H, c') ((sideRelay X Y Req Resp Req' Resp'
            C.Q).relayList rs)).ass ∧
      (C.toPureEnv.oracleIn (H, c) rs).hist =
        ((chalD C' G C.Q).toPureEnv.oracleIn (H, c') ((sideRelay X Y Req Resp Req' Resp'
            C.Q).relayList rs)).hist.map
          stripEntry ∧
      ((chalD C' G C.Q).toPureEnv.oracleIn (H, c') ((sideRelay X Y Req Resp Req' Resp'
          C.Q).relayList rs)).hist.length =
        min rs.length C.Q ∧
      ∀ e ∈ ((chalD C' G C.Q).toPureEnv.oracleIn (H, c') ((sideRelay X Y Req Resp Req' Resp'
          C.Q).relayList rs)).hist,
        e.response.isSome := by
  induction rs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, rfl, rfl, by simp [Env.oracleIn_nil, Challenger.toPureEnv],
      by simp [Env.oracleIn_nil, Challenger.toPureEnv]⟩
  | append_singleton rs r ih =>
    rw [Env.oracleIn_append_singleton, SideRelay.relayList_append_singleton,
      Env.oracleIn_append_singleton, SideRelay.length_relayList]
    generalize C.toPureEnv.oracleIn (H, c) rs = s at ih ⊢
    generalize hs' : (chalD C' G C.Q).toPureEnv.oracleIn (H, c')
        ((sideRelay X Y Req Resp Req' Resp' C.Q).relayList rs) = s' at ih ⊢
    obtain ⟨hb, hb', ha, hh, hl, hsome⟩ := ih
    by_cases hq : rs.length < C.Q
    · have hlen : s'.hist.length = rs.length := by rw [hl]; exact min_eq_left hq.le
      have hrun := h.run_eq s'.hist r (s.base.reprogram s.ass) (hlen ▸ hq) hsome
        (reach := ⟨H, rs, by rw [hs']⟩)
      rw [← hh, hlen] at hrun
      have horc : s'.base.reprogram s'.ass = s.base.reprogram s.ass := by rw [hb, hb', ha]
      rw [C.update_toPureEnv_of_lt _ _ _ hq,
        (chalD C' G C.Q).update_toPureEnv_of_lt _ _ _ (show rs.length < (chalD C' G C.Q).Q from hq)]
      have hcap : ((sideRelay X Y Req Resp Req' Resp' C.Q).route rs.length
          r).2.val = rs.length := by
        simp [sideRelay, min_eq_left hq.le]
      refine ⟨hb, hb', ?_, ?_, ?_, ?_⟩
      · simp only
        rw [horc, hrun, chalD_respond, run_mapOutput, hcap, ha]
        rfl
      · simp only
        rw [horc, hrun, List.map_append, ← hh, chalD_respond, run_mapOutput, hcap]
        simp [stripEntry, recordOf, sideRelay]
      · simp only [List.length_append, List.length_singleton, hlen]
        omega
      · intro e he
        rcases List.mem_append.1 he with he | he
        · exact hsome e he
        · rw [List.mem_singleton.1 he, chalD_respond, run_mapOutput]
          rfl
    · rw [C.update_toPureEnv_of_le _ _ _ (not_lt.1 hq),
        (chalD C' G C.Q).update_toPureEnv_of_le _ _ _ (show (chalD C' G C.Q).Q ≤ rs.length from
          not_lt.1 hq)]
      refine ⟨hb, hb', ha, hh, ?_, hsome⟩
      rw [hl, List.length_append, List.length_singleton]
      omega

/-- **The relay condition on the challengers gives the relay of their environments**
(`SideRelay.Relays`) at every base oracle and every number of slots. -/
theorem RelaysChallenger.relays [AddGroup Y] (h : G.RelaysChallenger C c C' c') (H : X → Y)
    (m : ℕ) : (sideRelay X Y Req Resp Req' Resp' C.Q).Relays C.toPureEnv (H, c) (chalD C' G
        C.Q).toPureEnv (H, c') m where
  answer_eq lg k r hk := by
    simp only [Env.answer, SideRelay.logs_apply, hk, Option.map_some, Option.elim,
      SideRelay.requestsBefore_logs]
    obtain ⟨hb, hb', ha, hh, hl, hsome⟩ := h.oracleIn H (requestsBefore lg k)
    by_cases hq : (requestsBefore lg k).length < C.Q
    · rw [C.answerAfter_toPureEnv_of_lt _ _ _ hq,
        (chalD C' G C.Q).answerAfter_toPureEnv_of_lt _ _ _
          (show ((sideRelay X Y Req Resp Req' Resp' C.Q).relayList (requestsBefore lg k)).length <
              (chalD C' G C.Q).Q by
            rw [SideRelay.length_relayList]; exact hq)]
      generalize C.toPureEnv.oracleIn (H, c) (requestsBefore lg k) = s at hb ha hh ⊢
      generalize hs' : (chalD C' G C.Q).toPureEnv.oracleIn (H, c')
        ((sideRelay X Y Req Resp Req' Resp' C.Q).relayList (requestsBefore lg
            k)) = s' at hb' ha hh hl hsome ⊢
      have hlen : s'.hist.length = (requestsBefore lg k).length := by
        rw [hl]; exact min_eq_left hq.le
      have hrun := h.run_eq s'.hist r (s.base.reprogram s.ass) (hlen ▸ hq) hsome
        (reach := ⟨H, requestsBefore lg k, by rw [hs']⟩)
      rw [← hh, hlen] at hrun
      have hcap : ((sideRelay X Y Req Resp Req' Resp' C.Q).route (requestsBefore lg k).length
          r).2.val =
          (requestsBefore lg k).length := by
        simp [sideRelay, min_eq_left hq.le]
      change ((C.respond c s.hist r).run (s.base.reprogram s.ass)).response = _
      rw [hrun, hb, hb', ha, chalD_respond, run_mapOutput, hcap]
      simp [recordOf, sideRelay]
    · rw [C.answerAfter_toPureEnv_of_le _ _ _ (not_lt.1 hq),
        (chalD C' G C.Q).answerAfter_toPureEnv_of_le _ _ _
          (show (chalD C' G C.Q).Q ≤ ((sideRelay X Y Req Resp Req' Resp' C.Q).relayList
              (requestsBefore lg k)).length by
            rw [SideRelay.length_relayList]; exact not_lt.1 hq)]
      rfl
  oracle_eq lg := by
    obtain ⟨hb, hb', ha, -, -, -⟩ := h.oracleIn H (requests lg)
    simp only [Env.oracle, SideRelay.requests_logs]
    change (C.toPureEnv.oracleIn (H, c) (requests lg)).base.reprogram
        (C.toPureEnv.oracleIn (H, c) (requests lg)).ass =
      ((chalD C' G C.Q).toPureEnv.oracleIn (H, c')
          ((sideRelay X Y Req Resp Req' Resp' C.Q).relayList (requests lg))).base.reprogram
        ((chalD C' G C.Q).toPureEnv.oracleIn (H, c')
            ((sideRelay X Y Req Resp Req' Resp' C.Q).relayList (requests lg))).ass
    rw [hb, hb', ha]

end AssignRelay

end GordieHowe.Quantum
