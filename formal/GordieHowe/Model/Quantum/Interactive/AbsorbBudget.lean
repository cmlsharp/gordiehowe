-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Absorb

@[expose] public section

/-!
# Absorbing side requests keeps the query budget

An adversary within its query budget (`AdaptiveIAlg.WithinBudget`) stays within it after its side
requests are absorbed (`AdaptiveIAlg.absorb_withinBudget`).

- `SideRelay.relayEnv`: the relay of a main environment, an environment of the adversary's
  interface, which is the relay of the main environment in the sense of `SideRelay.Relays`
  (`SideRelay.relays_relayEnv`).
- `Env.toChallenger`: every environment at a fixed tape is, in the mixed game, the environment of
  a challenger with one coin (`Env.toChallenger_answer`, `Env.toChallenger_oracle`): its reply
  carries the response and the whole table of the new oracle in force.
- `KindAlg.mgRun_congr`: the mixed game reads an environment only through its replies and its
  oracle in force at the logs.
- `AdaptiveIAlg.WithinBudget.trace_mgRun_eq_one`: within the budget, the mixed game against every
  environment at every tape keeps the trace.
-/

open Finset Matrix
open scoped BigOperators ENNReal ComplexOrder

namespace GordieHowe.Quantum

/-! ### The relayed request list -/

namespace SideRelay

variable {Req Resp Req' Resp' : Type} (F : SideRelay Req Resp Req' Resp')

/-- **The relayed request list**: request number `i` with request `r` becomes `route i r`. -/
def relayList (rs : List Req) : List Req' :=
  rs.mapIdx F.route

/-- The relay of the empty list is empty. -/
@[simp]
theorem relayList_nil : F.relayList [] = [] :=
  rfl

/-- Relaying a request appended to a list relays it with the list's length as its number. -/
theorem relayList_append_singleton (rs : List Req) (r : Req) :
    F.relayList (rs ++ [r]) = F.relayList rs ++ [F.route rs.length r] := by
  simp [relayList, List.mapIdx_append]

/-- The relayed list has the length of the list. -/
@[simp]
theorem length_relayList (rs : List Req) : (F.relayList rs).length = rs.length :=
  List.length_mapIdx

/-- **The requests before slot `k` of the relayed logs are the relayed requests before slot
`k`.** -/
theorem requestsBefore_logs {m : ℕ} (lg : LogReg Req m) :
    ∀ k, requestsBefore (F.logs lg) k = F.relayList (requestsBefore lg k)
  | 0 => rfl
  | k + 1 => by
    rw [requestsBefore, requestsBefore, requestsBefore_logs lg k]
    split_ifs with hk
    · rw [logs_apply]
      rcases hl : lg ⟨k, hk⟩ with _ | r
      · simp
      · simp [relayList_append_singleton]
    · simp

/-- **The requests of the relayed logs are the relayed requests.** -/
theorem requests_logs {m : ℕ} (lg : LogReg Req m) :
    requests (F.logs lg) = F.relayList (requests lg) :=
  F.requestsBefore_logs lg m

end SideRelay

/-- There are at most `k` requests before slot `k`. -/
theorem length_requestsBefore_le {Req : Type} {m : ℕ} (lg : LogReg Req m) :
    ∀ k, (requestsBefore lg k).length ≤ k
  | 0 => le_rfl
  | k + 1 => by
    rw [requestsBefore, List.length_append]
    have ih := length_requestsBefore_le lg k
    split_ifs with hk
    · rcases lg ⟨k, hk⟩ with _ | r <;> simp <;> omega
    · simp
      omega

/-! ### The relay of a main environment -/

namespace SideRelay

variable {Req Resp Req' Resp' X Y : Type} (F : SideRelay Req Resp Req' Resp')
  {Ω' St' : Type} {Q' : ℕ} (E' : Env Ω' Req' Resp' X Y Q' St') (m : ℕ)

/-- **The relay of a main environment** for `m` slots: request number `c` with request `r` in
state `s` is sent to `E'` as `route c r` in state `s` (if `c < Q'`; otherwise `E'` gives no
response and keeps its state), and the reply is `answer c r` of the main response. It answers
`Q' + m` requests, so every request of an adversary with `m` slots gets the relayed reply. -/
def relayEnv : Env Ω' Req Resp X Y (Q' + m) St' where
  μ := E'.μ
  oracle₀ := E'.oracle₀
  respond ω c r s :=
    if h : (c : ℕ) < Q' then
      ⟨F.answer c r (E'.respond ω ⟨c, h⟩ (F.route c r) s).response,
        (E'.respond ω ⟨c, h⟩ (F.route c r) s).state⟩
    else ⟨F.answer c r none, s⟩

/-- The state update of the relay is the main update of the relayed request. -/
theorem update_relayEnv (ω : Ω') (s : St') (r : Req) (c : ℕ) :
    (F.relayEnv E' m).update ω s (r, c) = E'.update ω s (F.route c r, c) := by
  simp only [Env.update, relayEnv]
  split_ifs <;> first | rfl | omega

/-- **The state of the relay after a request list is the main state after the relayed list.** -/
theorem oracleIn_relayEnv (ω : Ω') (rs : List Req) :
    (F.relayEnv E' m).oracleIn ω rs = E'.oracleIn ω (F.relayList rs) := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [Env.oracleIn_append_singleton, relayList_append_singleton, Env.oracleIn_append_singleton,
      ih, update_relayEnv, length_relayList]

/-- **The reply of the relay** to request number `rs.length < m` is the relayed main reply. -/
theorem answerAfter_relayEnv (ω : Ω') {rs : List Req} (h : rs.length < m) (r : Req) :
    (F.relayEnv E' m).answerAfter ω rs r =
      F.answer rs.length r (E'.answerAfter ω (F.relayList rs) (F.route rs.length r)) := by
  have h' : rs.length < Q' + m := by omega
  simp only [Env.answerAfter, length_relayList, oracleIn_relayEnv, h', dite_true]
  simp only [relayEnv]
  split_ifs <;> rfl

variable [OracleState St' X Y]

/-- **The relay of a main environment is its relay** (`SideRelay.Relays`), at every tape. -/
theorem relays_relayEnv (ω : Ω') : F.Relays (F.relayEnv E' m) ω E' ω m where
  answer_eq lg k r hk := by
    have hlt : (requestsBefore lg k).length < m :=
      lt_of_le_of_lt (length_requestsBefore_le lg k) k.2
    simp only [Env.answer, logs_apply, hk, Option.map_some, Option.elim, requestsBefore_logs,
      answerAfter_relayEnv F E' m ω hlt]
  oracle_eq lg := by
    simp only [Env.oracle, requests_logs, oracleIn_relayEnv]

end SideRelay

/-! ### Every environment at a fixed tape is a challenger's -/

/-- The table of an oracle as an assignment list: every input assigned its value. -/
noncomputable def oracleTable {X Y : Type} [Fintype X] (f : X → Y) : List (Assignment X Y) :=
  (Finset.univ : Finset X).toList.map fun x => ⟨x, f x⟩

/-- The last assignment to a listed input in a table is its value. -/
theorem lastAssign_map_graph {X Y : Type} [DecidableEq X] (f : X → Y) {l : List X} {x : X}
    (hx : x ∈ l) : lastAssign (l.map fun x => (⟨x, f x⟩ : Assignment X Y)) x = some (f x) := by
  induction l using List.reverseRecOn with
  | nil => simp at hx
  | append_singleton l a ih =>
    rw [List.map_append, List.map_singleton, lastAssign_append_singleton]
    by_cases ha : a = x
    · subst ha
      simp
    · simp only [ha, ite_false]
      rcases List.mem_append.1 hx with h | h
      · exact ih h
      · exact absurd (List.mem_singleton.1 h).symm ha

/-- **Reprogramming by the table of an oracle gives the oracle.** -/
theorem reprogram_oracleTable {X Y : Type} [Fintype X] [DecidableEq X] (H f : X → Y) :
    H.reprogram (oracleTable f) = f := by
  funext x
  rw [reprogram_apply_eq_lastAssign, oracleTable,
    lastAssign_map_graph f (Finset.mem_toList.2 (Finset.mem_univ x))]
  rfl

namespace Env

variable {Ω Req Resp X Y St : Type} {Q : ℕ} [Fintype X] [DecidableEq X] [OracleState St X Y]

/-- **The challenger of an environment at a fixed tape** `ω`: one coin, no queries, `Q` requests
answered. Its reply to request `req` after the history `hist` is the environment's response after
the requests of `hist`, with the table of the environment's oracle in force after them and `req`
as its assignments (`oracleTable`). Against the base oracle `toOracle (E.oracle₀ ω)` its
environment (`Challenger.toPureEnv`) has the replies and the oracles in force of `E` at `ω`
(`toChallenger_answer`, `toChallenger_oracle`). It is a proof device: it writes the whole table
of the oracle. -/
noncomputable def toChallenger (E : Env Ω Req Resp X Y Q St) (ω : Ω) : Challenger X Y Req Resp where
  Coins := Unit
  coins := PMF.pure ()
  Q := Q
  q := 0
  respond _ hist req := .pure ⟨E.answerAfter ω (hist.map HistoryEntry.request) req,
    oracleTable (OracleState.toOracle (X := X) (Y := Y) (E.oracleIn ω (hist.map HistoryEntry.request ++ [req])))⟩
  respond_queries _ _ _ _ := by simp

variable (E : Env Ω Req Resp X Y Q St) (ω : Ω)

/-- The oracle in force before the first request. -/
def baseOracle : X → Y :=
  OracleState.toOracle (E.oracle₀ ω)

variable [Fintype Y] [Nonempty Y]

/-- **A request numbered below `Q` to the challenger of an environment** appends the request and
the environment's response to the history, and the table of the environment's new oracle in force
to the assignments. -/
theorem toChallenger_update_of_lt (H : X → Y) (s : ChallengerState X Y Req Resp) (r : Req) {c : ℕ}
    (hc : c < Q) :
    (E.toChallenger ω).toPureEnv.update (H, ()) s (r, c) =
      ⟨s.base, s.hist ++ [⟨r, E.answerAfter ω (s.hist.map HistoryEntry.request) r⟩],
        s.ass ++ oracleTable (OracleState.toOracle (X := X) (Y := Y)
          (E.oracleIn ω (s.hist.map HistoryEntry.request ++ [r])))⟩ := by
  simp only [Env.update, show c < (E.toChallenger ω).Q from hc, dite_true]
  rfl

/-- A request numbered `Q` or later leaves the state of the challenger of an environment. -/
theorem toChallenger_update_of_le (H : X → Y) (s : ChallengerState X Y Req Resp) (r : Req) {c : ℕ}
    (hc : Q ≤ c) : (E.toChallenger ω).toPureEnv.update (H, ()) s (r, c) = s := by
  simp only [Env.update, show ¬ c < (E.toChallenger ω).Q from Nat.not_lt.2 hc, dite_false]

/-- **The state of the challenger of an environment after a request list**: the base oracle, the
history of the first `Q` requests, and the oracle in force of the environment. -/
theorem toChallenger_oracleIn (rs : List Req) :
    ((E.toChallenger ω).toPureEnv.oracleIn (E.baseOracle ω, ()) rs).base = E.baseOracle ω ∧
      ((E.toChallenger ω).toPureEnv.oracleIn (E.baseOracle ω, ()) rs).hist.map
        HistoryEntry.request = rs.take Q ∧
      OracleState.toOracle (X := X) (Y := Y)
          ((E.toChallenger ω).toPureEnv.oracleIn (E.baseOracle ω, ()) rs) =
        OracleState.toOracle (X := X) (Y := Y) (E.oracleIn ω rs) := by
  induction rs using List.reverseRecOn with
  | nil => exact ⟨rfl, by simp [Env.oracleIn_nil, Challenger.toPureEnv], rfl⟩
  | append_singleton rs r ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Env.oracleIn_append_singleton, Env.oracleIn_append_singleton]
    by_cases hr : rs.length < Q
    · have ht : rs.take Q = rs := List.take_of_length_le hr.le
      rw [E.toChallenger_update_of_lt ω _ _ _ hr, ← Env.oracleIn_append_singleton]
      refine ⟨h1, ?_, ?_⟩
      · rw [List.map_append, h2, ht, List.take_of_length_le (by simp; omega)]
        rfl
      · change Function.reprogram _ (_ ++ _) = _
        rw [QROM.reprogram_append, reprogram_oracleTable, h2, ht]
    · have hu : E.update ω (E.oracleIn ω rs) (r, rs.length) = E.oracleIn ω rs := by
        simp [Env.update, hr]
      rw [E.toChallenger_update_of_le ω _ _ _ (Nat.not_lt.1 hr), hu,
        List.take_append_of_le_length (by omega)]
      exact ⟨h1, h2, h3⟩

/-- **The challenger of an environment answers as the environment.** -/
theorem toChallenger_answerAfter (rs : List Req) (req : Req) :
    (E.toChallenger ω).toPureEnv.answerAfter (E.baseOracle ω, ()) rs req = E.answerAfter ω rs req := by
  by_cases hr : rs.length < Q
  · have h2 := (E.toChallenger_oracleIn ω rs).2.1
    rw [List.take_of_length_le hr.le] at h2
    simp only [Env.answerAfter, show rs.length < (E.toChallenger ω).Q from hr, dite_true]
    change E.answerAfter ω (List.map HistoryEntry.request _) req = _
    rw [h2]
    simp only [Env.answerAfter, hr, dite_true]
  · simp only [Env.answerAfter, show ¬ rs.length < (E.toChallenger ω).Q from hr, hr, dite_false]

/-- **The replies of the challenger of an environment are the environment's.** -/
theorem toChallenger_answer {m : ℕ} (lg : LogReg Req m) (k : Fin m) :
    (E.toChallenger ω).toPureEnv.answer (E.baseOracle ω, ()) lg k = E.answer ω lg k := by
  simp only [Env.answer]
  congr 1
  funext req
  exact E.toChallenger_answerAfter ω _ req

/-- **The oracles in force of the challenger of an environment are the environment's.** -/
theorem toChallenger_oracle {m : ℕ} (lg : LogReg Req m) :
    (E.toChallenger ω).toPureEnv.oracle (E.baseOracle ω, ()) lg = E.oracle ω lg :=
  (E.toChallenger_oracleIn ω (requests lg)).2.2

end Env

/-! ### The mixed game reads the environment through its replies and its oracles -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y]
  {ksK : KindShape X Y Req Resp} (K : KindAlg ksK O)

/-- **The mixed game depends on the environment only through its replies and its oracles in
force at the logs.** -/
theorem mgRun_congr {Ω Ω' St St' : Type} {Q Q' : ℕ} [OracleState St X Y] [OracleState St' X Y]
    (E : Env Ω Req Resp X Y Q St) (E' : Env Ω' Req Resp X Y Q' St') {ω : Ω} {ω' : Ω'}
    (hans : ∀ (lg : LogReg Req K.slots) k, E.answer ω lg k = E'.answer ω' lg k)
    (hor : ∀ lg : LogReg Req K.slots, E.oracle ω lg = E'.oracle ω' lg) (deph : Bool) :
    K.mgRun E ω deph = K.mgRun E' ω' deph := by
  have h1 : ∀ k, K.respG E ω k = K.respG E' ω' k := fun k => by simp only [respG, hans]
  have h2 : E.oraclePerm (W := K.W) (n := K.width) (m := K.slots) K.kind ω = E'.oraclePerm K.kind ω' := by
    simp only [Env.oraclePerm, hor]
  have h3 : K.postG E ω = K.postG E' ω' := by simp only [postG, hor]
  simp only [mgRun, mgCirc, eventCirc, h1, h2, h3]

/-- The mixed game does not increase the trace. -/
theorem re_trace_mgRun_le {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St)
    (ω : Ω) (deph : Bool) : (K.mgRun E ω deph).trace.re ≤ 1 := by
  have h := Circuit.re_trace_run_le (Equiv.refl _) (K.mgCirc E ω deph) K.mgInitM.posSemidef
  rw [K.mgInitM.trace_eq_one, Complex.one_re] at h
  exact h

end KindAlg

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y]

/-- **The probability that the composition does not end** is one minus the coin average of the
traces of the mixed game. -/
theorem outLaw_compose_none_eq {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) (C : Challenger X Y Req Resp)
    (H : X → Y) :
    (B.compose C).outLaw H none = ENNReal.ofReal (1 - ∑ c, (C.coins c).toReal *
      (B.toKindAlg.mgRun C.toPureEnv (H, c) true).trace.re) := by
  rw [Alg.outLaw_none, compose_eq_composeBothOut, KindAlg.composeBothOut_final,
    KindAlg.composeBoth_final, KindAlg.trace_withAnc, Matrix.trace_sum, Complex.re_sum]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    re_trace_embed (B.toKindAlg.emb_injective C H c _)]

/-- **Within the budget, the mixed game keeps the trace** against every environment at every
tape: the environment at the tape is that of a challenger with one coin (`Env.toChallenger`). -/
theorem WithinBudget.trace_mgRun_eq_one {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O} (hA : A.WithinBudget)
    {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St) (ω : Ω) :
    (A.toKindAlg.mgRun E ω true).trace = 1 := by
  have h0 := ((withinBudget_iff A).1 hA) (E.toChallenger ω) (E.baseOracle ω)
  rw [AdaptiveIAlg.outLaw_compose_none_eq A] at h0
  have hs : ∀ f : (E.toChallenger ω).Coins → ℝ, ∑ c, f c = f () := fun f =>
    Fintype.sum_eq_single _ fun x hx => (hx rfl).elim
  rw [ENNReal.ofReal_eq_zero, sub_nonpos, hs] at h0
  have hc : ((E.toChallenger ω).coins ()).toReal = 1 := by
    change ((PMF.pure ()) ()).toReal = 1
    simp
  rw [hc, one_mul, A.toKindAlg.mgRun_congr _ E (E.toChallenger_answer ω)
    (E.toChallenger_oracle ω)] at h0
  have hle := A.toKindAlg.re_trace_mgRun_le E ω true
  have hpsd := Circuit.posSemidef_run (Equiv.refl _) (A.toKindAlg.mgCirc E ω true)
    A.toKindAlg.mgInitM.posSemidef
  have him := (Complex.nonneg_iff.1 hpsd.trace_nonneg).2
  exact Complex.ext (by simpa using le_antisymm hle h0) (by rw [Complex.one_im]; exact him.symm)

variable {Req' Resp' : Type} [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited Req']

/-- **Absorbing side requests keeps the query budget**: if the adversary `A` stays within its
budget, so does the adversary with its side requests absorbed (`absorb`), for an injective relay
of requests. Against a main challenger at every oracle and coins, the mixed game of the absorbed
adversary is the placed mixed game of `A` against the relay of the main challenger's environment
(`mgRun_absorb`, `SideRelay.relays_relayEnv`), which keeps the trace
(`WithinBudget.trace_mgRun_eq_one`). -/
theorem absorb_withinBudget {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : SideRelay Req Resp Req' Resp')
    (hinj : ∀ c, Function.Injective (F.route c)) (hA : A.WithinBudget) :
    (A.absorb F).WithinBudget := by
  refine ((withinBudget_iff (A.absorb F)).2 fun C' H => ?_)
  rw [AdaptiveIAlg.outLaw_compose_none_eq, ENNReal.ofReal_eq_zero, sub_nonpos]
  have h : ∀ c', ((A.absorb F).toKindAlg.mgRun C'.toPureEnv (H, c') true).trace.re = 1 := by
    intro c'
    change ((A.absorb F).toKindAlg.mgRun C'.toPureEnv (H, c') true).trace.re = 1
    rw [A.mgRun_absorb F C'.toPureEnv (H, c') (F.relayEnv C'.toPureEnv A.slots)
      (H, c') (F.relays_relayEnv C'.toPureEnv A.slots (H, c')) hinj,
      re_trace_embed (A.placeClean_injective F _ _ _)]
    exact (congrArg Complex.re (hA.trace_mgRun_eq_one _ _)).trans Complex.one_re
  simp only [h, mul_one]
  have hsum : ∑ c', C'.coins c' = 1 := by
    rw [← tsum_fintype (L := .unconditional _), PMF.tsum_coe]
  rw [← ENNReal.toReal_sum fun c _ => PMF.apply_ne_top _ c, hsum, ENNReal.toReal_one]

end AdaptiveIAlg

end GordieHowe.Quantum
