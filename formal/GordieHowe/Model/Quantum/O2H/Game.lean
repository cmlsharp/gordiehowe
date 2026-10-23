-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Game
public import GordieHowe.Model.Quantum.O2H.FreshSecret

@[expose] public section

/-!
# A game as an oracle algorithm, and O2H at one request

For a distinguisher `D` and an environment `E`, `Distinguisher.gameAlg D E post L` is the game as
an `OracleAlg` with input the tape `ω`. Its oracle steps are the `m` slots: slot `k` applies
`queryPermOf (E.oracleFn D.kind ω)`, the oracle in force on the query branches and the zero
function on the request branches. Everything else is inside its input-dependent steps: the
distinguisher's steps, the requests (`Env.requestPerm`) and, after the last slot, `post`. AHU19
p. 10: "additional oracles can simply be encoded as part of z"; here the tape is the input `z`.
Its accepting set is the distinguisher's accepting set on the logs in `L`.

- `acceptProb_gameAlg`: run with the oracle of an environment `E'` whose answers are those of
  `E` and whose oracle agrees with `E`'s on the logs in `L`, the oracle algorithm accepts with
  the probability of the game against `E'` restricted to `L`.
- `madeLogs j`: the logs of the branches that made request number `j`. Once made, a request stays
  made (`mem_madeLogs_eventPerm`).
- `mask_stage_eq_of_agree`: the part of the game state on the branches that have not made
  request `j` depends only on the answers to the requests before `j` and the oracles after at
  most `j` requests. So `acceptProbOnAt_notMade_eq`: two environments that agree there give the
  same acceptance probability on the branches that never make request `j`.
- `openSet j`, `oracleFn_agree`, `mask_pre_eq`: the query branches that have not made request
  `j`, on which two environments that differ only in the oracle in force before request `j` can
  differ, and the independence of the part of each state on them from a fresh component of the
  tape. The O2H step at request `j` that uses them is
  `Distinguisher.advantage_acceptProbOn_made_le_of_fresh_secret_budget`
  (`GordieHowe/Model/Quantum/O2H/Budget.lean`).

The restriction to the branches that make request `j` is needed because `post` sees the whole
final oracle: on a branch that never makes request `j`, the two environments end with oracles
that differ on `T σ`. The hybrids compare those branches separately
(`acceptProbOnAt_notMade_eq`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### Masks and basis permutations -/

section Mask

variable {ι : Type*} [Fintype ι]

theorem permOp_trans (π π' : Equiv.Perm ι) (v : QState ι) :
    permOp (π.trans π') v = permOp π' (permOp π v) :=
  rfl

/-- The probability of `A ∩ B` is the probability of `A` in the masked vector. -/
theorem prob_inter_eq_prob_mask (A B : Set ι) (v : QState ι) :
    prob (A ∩ B) v = prob A (mask B v) := by
  have h : mask A (mask B v) = mask (A ∩ B) v := by
    ext i
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp [hA, hB]
  rw [prob, prob, h]

/-- **Masked runs agree.** Let `v` and `v'` be supported in `B`, with the same mask on `N`.
Suppose the permutations `π` and `π'` never map a state of `B` outside `N` into `N`, and agree on
every state of `B ∩ N` that one of them maps into `N`. Then `permOp π v` and `permOp π' v'` have
the same mask on `N`. -/
theorem mask_permOp_eq_of_agree {B N : Set ι} {π π' : Equiv.Perm ι} {v v' : QState ι}
    (hv : Supported B v) (hv' : Supported B v') (hN : mask N v = mask N v')
    (hπ : ∀ r ∈ B, r ∉ N → π r ∉ N) (hπ' : ∀ r ∈ B, r ∉ N → π' r ∉ N)
    (hagree : ∀ r ∈ B, r ∈ N → π r ∈ N ∨ π' r ∈ N → π r = π' r) :
    mask N (permOp π v) = mask N (permOp π' v') := by
  have key : ∀ {σ σ' : Equiv.Perm ι} {u u' : QState ι}, Supported B u → Supported B u' →
      mask N u = mask N u' → (∀ r ∈ B, r ∉ N → σ r ∉ N) → (∀ r ∈ B, r ∉ N → σ' r ∉ N) →
      (∀ r ∈ B, r ∈ N → σ r ∈ N ∨ σ' r ∈ N → σ r = σ' r) →
      ∀ s ∈ N, σ.symm s ∈ B → u (σ.symm s) = u' (σ'.symm s) := by
    intro σ σ' u u' hu hu' hN hσ hσ' hag s hs hrB
    have hrN : σ.symm s ∈ N := by
      by_contra h
      exact hσ _ hrB h (by simpa using hs)
    have he : σ' (σ.symm s) = s := by
      rw [← hag _ hrB hrN (Or.inl (by simpa using hs)), Equiv.apply_symm_apply]
    have he' : σ'.symm s = σ.symm s := by rw [Equiv.symm_apply_eq, he]
    rw [he', ← mask_apply_of_mem u hrN, hN, mask_apply_of_mem u' hrN]
  ext s
  by_cases hs : s ∈ N
  · simp only [mask_apply_of_mem _ hs, permOp_apply]
    by_cases hr : π.symm s ∈ B
    · exact key hv hv' hN hπ hπ' hagree s hs hr
    · by_cases hr' : π'.symm s ∈ B
      · exact (key hv' hv hN.symm hπ' hπ (fun r h1 h2 h3 => (hagree r h1 h2 h3.symm).symm) s hs
          hr').symm
      · rw [hv _ hr, hv' _ hr']
  · simp [hs]

/-- **A measurement splits by a function of the outcome.** -/
theorem prob_eq_sum_fiber {ι κ' : Type*} [Fintype ι] [Fintype κ'] [DecidableEq κ']
    (B : Set ι) (g : ι → κ') (v : QState ι) :
    prob B v = ∑ c, prob (B ∩ g ⁻¹' {c}) v := by
  classical
  simp only [prob, norm_mask_sq]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (· ∈ B)) (t := univ) (g := g)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun c _ => sum_congr ?_ fun _ _ => rfl
  ext i
  simp [and_comm]

end Mask

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] {Ω : Type*}
  [AddGroup Y] {Q : ℕ}

/-! ### Slots on reachable states -/

section Slots

variable (E : Env Ω Req A X Y Q)

/-- A slot from slot `m` on is the identity. -/
theorem eventPerm_of_le (ω : Ω) {k : ℕ} (hk : m ≤ k) (r : GameReg W n X Y Req A m) :
    D.eventPerm E ω k r = r := by
  simp [eventPerm, not_lt.2 hk]

/-- A query slot applies the oracle in force to every query register. -/
theorem eventPerm_of_query (ω : Ω) {k : ℕ} (hk : k < m) {r : GameReg W n X Y Req A m}
    (hkind : D.kind r.workspace = false) :
    D.eventPerm E ω k r =
      (r.1, fun i => ((r.2 i).1, (r.2 i).2 + E.oracle ω (splitLogs r).2 (r.2 i).1)) := by
  simp [eventPerm, hk, Env.requestPerm, copyPerm_apply, respondPerm_apply, hkind,
    Env.oraclePerm, splitLogs]

/-- The request of slot `k` on a request branch of a reachable state logs the request and writes
its answer after the branch's earlier requests. -/
theorem requestPerm_of_request (ω : Ω) {k : ℕ} (hk : k < m) {r : GameReg W n X Y Req A m}
    (hr : r ∈ logsIn (reachableLogs k)) (hkind : D.kind r.workspace = true) :
    E.requestPerm D.kind ω ⟨k, hk⟩ r = ((r.workspace, r.request,
      Equiv.swap none (E.answerAfter ω (requests (splitLogs r).2) r.request) r.response,
      Function.update r.logs ⟨k, hk⟩ (some r.request)), r.2) := by
  have hblank : r.logs ⟨k, hk⟩ = none := hr ⟨k, hk⟩ le_rfl
  have hreq : requestsBefore (Function.update r.logs ⟨k, hk⟩ (some r.request)) k =
      requests (splitLogs r).2 := by
    rw [requests_eq_requestsBefore hr]
    exact requestsBefore_congr fun k' hk' =>
      Function.update_of_ne (fun e => by subst e; simp at hk') _ _
  simp only [Env.requestPerm, Equiv.prodCongr_apply, Equiv.trans_apply,
    copyPerm_apply, hkind, ite_true, hblank, Equiv.swap_apply_left, Prod.map, Equiv.refl_apply,
    respondPerm_apply, Env.answer, Function.update_self, Option.elim, hreq]

/-- The request of slot `k` is the identity on a query branch. -/
theorem requestPerm_of_query (ω : Ω) {k : ℕ} (hk : k < m) {r : GameReg W n X Y Req A m}
    (hkind : D.kind r.workspace = false) : E.requestPerm D.kind ω ⟨k, hk⟩ r = r := by
  simp only [Env.requestPerm, Equiv.prodCongr_apply, Equiv.trans_apply, Prod.map,
    Equiv.refl_apply, copyPerm_apply, hkind, Bool.false_eq_true, ite_false, respondPerm_apply]

theorem eventPerm_of_lt (ω : Ω) {k : ℕ} (hk : k < m) (r : GameReg W n X Y Req A m) :
    D.eventPerm E ω k r = E.oraclePerm D.kind ω (E.requestPerm D.kind ω ⟨k, hk⟩ r) := by
  simp [eventPerm, hk]

/-- The request of slot `k` and the whole slot leave the same logs. -/
theorem logs_requestPerm (ω : Ω) {k : ℕ} (hk : k < m) (r : GameReg W n X Y Req A m) :
    (splitLogs (E.requestPerm D.kind ω ⟨k, hk⟩ r)).2 = (splitLogs (D.eventPerm E ω k r)).2 := by
  rw [D.eventPerm_of_lt E ω hk, Env.logs_oraclePerm]

/-- A request slot on a reachable state logs the request and writes its answer after the
branch's earlier requests. -/
theorem eventPerm_of_request (ω : Ω) {k : ℕ} (hk : k < m) {r : GameReg W n X Y Req A m}
    (hr : r ∈ logsIn (reachableLogs k)) (hkind : D.kind r.workspace = true) :
    D.eventPerm E ω k r = ((r.workspace, r.request,
      Equiv.swap none (E.answerAfter ω (requests (splitLogs r).2) r.request) r.response,
      Function.update r.logs ⟨k, hk⟩ (some r.request)), r.2) := by
  rw [D.eventPerm_of_lt E ω hk, D.requestPerm_of_request E ω hk hr hkind]
  simp [Env.oraclePerm, hkind]

/-- On a reachable state, two environments give the same slot permutation if they have the same
oracle in force on a query branch and the same answer on a request branch. -/
theorem eventPerm_eq_of_agree {Ω' : Type*} (E' : Env Ω' Req A X Y Q) {ω : Ω} {ω' : Ω'} {k : ℕ}
    {r : GameReg W n X Y Req A m} (hr : r ∈ logsIn (reachableLogs k))
    (hq : D.kind r.workspace = false → E.oracle ω (splitLogs r).2 = E'.oracle ω' (splitLogs r).2)
    (ha : D.kind r.workspace = true → E.answerAfter ω (requests (splitLogs r).2) r.request =
      E'.answerAfter ω' (requests (splitLogs r).2) r.request) :
    D.eventPerm E ω k r = D.eventPerm E' ω' k r := by
  by_cases hk : k < m
  · cases h : D.kind r.workspace
    · rw [D.eventPerm_of_query E ω hk h, D.eventPerm_of_query E' ω' hk h, hq h]
    · rw [D.eventPerm_of_request E ω hk hr h, D.eventPerm_of_request E' ω' hk hr h, ha h]
  · rw [D.eventPerm_of_le E ω (not_lt.1 hk), D.eventPerm_of_le E' ω' (not_lt.1 hk)]

/-- On a reachable state, a slot appends the request to the branch's requests on a request
branch and keeps them otherwise. -/
theorem requests_eventPerm (ω : Ω) {k : ℕ} {r : GameReg W n X Y Req A m}
    (hr : r ∈ logsIn (reachableLogs k)) :
    requests (splitLogs (D.eventPerm E ω k r)).2 =
      if D.kind r.workspace = true ∧ k < m then requests (splitLogs r).2 ++ [r.request]
      else requests (splitLogs r).2 := by
  by_cases hk : k < m
  · cases h : D.kind r.workspace
    · rw [D.eventPerm_of_query E ω hk h]
      simp [splitLogs]
    · rw [D.eventPerm_of_request E ω hk hr h]
      simp only [splitLogs, Equiv.coe_fn_mk, hk, and_self, ite_true]
      rw [requests_update (lg := r.logs) (k := ⟨k, hk⟩) (fun k' hk' => hr k' hk'.le)]
      exact congrArg (· ++ [r.request]) (requests_eq_requestsBefore (lg := r.logs) hr).symm
  · rw [D.eventPerm_of_le E ω (not_lt.1 hk)]
    simp [hk]

end Slots

/-! ### The part of the game on a set of logs -/

/-- **The part of the game on a set of logs `N`.** If no slot moves a reachable state with logs
outside `N` into `N`, and the two environments give the same slot permutation on every reachable
state with logs in `N` that one of them keeps in `N`, then the game states have the same part on
`N`. -/
theorem mask_stage_eq_of_eventPerm (E : Env Ω Req A X Y Q) {Ω' : Type*} (E' : Env Ω' Req A X Y Q)
    {ω : Ω} {ω' : Ω'} (N : Set (LogReg Req m))
    (hclosed : ∀ k (r : GameReg W n X Y Req A m), r ∈ logsIn (reachableLogs k) → r ∉ logsIn N →
      D.eventPerm E ω k r ∉ logsIn N ∧ D.eventPerm E' ω' k r ∉ logsIn N)
    (hagree : ∀ k (r : GameReg W n X Y Req A m), r ∈ logsIn (reachableLogs k) → r ∈ logsIn N →
      D.eventPerm E ω k r ∈ logsIn N ∨ D.eventPerm E' ω' k r ∈ logsIn N →
      D.eventPerm E ω k r = D.eventPerm E' ω' k r) :
    ∀ k, mask (logsIn N) (D.stage E ω k) = mask (logsIn N) (D.stage E' ω' k)
  | 0 => rfl
  | k + 1 => by
    simp only [stage, hybrid_succ]
    rw [liftedStep, mask_logControlled, mask_logControlled]
    congr 1
    exact mask_permOp_eq_of_agree (D.stage_supported E ω k) (D.stage_supported E' ω' k)
      (mask_stage_eq_of_eventPerm E E' N hclosed hagree k) (fun r hr hN => (hclosed k r hr hN).1)
      (fun r hr hN => (hclosed k r hr hN).2) (hagree k)

/-! ### The game as an oracle algorithm -/

section GameAlg

variable (E : Env Ω Req A X Y Q)
  (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))

/-- The oracle function of slot permutations on tape `ω`: the oracle in force on the query
branches, the zero function on the request branches. -/
def _root_.GordieHowe.Quantum.Env.oracleFn (E : Env Ω Req A X Y Q) (kind : W → Bool) (ω : Ω) :
    W × Req × Option A × LogReg Req m → X → Y :=
  fun s => if kind s.1 then 0 else E.oracle ω s.2.2.2

theorem _root_.GordieHowe.Quantum.Env.oraclePerm_eq (E : Env Ω Req A X Y Q) (kind : W → Bool) (ω : Ω) :
    E.oraclePerm (n := n) (m := m) kind ω = queryPermOf (E.oracleFn kind ω) :=
  rfl

/-- The final unitary of the game on tape `ω`: `post` of the oracle in force, controlled by the
logs. -/
noncomputable def postOp (ω : Ω) :
    QState (GameReg W n X Y Req A m) ≃ₗᵢ[ℂ] QState (GameReg W n X Y Req A m) :=
  logControlled fun lg => post (E.oracle ω lg)

/-- The `t`-th unitary of the oracle algorithm on tape `ω`: the distinguisher's step `t`, then the
request of slot `t`; after the last slot, `post`. -/
noncomputable def gameStep (ω : Ω) (t : ℕ) :
    QState (GameReg W n X Y Req A m) ≃ₗᵢ[ℂ] QState (GameReg W n X Y Req A m) :=
  if h : t < m then (D.liftedStep t).trans (permOp (E.requestPerm D.kind ω ⟨t, h⟩))
  else (D.liftedStep t).trans (postOp E post ω)

/-- **The game as an oracle algorithm.** Its input is the tape, its oracle steps are the `m`
slots, and its accepting set is the distinguisher's on the logs in `L`. -/
noncomputable def gameAlg (L : Set (LogReg Req m)) :
    OracleAlg Ω (GameReg W n X Y Req A m) m where
  init _ := D.gameInit
  norm_init _ := D.norm_gameInit
  step ω t := D.gameStep E post ω t
  accept _ := D.gameAccept ∩ logsIn L

/-- The states of the oracle algorithm of `E` run with the oracle function of `E'`, before each
oracle step, when the two environments give the same answers on tape `ω`: the game state against
`E'` after the request of the slot. -/
theorem gameAlg_stage (E' : Env Ω Req A X Y Q) (L : Set (LogReg Req m)) (ω : Ω)
    (hans : ∀ (lg : LogReg Req m) k, E.answer ω lg k = E'.answer ω lg k) :
    ∀ k (hk : k < m), (D.gameAlg E post L).stage (queryPermOf (E'.oracleFn D.kind ω)) ω k =
      permOp (E.requestPerm D.kind ω ⟨k, hk⟩) (D.stage E' ω k) := by
  set A := D.gameAlg E post L
  have hreq : ∀ k : Fin m, E.requestPerm (n := n) D.kind ω k = E'.requestPerm D.kind ω k :=
    fun k => by simp only [Env.requestPerm, funext fun lg => hans lg k]
  have hstep : ∀ t (ht : t < m + 1), A.stepAt ω t = D.gameStep E post ω t := fun t ht => by
    rw [OracleAlg.stepAt_of_lt _ ht]
    rfl
  intro k
  induction k with
  | zero =>
    intro hk
    rw [OracleAlg.stage, hybrid_zero, hstep 0 (by omega), gameStep, dif_pos hk]
    rfl
  | succ k ih =>
    intro hk
    rw [OracleAlg.stage, hybrid_succ, ← OracleAlg.stage, ih (by omega), hstep _ (by omega),
      gameStep, dif_pos hk, LinearIsometryEquiv.trans_apply, D.stage_succ, eventPerm,
      dif_pos (show k < m by omega), permOp_trans]
    simp only [hreq, Env.oraclePerm_eq]

/-- **The bridge.** If `E` and `E'` give the same answers on tape `ω`, and the same oracle on the
logs in `L`, the oracle algorithm of `E` run with the oracle function of `E'` accepts with the
probability of the game against `E'` restricted to `L`. -/
theorem acceptProb_gameAlg (E' : Env Ω Req A X Y Q) (L : Set (LogReg Req m)) (ω : Ω)
    (hans : ∀ (lg : LogReg Req m) k, E.answer ω lg k = E'.answer ω lg k)
    (hL : ∀ lg ∈ L, E.oracle ω lg = E'.oracle ω lg) :
    (D.gameAlg E post L).acceptProb (queryPermOf (E'.oracleFn D.kind ω)) ω =
      D.acceptProbOnAt E' post L ω := by
  set A := D.gameAlg E post L
  set π := queryPermOf (n := n) (E'.oracleFn D.kind ω)
  have hreq : ∀ k : Fin m, E.requestPerm (n := n) D.kind ω k = E'.requestPerm D.kind ω k :=
    fun k => by simp only [Env.requestPerm, funext fun lg => hans lg k]
  have hstep : ∀ t (ht : t < m + 1), A.stepAt ω t = D.gameStep E post ω t := fun t ht => by
    rw [OracleAlg.stepAt_of_lt _ ht]
    rfl
  have hlt := D.gameAlg_stage E post E' L ω hans
  have hfin : A.final π ω = postOp E post ω (D.run E' ω) := by
    rw [OracleAlg.final, run]
    cases m with
    | zero =>
      rw [OracleAlg.stage, hybrid_zero, hstep 0 (by omega), gameStep, dif_neg (lt_irrefl 0)]
      rfl
    | succ k =>
      rw [OracleAlg.stage, hybrid_succ, ← OracleAlg.stage, hlt k (by omega), hstep _ (by omega),
        gameStep, dif_neg (lt_irrefl _), LinearIsometryEquiv.trans_apply, D.stage_succ,
        eventPerm, dif_pos (show k < k + 1 by omega), permOp_trans]
      simp only [hreq, π, Env.oraclePerm_eq]
  rw [OracleAlg.acceptProb, hfin, acceptProbOnAt, final]
  change prob (D.gameAccept ∩ logsIn L) _ = prob (D.gameAccept ∩ logsIn L) _
  rw [prob_inter_eq_prob_mask, prob_inter_eq_prob_mask, postOp, mask_logControlled,
    mask_logControlled]
  congr 1
  exact Supported.logControlled_eq (fun r hr => mask_apply_of_notMem _ hr) fun lg hlg => by
    rw [hL lg hlg]

theorem acceptProb_gameAlg_self (L : Set (LogReg Req m)) (ω : Ω) :
    (D.gameAlg E post L).acceptProb (queryPermOf (E.oracleFn D.kind ω)) ω =
      D.acceptProbOnAt E post L ω :=
  D.acceptProb_gameAlg E post E L ω (fun _ _ => rfl) fun _ _ => rfl

end GameAlg

/-! ### Branches that made a request -/

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req]
  [DecidableEq A] [AddGroup Y] in
/-- The logs of the branches that made request number `j`. -/
def _root_.GordieHowe.Quantum.madeLogs (j : ℕ) : Set (LogReg Req m) :=
  {lg | j < (requests lg).length}

/-- On reachable states, a slot permutation keeps a made request made. -/
theorem mem_madeLogs_eventPerm (E : Env Ω Req A X Y Q) (ω : Ω) {j k : ℕ}
    {r : GameReg W n X Y Req A m} (hr : r ∈ logsIn (reachableLogs k))
    (hj : r ∈ logsIn (madeLogs j)) : D.eventPerm E ω k r ∈ logsIn (madeLogs j) := by
  simp only [mem_logsIn, madeLogs, Set.mem_ofPred_eq] at hj ⊢
  rw [D.requests_eventPerm E ω hr]
  split_ifs
  · rw [List.length_append]
    omega
  · exact hj

/-- A request slot on a reachable state with `j` earlier requests makes request number `j`. -/
theorem mem_madeLogs_eventPerm_of_request (E : Env Ω Req A X Y Q) (ω : Ω) {j k : ℕ} (hk : k < m)
    {r : GameReg W n X Y Req A m} (hr : r ∈ logsIn (reachableLogs k)) (hkind : D.kind r.workspace = true)
    (hj : j = (requests (splitLogs r).2).length) : D.eventPerm E ω k r ∈ logsIn (madeLogs j) := by
  simp only [mem_logsIn, madeLogs, Set.mem_ofPred_eq]
  rw [D.requests_eventPerm E ω hr, if_pos ⟨hkind, hk⟩, List.length_append, List.length_singleton]
  omega

/-- **The game on the branches that have not made request `j`.** If `E` at `ω` and `E'` at `ω'`
give the same answers to the requests numbered below `j` and have the same oracle after at most
`j` requests, the game states have the same part on the logs that have not made request `j`. -/
theorem mask_stage_eq_of_agree (E : Env Ω Req A X Y Q) {Ω' : Type*} (E' : Env Ω' Req A X Y Q)
    {ω : Ω} {ω' : Ω'} {j : ℕ}
    (hans : ∀ rs req, rs.length < j → E.answerAfter ω rs req = E'.answerAfter ω' rs req)
    (horacle : ∀ rs, rs.length ≤ j → E.oracleIn ω rs = E'.oracleIn ω' rs) (k : ℕ) :
    mask (logsIn (madeLogs j)ᶜ) (D.stage E ω k) = mask (logsIn (madeLogs j)ᶜ) (D.stage E' ω' k) := by
  refine D.mask_stage_eq_of_eventPerm E E' _ (fun k r hr hN => ?_) (fun k r hr hN himg => ?_) k
  · simp only [mem_logsIn, Set.mem_compl_iff, not_not] at hN ⊢
    exact ⟨D.mem_madeLogs_eventPerm E ω hr hN, D.mem_madeLogs_eventPerm E' ω' hr hN⟩
  · simp only [mem_logsIn, Set.mem_compl_iff, madeLogs, Set.mem_ofPred_eq, not_lt] at hN
    by_cases hk : k < m
    · refine D.eventPerm_eq_of_agree E E' hr (fun _ => horacle _ hN) fun hkind => ?_
      rcases hN.lt_or_eq with hlt | heq
      · exact hans _ _ hlt
      · exfalso
        rcases himg with h | h
        · exact h (D.mem_madeLogs_eventPerm_of_request E ω hk hr hkind heq.symm)
        · exact h (D.mem_madeLogs_eventPerm_of_request E' ω' hk hr hkind heq.symm)
    · rw [D.eventPerm_of_le E ω (not_lt.1 hk), D.eventPerm_of_le E' ω' (not_lt.1 hk)]

/-- The final states have the same part on `N` if the runs do and the oracles in force agree on
the logs in `N`. -/
theorem mask_final_eq (E : Env Ω Req A X Y Q) {Ω' : Type*} (E' : Env Ω' Req A X Y Q)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    {ω : Ω} {ω' : Ω'} {N : Set (LogReg Req m)}
    (hrun : mask (logsIn N) (D.run E ω) = mask (logsIn N) (D.run E' ω'))
    (horacle : ∀ lg ∈ N, E.oracle ω lg = E'.oracle ω' lg) :
    mask (logsIn N) (D.final E post ω) = mask (logsIn N) (D.final E' post ω') := by
  rw [final, final, mask_logControlled, mask_logControlled, hrun]
  exact Supported.logControlled_eq (fun r hr => mask_apply_of_notMem _ hr) fun lg hlg => by
    rw [horacle lg hlg]

/-- The acceptance probability on the logs in `L ∩ N` depends only on the part of the final
state on `N`. -/
theorem acceptProbOnAt_inter_eq (E : Env Ω Req A X Y Q) {Ω' : Type*} (E' : Env Ω' Req A X Y Q)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    {ω : Ω} {ω' : Ω'} {N : Set (LogReg Req m)}
    (h : mask (logsIn N) (D.final E post ω) = mask (logsIn N) (D.final E' post ω'))
    (L : Set (LogReg Req m)) :
    D.acceptProbOnAt E post (L ∩ N) ω = D.acceptProbOnAt E' post (L ∩ N) ω' := by
  have hset : D.gameAccept ∩ logsIn (L ∩ N) =
      (D.gameAccept ∩ logsIn L) ∩ logsIn (W := W) (n := n) (X := X) (Y := Y) (A := A) N := by
    ext r
    simp [Set.mem_inter_iff, and_assoc]
  rw [acceptProbOnAt, acceptProbOnAt, hset, prob_inter_eq_prob_mask _ (logsIn N),
    prob_inter_eq_prob_mask _ (logsIn N), h]

/-- Two environments that agree before request `j` (`mask_stage_eq_of_agree`) give the same
acceptance probability on the branches that never make request `j`. -/
theorem acceptProbOnAt_notMade_eq (E : Env Ω Req A X Y Q) {Ω' : Type*} (E' : Env Ω' Req A X Y Q)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    {ω : Ω} {ω' : Ω'} {j : ℕ}
    (hans : ∀ rs req, rs.length < j → E.answerAfter ω rs req = E'.answerAfter ω' rs req)
    (horacle : ∀ rs, rs.length ≤ j → E.oracleIn ω rs = E'.oracleIn ω' rs)
    (L : Set (LogReg Req m)) :
    D.acceptProbOnAt E post (L ∩ (madeLogs j)ᶜ) ω =
      D.acceptProbOnAt E' post (L ∩ (madeLogs j)ᶜ) ω' :=
  D.acceptProbOnAt_inter_eq E E' post (D.mask_final_eq E E' post
    (D.mask_stage_eq_of_agree E E' hans horacle m) fun lg hlg => by
      simp only [Set.mem_compl_iff, madeLogs, Set.mem_ofPred_eq, not_lt] at hlg
      rw [Env.oracle, Env.oracle, horacle _ hlg]) L

/-! ### O2H at one request with a fresh secret -/

variable {V R : Type*} [Fintype V] [Fintype R]
  (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))

omit [Fintype V] [Fintype R] in
/-- The query branches that have not made request `j`, as contents of the work register. -/
def openSet (j : ℕ) : Set (W × Req × Option A × LogReg Req m) :=
  {w | D.kind w.1 = false ∧ (requests w.2.2.2).length ≤ j}

instance (j : ℕ) (w : W × Req × Option A × LogReg Req m) : Decidable (w ∈ D.openSet j) :=
  inferInstanceAs (Decidable (_ ∧ _))

omit [Fintype V] [Fintype R] in
/-- Two oracle functions that agree after more than `j` requests and, after at most `j`
requests, outside `T`, agree outside `T` on the query branches that have not made request `j`. -/
theorem oracleFn_agree {Ω' : Type*} (E E' : Env Ω' Req A X Y Q) {j : ℕ} {ω : Ω'} {T : Set X}
    (hafter : ∀ rs, j < rs.length → E.oracleIn ω rs = E'.oracleIn ω rs)
    (hbefore : ∀ rs, rs.length ≤ j → ∀ x ∉ T, E.oracleIn ω rs x = E'.oracleIn ω rs x)
    (w : W × Req × Option A × LogReg Req m) (x : X)
    (hx : x ∉ (if w ∈ D.openSet j then T else ∅)) :
    E'.oracleFn D.kind ω w x = E.oracleFn D.kind ω w x := by
  classical
  simp only [Env.oracleFn, Env.oracle]
  by_cases hk : D.kind w.1 = true
  · simp [hk]
  · simp only [hk, Bool.false_eq_true, ite_false]
    by_cases hlen : (requests w.2.2.2).length ≤ j
    · have hw : w ∈ D.openSet j := ⟨by simpa using hk, hlen⟩
      simp only [hw, ite_true] at hx
      exact (hbefore _ hlen x hx).symm
    · exact (congrFun (hafter _ (not_le.1 hlen)) x).symm

omit [Fintype V] [Fintype R] in
/-- **The open part of the states before the oracle steps.** If the answers to the requests
numbered below `j` and the oracles after at most `j` requests are the same on two tapes, so is
the part, on the query branches that have not made request `j`, of every state of `gameAlg` just
before an oracle step. -/
theorem mask_pre_eq {Ω' : Type*} (E : Env Ω' Req A X Y Q) (L : Set (LogReg Req m)) {ω ω' : Ω'}
    {j : ℕ} (hans : ∀ rs req, rs.length < j → E.answerAfter ω rs req = E.answerAfter ω' rs req)
    (horacle : ∀ rs, rs.length ≤ j → E.oracleIn ω rs = E.oracleIn ω' rs) (i : Fin m) :
    mask {r : GameReg W n X Y Req A m | r.1 ∈ D.openSet j}
        ((D.gameAlg E post L).pre (queryPermOf (E.oracleFn D.kind ω)) ω i) =
      mask {r : GameReg W n X Y Req A m | r.1 ∈ D.openSet j}
        ((D.gameAlg E post L).pre (queryPermOf (E.oracleFn D.kind ω')) ω' i) := by
  set N := logsIn (W := W) (n := n) (X := X) (Y := Y) (A := A) (madeLogs (m := m) j)ᶜ
  set Mr := {r : GameReg W n X Y Req A m | r.1 ∈ D.openSet j}
  have hMN : Mr ⊆ N := fun r hr => by
    simp only [Mr, Set.mem_ofPred_eq, openSet] at hr
    simp [N, madeLogs, hr.2, splitLogs]
  have hmask : ∀ v : QState (GameReg W n X Y Req A m), mask Mr v = mask Mr (mask N v) := fun v => by
    ext r
    by_cases h : r ∈ Mr
    · rw [mask_apply_of_mem _ h, mask_apply_of_mem _ h, mask_apply_of_mem _ (hMN h)]
    · rw [mask_apply_of_notMem _ h, mask_apply_of_notMem _ h]
  rw [OracleAlg.pre, OracleAlg.pre, D.gameAlg_stage E post E L ω (fun _ _ => rfl) i i.2,
    D.gameAlg_stage E post E L ω' (fun _ _ => rfl) i i.2, hmask, hmask (permOp _ _)]
  congr 1
  have hmade : ∀ ω'' r, r ∈ logsIn (reachableLogs i) → r ∉ N →
      E.requestPerm D.kind ω'' ⟨i, i.2⟩ r ∉ N := fun ω'' r hr hrN => by
    simp only [N, mem_logsIn, Set.mem_compl_iff, not_not] at hrN ⊢
    rw [D.logs_requestPerm E ω'' i.2]
    exact D.mem_madeLogs_eventPerm E ω'' hr hrN
  refine mask_permOp_eq_of_agree (D.stage_supported E ω i) (D.stage_supported E ω' i)
    (D.mask_stage_eq_of_agree E E hans horacle i) (hmade ω) (hmade ω') ?_
  intro r hr hrN himg
  cases hkind : D.kind r.workspace
  · rw [D.requestPerm_of_query E _ i.2 hkind, D.requestPerm_of_query E _ i.2 hkind]
  · rw [D.requestPerm_of_request E _ i.2 hr hkind, D.requestPerm_of_request E _ i.2 hr hkind]
    simp only [N, mem_logsIn, Set.mem_compl_iff, madeLogs, Set.mem_ofPred_eq, not_lt] at hrN
    rcases hrN.lt_or_eq with hlt | heq
    · rw [hans _ _ hlt]
    · exfalso
      have himade : ∀ ω'', E.requestPerm D.kind ω'' ⟨i, i.2⟩ r ∉ N := fun ω'' h => by
        have := D.mem_madeLogs_eventPerm_of_request E ω'' i.2 hr hkind heq.symm
        simp only [N, mem_logsIn, Set.mem_compl_iff] at h this
        rw [D.logs_requestPerm E ω'' i.2] at h
        exact h this
      rcases himg with h | h
      · exact himade ω h
      · exact himade ω' h

end Distinguisher

end GordieHowe.Quantum
