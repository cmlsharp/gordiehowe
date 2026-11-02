-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.Budget
public import GordieHowe.Model.Quantum.O2H.EventBlocks
public import GordieHowe.Model.Quantum.O2H.RevealedStep

@[expose] public section

/-!
# Splitting a game's run at the slot of a request

Tools for comparing two environments of the pure game (`GordieHowe/Model/Quantum/Pure/Game.lean`)
that differ from request number `e` on.

- `contOp E ω k`: the run from slot `k` on as one unitary; `run_eq_contOp`.
- `acceptWithAt E P ω`: the probability of an event `P` of the distinguisher's outcome, the logs
  and the final oracle in force.
- `evBlock e b`, `blockState E e b ω`: the basis states just before slot `k` that make request
  number `e` with request `req` after the logs `lg`, for the block `b = (k, lg, req)`, and the part
  of the state on them.
- `mask_evLogs_run`: the final state on the block's final logs (`evLogs`,
  `GordieHowe/Model/Quantum/O2H/EventBlocks.lean`) is the run from slot `k` of the block's state.
- `contOp_eq_of_evBlock`: from a block on, the run reads the environment only at the block's
  request and after it.
- `blockState_eq_of_agree`, `mask_run_notMade_eq`: environments that agree before request `e` have
  the same block states and the same final state on the branches that never make request `e`.
- `stage_congr`, `contOp_congr`: environments with the same answers and oracles in force run the
  same.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] {Ω : Type*}
  [AddGroup Y] {Q : ℕ} {St St' : Type _} [OracleState St X Y] [OracleState St' X Y]

/-! ### The run from a slot on -/

/-- **The run from slot `k` on**: slot `k`, the step after it, …, slot `m − 1`, the last step. -/
noncomputable def contOp (E : Env Ω Req A X Y Q St) (ω : Ω) (k : ℕ) :
    QState (GameReg W n X Y Req A m) ≃ₗᵢ[ℂ] QState (GameReg W n X Y Req A m) :=
  if h : k < m then
    ((permOp (D.eventPerm E ω k)).trans (D.liftedStep (k + 1))).trans (contOp E ω (k + 1))
  else LinearIsometryEquiv.refl ℂ _
termination_by m - k

/-- **The run is the run from slot `k` on, applied to the state before slot `k`.** -/
theorem contOp_of_lt (E : Env Ω Req A X Y Q St) (ω : Ω) {k : ℕ} (hk : k < m)
    (v : QState (GameReg W n X Y Req A m)) :
    D.contOp E ω k v = D.contOp E ω (k + 1) (D.liftedStep (k + 1) (permOp (D.eventPerm E ω k) v)) := by
  rw [contOp]
  simp only [hk, ↓reduceDIte]
  rfl

/-- From slot `m` on, the run from a slot is the identity. -/
theorem contOp_of_le (E : Env Ω Req A X Y Q St) (ω : Ω) {k : ℕ} (hk : m ≤ k)
    (v : QState (GameReg W n X Y Req A m)) : D.contOp E ω k v = v := by
  have hk' : ¬ k < m := not_lt.2 hk
  rw [contOp]
  simp only [hk', ↓reduceDIte]
  rfl

/-- **The run is the run from slot `k` on, applied to the state before slot `k`.** -/
theorem run_eq_contOp (E : Env Ω Req A X Y Q St) (ω : Ω) {k : ℕ} (hk : k ≤ m) :
    D.run E ω = D.contOp E ω k (D.stage E ω k) := by
  induction h : m - k generalizing k with
  | zero =>
    obtain rfl : k = m := by omega
    rw [contOp_of_le _ _ _ le_rfl]
    rfl
  | succ d ih =>
    have hk' : k < m := by omega
    rw [contOp_of_lt _ _ _ hk', ← stage_succ]
    exact ih (by omega) (by omega)

/-- The run from slot `j` keeps a support `logsIn L` that every slot from `j₀` on keeps. -/
theorem contOp_supported (E : Env Ω Req A X Y Q St) (ω : Ω) (L : Set (LogReg Req m)) (j₀ : ℕ)
    (hL : ∀ j, j₀ ≤ j → ∀ r ∈ logsIn (W := W) (n := n) (X := X) (Y := Y) (A := A) L,
      D.eventPerm E ω j r ∈ logsIn L) :
    ∀ j, j₀ ≤ j → ∀ v, Supported (logsIn L) v → Supported (logsIn L) (D.contOp E ω j v) := by
  intro j hj v hv
  induction h : m - j generalizing j v with
  | zero => rwa [D.contOp_of_le E ω (k := j) (by omega)]
  | succ d ih =>
    rw [D.contOp_of_lt E ω (k := j) (by omega)]
    refine ih (j + 1) (by omega) _ ?_ (by omega)
    exact (hv.permOp (hL j hj)).logControlled _

/-- Two runs from slot `j` agree on a state supported on reachable logs in `L` when `L` is kept
by every slot from `j₀` on and the slots agree there. -/
theorem contOp_eq_of_supported (E : Env Ω Req A X Y Q St) {Ω' : Type*}
    (E' : Env Ω' Req A X Y Q St') {ω : Ω} {ω' : Ω'} (L : Set (LogReg Req m)) (j₀ : ℕ)
    (hL : ∀ j, j₀ ≤ j → ∀ r ∈ logsIn (W := W) (n := n) (X := X) (Y := Y) (A := A) L,
      D.eventPerm E ω j r ∈ logsIn L)
    (hag : ∀ j, j₀ ≤ j → ∀ r ∈ logsIn (W := W) (n := n) (X := X) (Y := Y) (A := A)
      (reachableLogs j ∩ L), D.eventPerm E ω j r = D.eventPerm E' ω' j r) :
    ∀ j, j₀ ≤ j → ∀ v, Supported (logsIn (reachableLogs j ∩ L)) v →
      D.contOp E ω j v = D.contOp E' ω' j v := by
  intro j hj v hv
  induction h : m - j generalizing j v with
  | zero => rw [D.contOp_of_le E ω (k := j) (by omega), D.contOp_of_le E' ω' (k := j) (by omega)]
  | succ d ih =>
    rw [D.contOp_of_lt E ω (k := j) (by omega), D.contOp_of_lt E' ω' (k := j) (by omega),
      ← hv.permOp_eq (hag j hj)]
    refine ih (j + 1) (by omega) _ ?_ (by omega)
    refine (hv.permOp fun r hr => ?_).logControlled _
    exact ⟨D.eventPerm_mem_reachableSet E ω (r := r) hr.1, hL j hj r hr.2⟩

/-! ### Events of the output, the logs and the final oracle -/

/-- **The probability of an event of the output, the logs and the final oracle in force**: the
final measurement gives a distinguisher outcome `d` and logs `lg` with `P d lg (E.oracle ω lg)`. -/
noncomputable def acceptWithAt (E : Env Ω Req A X Y Q St)
    (P : DReg W n X Y Req A → LogReg Req m → (X → Y) → Prop) (ω : Ω) : ℝ :=
  prob {r | P (splitLogs r).1 (splitLogs r).2 (E.oracle ω (splitLogs r).2)} (D.run E ω)

/-! ### Event blocks -/

/-- **An event block** `(k, lg, req)` for request number `e`: the basis states just before slot
`k`, with logs `lg` holding `e` requests, that request `req` at slot `k`; empty unless `lg` holds `e` requests and is blank from slot `k`
on. -/
def evBlock (e : ℕ) (b : Fin m × LogReg Req m × Req) : Set (GameReg W n X Y Req A m) :=
  {r | (splitLogs r).2 = b.2.1 ∧ D.kind r.workspace = true ∧ r.request = b.2.2 ∧
    (requests b.2.1).length = e ∧ ∀ k' : Fin m, b.1 ≤ k' → b.2.1 k' = none}

/-- **The state of an event block** at a tape: the part of the state before slot `k` on the
block. -/
noncomputable def blockState (E : Env Ω Req A X Y Q St) (e : ℕ) (b : Fin m × LogReg Req m × Req)
    (ω : Ω) : QState (GameReg W n X Y Req A m) :=
  mask (D.evBlock e b) (D.stage E ω b.1)


/-! ### Splitting the run at an event block -/

/-- Environments with the same answers and oracles in force give the same slot permutations. -/
theorem eventPerm_congr (E : Env Ω Req A X Y Q St) {Ω' : Type*} {Q' : ℕ} (E' : Env Ω' Req A X Y Q' St')
    {ω : Ω} {ω' : Ω'} (hans : ∀ rs req, E.answerAfter ω rs req = E'.answerAfter ω' rs req)
    (horc : ∀ rs, (OracleState.toOracle (E.oracleIn ω rs) : X → Y) =
      OracleState.toOracle (E'.oracleIn ω' rs)) (k : ℕ) :
    D.eventPerm E ω k = D.eventPerm E' ω' k := by
  have ha : E.answerAfter ω = E'.answerAfter ω' := by
    funext rs req
    exact hans rs req
  unfold eventPerm Env.requestPerm Env.oraclePerm Env.answer Env.oracle
  simp only [ha, horc]

/-- **Runs that agree everywhere**: two environments with the same answers and oracles in force
after every list of requests give the same states. -/
theorem stage_congr (E : Env Ω Req A X Y Q St) {Ω' : Type*} {Q' : ℕ} (E' : Env Ω' Req A X Y Q' St')
    {ω : Ω} {ω' : Ω'} (hans : ∀ rs req, E.answerAfter ω rs req = E'.answerAfter ω' rs req)
    (horc : ∀ rs, (OracleState.toOracle (E.oracleIn ω rs) : X → Y) =
      OracleState.toOracle (E'.oracleIn ω' rs)) (k : ℕ) :
    D.stage E ω k = D.stage E' ω' k := by
  have h : (fun j => permOp (D.eventPerm E ω j)) = fun j => permOp (D.eventPerm E' ω' j) := by
    funext j
    rw [D.eventPerm_congr E E' hans horc]
  unfold stage
  rw [h]

/-- `stage_congr` for the run from a slot on. -/
theorem contOp_congr (E : Env Ω Req A X Y Q St) {Ω' : Type*} {Q' : ℕ} (E' : Env Ω' Req A X Y Q' St')
    {ω : Ω} {ω' : Ω'} (hans : ∀ rs req, E.answerAfter ω rs req = E'.answerAfter ω' rs req)
    (horc : ∀ rs, (OracleState.toOracle (E.oracleIn ω rs) : X → Y) =
      OracleState.toOracle (E'.oracleIn ω' rs)) (k : ℕ) :
    D.contOp E ω k = D.contOp E' ω' k := by
  ext1 v
  induction h : m - k generalizing k v with
  | zero => rw [D.contOp_of_le E ω (k := k) (by omega), D.contOp_of_le E' ω' (k := k) (by omega)]
  | succ d ih =>
    rw [D.contOp_of_lt E ω (k := k) (by omega), D.contOp_of_lt E' ω' (k := k) (by omega),
      D.eventPerm_congr E E' hans horc]
    exact ih (k + 1) _ (by omega)

/-- A slot `j` changes no log other than log `j`. -/
theorem logs_eventPerm_of_ne (E : Env Ω Req A X Y Q St) (ω : Ω) {j : ℕ} {k' : Fin m}
    (hj : (k' : ℕ) ≠ j) (r : GameReg W n X Y Req A m) :
    (splitLogs (D.eventPerm E ω j r)).2 k' = (splitLogs r).2 k' := by
  by_cases hk : j < m
  · rw [← D.logs_requestPerm E ω hk, Env.logs_requestPerm]
    split_ifs
    · exact Function.update_of_ne (fun h => hj (by rw [h])) _ _
    · rfl
  · rw [D.eventPerm_of_le E ω (not_lt.1 hk)]

omit [Fintype Req] [DecidableEq Req] in
/-- Membership in `evLogs e b` reads only the logs up to slot `b.1`. -/
theorem mem_evLogs_iff_of_agree {e : ℕ} {b : Fin m × LogReg Req m × Req} {lg lg' : LogReg Req m}
    (h : ∀ k' : Fin m, k' ≤ b.1 → lg k' = lg' k') : lg ∈ evLogs e b ↔ lg' ∈ evLogs e b := by
  simp only [evLogs, Set.mem_ofPred_eq]
  rw [← h b.1 le_rfl]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun k' hk' => (h k' hk'.le).symm.trans (h1 k' hk'), h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun k' hk' => (h k' hk'.le).trans (h1 k' hk'), h2, h3, h4⟩

/-- On a reachable state, slot `b.1` lands in `evLogs e b` exactly from the event block. -/
theorem eventPerm_mem_evLogs_iff (E : Env Ω Req A X Y Q St) (ω : Ω) (e : ℕ)
    (b : Fin m × LogReg Req m × Req) {r : GameReg W n X Y Req A m}
    (hr : r ∈ logsIn (reachableLogs b.1)) :
    D.eventPerm E ω b.1 r ∈ logsIn (evLogs e b) ↔ r ∈ D.evBlock e b := by
  have hk : (b.1 : ℕ) < m := b.1.2
  cases hkind : D.kind r.workspace
  · rw [D.eventPerm_of_query E ω hk hkind]
    constructor
    · intro h
      have h2 := h.2.1
      have hb : r.1.2.2.2 b.1 = none := hr b.1 le_rfl
      simp only [splitLogs, Equiv.coe_fn_mk] at h2
      rw [hb] at h2
      exact absurd h2 (by simp)
    · intro h
      exact absurd h.2.1 (by simp [hkind])
  · rw [D.eventPerm_of_request E ω hk hr hkind]
    simp only [mem_logsIn, splitLogs, Equiv.coe_fn_mk, evLogs, evBlock, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨funext fun k' => ?_, hkind, ?_, h3, h4⟩
      · rcases lt_or_ge k' b.1 with h' | h'
        · rw [← h1 k' h', Function.update_of_ne (ne_of_lt h')]
        · rw [h4 k' h']
          exact hr k' (Fin.le_def.1 h')
      · simpa using h2
    · rintro ⟨h1, -, h2, h3, h4⟩
      refine ⟨fun k' hk' => ?_, ?_, h3, h4⟩
      · rw [Function.update_of_ne (ne_of_lt hk'), ← h1]
      · rw [Function.update_self, h2]

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] in
/-- A mask of a subset absorbs the mask of the superset. -/
theorem mask_mask_of_sub {ι : Type*} [Fintype ι] {S T : Set ι} (h : S ⊆ T) (v : QState ι) :
    mask S (mask T v) = mask S v := by
  ext i
  by_cases hS : i ∈ S
  · simp [hS, h hS]
  · simp [hS]

omit [DecidableEq Req] [DecidableEq A] [AddGroup Y] in
/-- An event block is reachable before its slot. -/
theorem evBlock_subset_reachable (e : ℕ) (b : Fin m × LogReg Req m × Req) :
    D.evBlock e b ⊆ logsIn (reachableLogs b.1) := fun r hr k' hk' => by
  rw [hr.1]
  exact hr.2.2.2.2 k' (Fin.le_def.2 hk')

/-- **The final state on an event block is the run from slot `k` of the block's state.** -/
theorem mask_evLogs_run (E : Env Ω Req A X Y Q St) (ω : Ω) (e : ℕ)
    (b : Fin m × LogReg Req m × Req) :
    mask (logsIn (evLogs e b)) (D.run E ω) = D.contOp E ω b.1 (D.blockState E e b ω) := by
  have hk : (b.1 : ℕ) < m := b.1.2
  rw [D.run_eq_contOp E ω hk.le, contOp_of_lt _ _ _ hk, contOp_of_lt _ _ _ hk]
  set f := (D.liftedStep (b.1 + 1)).trans (D.contOp E ω (b.1 + 1))
  have hc : ∀ L : Set (LogReg Req m), (∀ j, (b.1 : ℕ) + 1 ≤ j → ∀ r ∈ logsIn (W := W) (n := n)
      (X := X) (Y := Y) (A := A) L, D.eventPerm E ω j r ∈ logsIn L) →
      ∀ v, Supported (logsIn L) v → Supported (logsIn L) (f v) := fun L hL v hv =>
    D.contOp_supported E ω L _ hL _ le_rfl _ (hv.logControlled _)
  have hL : ∀ j, (b.1 : ℕ) + 1 ≤ j → ∀ r : GameReg W n X Y Req A m,
      (r ∈ logsIn (evLogs e b) ↔ D.eventPerm E ω j r ∈ logsIn (evLogs e b)) := fun j hj r =>
    (mem_evLogs_iff_of_agree fun k' hk' =>
      (D.logs_eventPerm_of_ne E ω (by have := Fin.le_def.1 hk'; omega) r).symm)
  have := mask_comm_of_supported f (hc _ fun j hj r hr => (hL j hj r).1 hr)
    (fun v hv => (hc (evLogs e b)ᶜ (fun j hj r hr h' => hr ((hL j hj r).2 h')) v hv : _))
    (permOp (D.eventPerm E ω b.1) (D.stage E ω b.1))
  change mask _ (f _) = f _
  rw [this]
  congr 1
  ext s
  obtain ⟨r, rfl⟩ : ∃ r, s = D.eventPerm E ω b.1 r := ⟨_, (Equiv.apply_symm_apply _ s).symm⟩
  simp only [blockState]
  by_cases hr : r ∈ logsIn (reachableLogs b.1)
  · have hs := D.eventPerm_mem_evLogs_iff E ω e b hr
    by_cases hB : r ∈ D.evBlock e b
    · rw [mask_apply_of_mem _ (hs.2 hB), permOp_apply, permOp_apply, Equiv.symm_apply_apply,
        mask_apply_of_mem _ hB]
    · rw [mask_apply_of_notMem _ (fun h => hB (hs.1 h)), permOp_apply, Equiv.symm_apply_apply,
        mask_apply_of_notMem _ hB]
  · have h0 := D.stage_supported E ω b.1 r hr
    rw [permOp_apply, Equiv.symm_apply_apply]
    by_cases hs : D.eventPerm E ω b.1 r ∈ logsIn (evLogs e b)
    · rw [mask_apply_of_mem _ hs, permOp_apply, Equiv.symm_apply_apply, h0]
      by_cases hB : r ∈ D.evBlock e b
      · rw [mask_apply_of_mem _ hB, h0]
      · rw [mask_apply_of_notMem _ hB]
    · rw [mask_apply_of_notMem _ hs]
      by_cases hB : r ∈ D.evBlock e b
      · rw [mask_apply_of_mem _ hB, h0]
      · rw [mask_apply_of_notMem _ hB]

/-- **From an event block on, the run reads the environment only after the block's request**:
two environments that give the same answer to the block's request and the same answers and
oracles in force after every list of requests extending it run the same from slot `k` on, on a
state supported on the block. -/
theorem contOp_eq_of_evBlock (E : Env Ω Req A X Y Q St) {Ω' : Type*}
    (E' : Env Ω' Req A X Y Q St') {ω : Ω} {ω' : Ω'} (e : ℕ) (b : Fin m × LogReg Req m × Req)
    (hev : E.answerAfter ω (requests b.2.1) b.2.2 = E'.answerAfter ω' (requests b.2.1) b.2.2)
    (hans : ∀ rs' req', E.answerAfter ω (requests b.2.1 ++ b.2.2 :: rs') req' =
      E'.answerAfter ω' (requests b.2.1 ++ b.2.2 :: rs') req')
    (horc : ∀ rs', (OracleState.toOracle (E.oracleIn ω (requests b.2.1 ++ b.2.2 :: rs')) : X → Y) =
      OracleState.toOracle (E'.oracleIn ω' (requests b.2.1 ++ b.2.2 :: rs')))
    {v : QState (GameReg W n X Y Req A m)} (hv : Supported (D.evBlock e b) v) :
    D.contOp E ω b.1 v = D.contOp E' ω' b.1 v := by
  have hk : (b.1 : ℕ) < m := b.1.2
  have hB := D.evBlock_subset_reachable e b
  rw [D.contOp_of_lt E ω hk, D.contOp_of_lt E' ω' hk,
    hv.permOp_eq (π' := D.eventPerm E' ω' b.1) fun r hr => D.eventPerm_eq_of_agree E E' (hB hr)
      (fun h => absurd hr.2.1 (by simp [h])) (fun _ => by rw [hr.1, hr.2.2.1]; exact hev)]
  refine D.contOp_eq_of_supported E E' (evLogs e b) (b.1 + 1) (fun j hj r hr => ?_)
    (fun j hj r hr => ?_) _ le_rfl _ ?_
  · exact (mem_evLogs_iff_of_agree fun k' hk' =>
      (D.logs_eventPerm_of_ne E ω (by have := Fin.le_def.1 hk'; omega) r).symm).1 hr
  · obtain ⟨rs', hrs⟩ := requests_of_mem_evLogs hr.2
    refine D.eventPerm_eq_of_agree E E' hr.1 (fun _ => ?_) (fun _ => ?_)
    · simp only [Env.oracle, hrs]
      exact horc rs'
    · rw [hrs]
      exact hans _ _
  · exact (hv.permOp (B' := logsIn (reachableLogs (b.1 + 1) ∩ evLogs e b)) fun r hr =>
      ⟨D.eventPerm_mem_reachableSet E' ω' (hB hr),
      (D.eventPerm_mem_evLogs_iff E' ω' e b (hB hr)).2 hr⟩).logControlled _

/-- **Before request `e`, the block states read the environment only before request `e`.** -/
theorem blockState_eq_of_agree (E : Env Ω Req A X Y Q St) {Ω' : Type*}
    (E' : Env Ω' Req A X Y Q St') {ω : Ω} {ω' : Ω'} {e : ℕ}
    (hans : ∀ rs req, rs.length < e → E.answerAfter ω rs req = E'.answerAfter ω' rs req)
    (horc : ∀ rs : List Req, rs.length ≤ e →
      (OracleState.toOracle (E.oracleIn ω rs) : X → Y) = OracleState.toOracle (E'.oracleIn ω' rs))
    (b : Fin m × LogReg Req m × Req) :
    D.blockState E e b ω = D.blockState E' e b ω' := by
  have hsub : D.evBlock e b ⊆ logsIn (madeLogs e)ᶜ := fun r hr => by
    show ¬ e < (requests (splitLogs r).2).length
    rw [hr.1, hr.2.2.2.1]
    exact lt_irrefl e
  unfold blockState
  rw [← mask_mask_of_sub hsub (D.stage E ω b.1), ← mask_mask_of_sub hsub (D.stage E' ω' b.1),
    D.mask_stage_eq_of_agree E E' hans horc]

/-- **On the branches that never make request `e`, the final states agree** for environments
that agree before request `e`. -/
theorem mask_run_notMade_eq (E : Env Ω Req A X Y Q St) {Ω' : Type*}
    (E' : Env Ω' Req A X Y Q St') {ω : Ω} {ω' : Ω'} {e : ℕ}
    (hans : ∀ rs req, rs.length < e → E.answerAfter ω rs req = E'.answerAfter ω' rs req)
    (horc : ∀ rs : List Req, rs.length ≤ e →
      (OracleState.toOracle (E.oracleIn ω rs) : X → Y) = OracleState.toOracle (E'.oracleIn ω' rs)) :
    mask (logsIn (madeLogs e)ᶜ) (D.run E ω) = mask (logsIn (madeLogs e)ᶜ) (D.run E' ω') :=
  D.mask_stage_eq_of_agree E E' hans horc m

end Distinguisher

end GordieHowe.Quantum
