-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ReqBridge
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeCore

@[expose] public section

/-!
# Replies that read the earlier requests, and reindexing the coins of the replies

A query algorithm with classical request points (`Quantum.ReqQueryAlg`,
`GordieHowe/Model/Quantum/Interactive/CompressedSimReq.lean`) answered by replies that may read
the requests logged before the request point (`ReqQueryAlg.instLog`,
`GordieHowe/Model/Quantum/Interactive/ReqBridge.lean`): the reply at request point `k` to the
request `r` is `a k rs r`, with `rs` the requests of the earlier request points. A challenger whose
coins are indexed by the number of earlier requests of some kind answers this way.

The logs copy every request (deferred measurement), so the branches with different requests do
not interfere, and the part of the simulated state `Sim*` (CMS19 section 3.6) with the logs
holding the requests `L` depends on the replies only through the replies to `L`. So two families of
replies, each drawn from its coins, whose replies to every request pattern have the same law, give
the same coin average of `simLaw` (`ReqQueryAlg.sum_simLaw_instLog_eq`). This reindexes the coins
of a challenger: coins indexed by the number of earlier requests and coins indexed by the step give
the same average when, on every pattern, the coins read are distinct and uniform.

- `requestsBefore_update_self`: filling log `k` leaves the requests before `k` unchanged.
- `ReqQueryAlg.instLog_congr_write`: replies differing only where the writing ignores them give the
  same instance.
- `ReqQueryAlg.preVLog`, `ReqQueryAlg.simStage_eq_preVLog`: the simulated run of the instance
  (with `ReqQueryAlg.simStep_instLog` of `ReqBridgeCore.lean`). `ReqQueryAlg.stageLog_supp`,
  `ReqQueryAlg.preVLog_supp`, `ReqQueryAlg.simStateLog_supp`: after step `k` the logs are filled
  exactly below `k + 1`.
- `ReqQueryAlg.LogsIn`, `ReqQueryAlg.simStateLog_in`: the logged requests are requests of `G`.
- `ReqQueryAlg.RepliesAgree k lg a a'`: the replies `a` and `a'` agree at the requests the logs
  `lg` hold below `k`. `ReqQueryAlg.wsSlice_simStateLog_congr`: then the slices of the simulated
  states at `lg` agree.
- `ReqQueryAlg.simLaw_instLog_eq_sum`: `simLaw` of the instance as a sum over the logs of the Born
  weights of the slices.
- `sum_mul_comp_eq_sum_map`: a coin average of a function of `v c` is the average over the law of
  `v`.
- `ReqQueryAlg.sum_simLaw_instLog_eq` (**the reindexing**).
-/

open Matrix
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-- **Filling log `k` leaves the requests before `k` unchanged.** -/
theorem requestsBefore_update_self {Req : Type} {m : ℕ} (lg : LogReg Req m) (k : Fin m)
    (x : Option Req) : requestsBefore (Function.update lg k x) k = requestsBefore lg k :=
  requestsBefore_congr fun _ hk' => Function.update_of_ne (Fin.ne_of_lt hk') _ _

/-- **A coin average of a function of `v c` is the average over the law of `v`.** -/
theorem sum_mul_comp_eq_sum_map {κ U : Type} [Fintype κ] [Fintype U] [DecidableEq U] (μ : PMF κ)
    (v : κ → U) (F : U → ℝ≥0∞) : ∑ c, μ c * F (v c) = ∑ u, (μ.map v) u * F u := by
  simp only [PMF.map_apply, tsum_fintype (L := .unconditional _), Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single (v c) (fun u _ hu => by simp [hu])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

namespace ReqQueryAlg

variable {X Y Req Resp O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Req] [Fintype Req] {t : ℕ} (G : ReqQueryAlg X Y Req Resp t O)

/-- **Replies that differ only where the writing ignores the reply give the same instance**: if at
every step `k` where `a` and `a'` reply differently the reply written does not matter
(`G.write k x = G.write k y`), the instances are equal. -/
theorem instLog_congr_write {a a' : ℕ → List Req → Req → Option Resp}
    (h : ∀ (k : Fin (t + 1)) (prev : List Req) (r : Req), a k prev r ≠ a' k prev r →
      ∀ x y, G.write k x = G.write k y) :
    G.instLog a = G.instLog a' := by
  have hp : ∀ k, G.reqPermLog a k = G.reqPermLog a' k := by
    intro k
    refine Equiv.ext fun p => ?_
    obtain ⟨w, lg⟩ := p
    change (G.write k (a k (requestsBefore lg k) (G.req k w)) w, _) =
      (G.write k (a' k (requestsBefore lg k) (G.req k w)) w, _)
    by_cases he : a k (requestsBefore lg k) (G.req k w) = a' k (requestsBefore lg k) (G.req k w)
    · rw [he]
    · rw [h k _ _ he (a k (requestsBefore lg k) (G.req k w))
        (a' k (requestsBefore lg k) (G.req k w))]
  have hs : G.instStepLog a = G.instStepLog a' := funext fun k => by
    unfold instStepLog
    rw [hp k]
  unfold instLog
  rw [hs]

end ReqQueryAlg

/-! ### The simulated run of the instance -/

namespace ReqQueryAlg

open GordieHowe.QROM

section Reindex

variable {m t : ℕ} {I J B Req Resp O : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Inhabited Req]
  (e : BitStr I J ≃ B) (G : ReqQueryAlg (Bits m) (BitStr I J) Req Resp t O)

/-- **A unitary on a slice, controlled by the passive factor**, acts on each slice. -/
theorem wsSlice_relabel_controlled {W L : Type} [Fintype W] [DecidableEq W] [Fintype L]
    [DecidableEq L] (U : QState (SimRegister W I J m t) ≃ₗᵢ[ℂ] QState (SimRegister W I J m t))
    (v : QState (SimRegister (W × L) I J m t)) (l : L) :
    wsSlice (relabel (wsSplit W L).symm (controlled (fun _ => U) (relabel (wsSplit W L) v))) l =
      U (wsSlice v l) := by
  ext x
  simp only [wsSlice, relabel_apply, Equiv.symm_symm, Equiv.apply_symm_apply, controlled_apply]

variable (a : ℕ → List Req → Req → Option Resp)

/-- **The instance's simulated run before step `k`**: the initial state with the empty database,
then after step `k` the simulated query. -/
noncomputable def preVLog : ℕ → QState (SimRegister (G.W × LogReg Req (t + 1)) I J m t)
  | 0 => simInit e (G.instLog a)
  | k + 1 => simQuery e (G.instLog a).W t (simStage e (G.instLog a) k)

omit [Fintype Resp] [DecidableEq Resp] [Inhabited Req] in
theorem simStage_eq_preVLog (k : ℕ) :
    simStage e (G.instLog a) k = simStep (G.instLog a) k (preVLog e G a k) := by
  cases k with
  | zero => simp only [simStage, preVLog, Nat.rec_zero]
  | succ k => simp only [simStage, preVLog]

/-- The logs of a basis state of the instance's simulation register. -/
abbrev logsOf (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t) : LogReg Req (t + 1) :=
  (wsSplit G.W (LogReg Req (t + 1)) b).2

/-- **After step `k` the logs are filled exactly below `k + 1`**, if they were filled exactly below
`k` before it. -/
theorem stageLog_supp (k : Fin (t + 1))
    (hpre : ∀ b, preVLog e G a k b ≠ 0 → LogsAt (k : ℕ) (G.logsOf b))
    (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t)
    (hb : simStage e (G.instLog a) k b ≠ 0) : LogsAt ((k : ℕ) + 1) (G.logsOf b) := by
  rw [simStage_eq_preVLog, simStep_instLog] at hb
  refine supp_controlled_ws G _ (fun b'' hb'' => ?_) b hb
  rw [permOp_apply] at hb''
  have h := hpre _ hb''
  obtain ⟨⟨⟨w, lg⟩, qs⟩, sl⟩ := b''
  simp only [logsOf, wsSplit, Equiv.coe_fn_mk, reqPermLogSim, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Prod.map, id] at h ⊢
  set p := (G.reqPermLog a k).symm (w, lg) with hp
  have hlg : lg = Function.update p.2 k (Equiv.swap none (some (G.req k p.1)) (p.2 k)) := by
    have := congrArg Prod.snd ((G.reqPermLog a k).apply_symm_apply (w, lg))
    rw [← hp] at this
    exact this.symm
  have hpk : p.2 k = none := LogsAt.eq_none h
  rw [hlg, hpk, Equiv.swap_apply_left]
  intro j
  by_cases hj : j = k
  · subst hj
    simp
  · rw [Function.update_of_ne hj, ← h j]
    have : (j : ℕ) ≠ k := fun h' => hj (Fin.ext h')
    omega

/-- **The logs of the instance's simulated run before step `k` are filled exactly below `k`.** -/
theorem preVLog_supp (k : ℕ) (hk : k ≤ t + 1) (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t)
    (hb : preVLog e G a k b ≠ 0) : LogsAt k (G.logsOf b) := by
  induction k generalizing b with
  | zero =>
    obtain ⟨⟨⟨w, lg⟩, qs⟩, sl⟩ := b
    have hlg : lg = fun _ => none := by
      by_contra h
      apply hb
      change (G.instLog a).init ((w, lg), qs) * _ = 0
      simp [ReqQueryAlg.instLog, relabel_apply, tensorKet_apply, logSplit, h]
    subst hlg
    intro j
    simp [logsOf, wsSplit]
  | succ k ih =>
    have hk' : k < t + 1 := by omega
    have hq : preVLog e G a (k + 1) = relabel (wsSplit G.W (LogReg Req (t + 1))).symm
        (controlled (fun _ => simQueryIso e G.W) (relabel (wsSplit G.W (LogReg Req (t + 1)))
          (simStage e (G.instLog a) k))) :=
      simQuery_prod e G.W (LogReg Req (t + 1)) (simStage e (G.instLog a) k)
    rw [hq] at hb
    exact supp_controlled_ws G _ (fun b' hb' =>
      stageLog_supp e G a ⟨k, hk'⟩ (fun b'' hb'' => ih (by omega) b'' hb'') b' hb') b hb

/-- **The logs of the instance's simulated state are full.** -/
theorem simStateLog_supp (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t)
    (hb : simState e (G.instLog a) b ≠ 0) : ∀ j, (G.logsOf b j).isSome := fun j =>
  (stageLog_supp e G a (Fin.last t) (fun b' hb' => preVLog_supp e G a t (by omega) b' hb') b hb
    j).1 (by simp only [Fin.val_last]; omega)

/-- **The logged requests are requests of `G`**: a log `j` holding `r` holds `G.req j w` for some
work register `w`. -/
def LogsIn (lg : LogReg Req (t + 1)) : Prop :=
  ∀ j r, lg j = some r → ∃ w, r = G.req j w

/-- **After step `k` the logged requests are requests of `G`**, if they were before it. -/
theorem stageLog_in (k : Fin (t + 1))
    (hpre : ∀ b, preVLog e G a k b ≠ 0 → G.LogsIn (G.logsOf b))
    (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t)
    (hb : simStage e (G.instLog a) k b ≠ 0) : G.LogsIn (G.logsOf b) := by
  rw [simStage_eq_preVLog, simStep_instLog] at hb
  refine supp_controlled_ws G _ (fun b'' hb'' => ?_) b hb
  rw [permOp_apply] at hb''
  have h := hpre _ hb''
  obtain ⟨⟨⟨w, lg⟩, qs⟩, sl⟩ := b''
  simp only [logsOf, wsSplit, Equiv.coe_fn_mk, reqPermLogSim, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Prod.map, id] at h ⊢
  set p := (G.reqPermLog a k).symm (w, lg) with hp
  have hlg : lg = Function.update p.2 k (Equiv.swap none (some (G.req k p.1)) (p.2 k)) := by
    have := congrArg Prod.snd ((G.reqPermLog a k).apply_symm_apply (w, lg))
    rw [← hp] at this
    exact this.symm
  intro j r hr
  rw [hlg] at hr
  by_cases hj : j = k
  · subst hj
    rw [Function.update_self] at hr
    rcases hpk : p.2 j with _ | r'
    · rw [hpk, Equiv.swap_apply_left, Option.some.injEq] at hr
      exact ⟨p.1, hr.symm⟩
    · by_cases hr' : some r' = some (G.req j p.1)
      · rw [hpk, hr', Equiv.swap_apply_right] at hr
        exact absurd hr (by simp)
      · rw [hpk, Equiv.swap_apply_of_ne_of_ne (by simp) hr'] at hr
        exact h j r (hpk.trans hr)
  · rw [Function.update_of_ne hj] at hr
    exact h j r hr

/-- **Before every step the logged requests are requests of `G`.** -/
theorem preVLog_in (k : ℕ) (hk : k ≤ t + 1) (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t)
    (hb : preVLog e G a k b ≠ 0) : G.LogsIn (G.logsOf b) := by
  induction k generalizing b with
  | zero =>
    have := preVLog_supp e G a 0 (Nat.zero_le _) b hb
    intro j r hr
    have h0 := (this j).not.1 (Nat.not_lt_zero _)
    rw [hr] at h0
    exact absurd rfl h0
  | succ k ih =>
    have hk' : k < t + 1 := by omega
    have hq : preVLog e G a (k + 1) = relabel (wsSplit G.W (LogReg Req (t + 1))).symm
        (controlled (fun _ => simQueryIso e G.W) (relabel (wsSplit G.W (LogReg Req (t + 1)))
          (simStage e (G.instLog a) k))) :=
      simQuery_prod e G.W (LogReg Req (t + 1)) (simStage e (G.instLog a) k)
    rw [hq] at hb
    exact supp_controlled_ws G _ (fun b' hb' =>
      stageLog_in e G a ⟨k, hk'⟩ (fun b'' hb'' => ih (by omega) b'' hb'') b' hb') b hb

/-- **The logged requests of the instance's simulated state are requests of `G`.** -/
theorem simStateLog_in (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t)
    (hb : simState e (G.instLog a) b ≠ 0) : G.LogsIn (G.logsOf b) :=
  stageLog_in e G a (Fin.last t) (fun b' hb' => preVLog_in e G a t (by omega) b' hb') b hb

/-! ### The replies at the logged requests -/

/-- **The replies `a` and `a'` agree at the requests the logs `lg` hold below `k`**: at every
request point `j < k` whose log holds `r`, both reply `r` alike after the requests logged before
`j`. -/
def RepliesAgree (k : ℕ) (lg : LogReg Req (t + 1)) (a a' : ℕ → List Req → Req → Option Resp) :
    Prop :=
  ∀ j : Fin (t + 1), (j : ℕ) < k → ∀ r, lg j = some r →
    a j (requestsBefore lg j) r = a' j (requestsBefore lg j) r

variable {a} {a' : ℕ → List Req → Req → Option Resp}

/-- A vector before step `k` vanishes at the basis states whose log `k` is filled. -/
theorem preVLog_eq_zero_of_isSome (k : Fin (t + 1))
    {b : SimRegister (G.W × LogReg Req (t + 1)) I J m t} (hb : (G.logsOf b k).isSome) :
    preVLog e G a k b = 0 := by
  by_contra h
  have := LogsAt.eq_none (preVLog_supp e G a k (by omega) b h)
  rw [this] at hb
  exact Bool.false_ne_true hb

/-- **The slice after step `k` at the logs `lg` reads the replies only at the requests of `lg`**,
given the same for the slices before step `k`. -/
theorem wsSlice_stage_congr (k : Fin (t + 1)) (lg : LogReg Req (t + 1))
    (hag : RepliesAgree ((k : ℕ) + 1) lg a a')
    (hpre : ∀ lg', RepliesAgree k lg' a a' →
      wsSlice (preVLog e G a k) lg' = wsSlice (preVLog e G a' k) lg') :
    wsSlice (simStage e (G.instLog a) k) lg = wsSlice (simStage e (G.instLog a') k) lg := by
  suffices hslice : wsSlice (permOp (reqPermLogSim G a k) (preVLog e G a k)) lg =
      wsSlice (permOp (reqPermLogSim G a' k) (preVLog e G a' k)) lg by
    rw [simStage_eq_preVLog, simStage_eq_preVLog, simStep_instLog, simStep_instLog]
    exact (wsSlice_relabel_controlled (stepSim G k) _ lg).trans
      ((congrArg (stepSim G k) hslice).trans (wsSlice_relabel_controlled (stepSim G k) _ lg).symm)
  ext x
  obtain ⟨⟨w, qs⟩, sl⟩ := x
  change preVLog e G a k (((G.reqPermLog a k).symm (w, lg), qs), sl) =
    preVLog e G a' k (((G.reqPermLog a' k).symm (w, lg), qs), sl)
  have hlogs : ∀ α : ℕ → List Req → Req → Option Resp, ((G.reqPermLog α k).symm (w, lg)).2 =
      Function.update lg k (Equiv.swap none (some (G.req k w)) (lg k)) := fun _ => rfl
  rcases hk : lg k with _ | r
  · have h0 : ∀ α : ℕ → List Req → Req → Option Resp,
        preVLog e G α k (((G.reqPermLog α k).symm (w, lg), qs), sl) = 0 := fun α =>
      preVLog_eq_zero_of_isSome e G k (by
        change ((G.reqPermLog α k).symm (w, lg)).2 k |>.isSome
        rw [hlogs, Function.update_self, hk, Equiv.swap_apply_left]
        rfl)
    rw [h0, h0]
  · by_cases hr : r = G.req k w
    · have hrep : a k (requestsBefore lg k) (G.req k w) = a' k (requestsBefore lg k) (G.req k w) :=
        hag k (Nat.lt_succ_self _) _ (by rw [hk, hr])
      have hsym : (G.reqPermLog a k).symm (w, lg) = (G.reqPermLog a' k).symm (w, lg) := by
        change ((G.write k (a k (requestsBefore lg k) (G.req k w))).symm w, _) =
          ((G.write k (a' k (requestsBefore lg k) (G.req k w))).symm w, _)
        rw [hrep]
      rw [hsym]
      set p := (G.reqPermLog a' k).symm (w, lg) with hp
      have hp2 : p.2 = Function.update lg k none := by
        rw [hp, hlogs, hk, hr, Equiv.swap_apply_right]
      have hag' : RepliesAgree k p.2 a a' := by
        intro j hj r' hr'
        have hjk : j ≠ k := Fin.ne_of_lt hj
        have hrb : requestsBefore p.2 j = requestsBefore lg j :=
          requestsBefore_congr fun j' hj' => by
            rw [hp2, Function.update_of_ne (Fin.ne_of_lt (lt_trans hj' hj))]
        rw [hp2, Function.update_of_ne hjk] at hr'
        rw [hrb]
        exact hag j (by omega) r' hr'
      have := congrArg (fun v : QState (SimRegister G.W I J m t) => v ((p.1, qs), sl))
        (hpre p.2 hag')
      exact this
    · have h0 : ∀ α : ℕ → List Req → Req → Option Resp,
          preVLog e G α k (((G.reqPermLog α k).symm (w, lg), qs), sl) = 0 := fun α =>
        preVLog_eq_zero_of_isSome e G k (by
          change ((G.reqPermLog α k).symm (w, lg)).2 k |>.isSome
          rw [hlogs, Function.update_self, hk, Equiv.swap_apply_of_ne_of_ne (by simp)
            (by simpa using hr)]
          rfl)
      rw [h0, h0]

/-- **The slice before step `k` at the logs `lg` reads the replies only at the requests of
`lg`.** -/
theorem wsSlice_preVLog_congr (k : ℕ) (hk : k ≤ t + 1) (lg : LogReg Req (t + 1))
    (hag : RepliesAgree k lg a a') :
    wsSlice (preVLog e G a k) lg = wsSlice (preVLog e G a' k) lg := by
  induction k generalizing lg with
  | zero => rfl
  | succ k ih =>
    have hk' : k < t + 1 := by omega
    have hq : ∀ α : ℕ → List Req → Req → Option Resp, preVLog e G α (k + 1) =
        relabel (wsSplit G.W (LogReg Req (t + 1))).symm (controlled (fun _ => simQueryIso e G.W)
          (relabel (wsSplit G.W (LogReg Req (t + 1))) (simStage e (G.instLog α) k))) := fun α =>
      simQuery_prod e G.W (LogReg Req (t + 1)) (simStage e (G.instLog α) k)
    rw [hq, hq]
    exact (wsSlice_relabel_controlled (simQueryIso e G.W) _ lg).trans
      ((congrArg (simQueryIso e G.W) (wsSlice_stage_congr e G ⟨k, hk'⟩ lg hag
        fun lg' h' => ih (by omega) lg' h')).trans
        (wsSlice_relabel_controlled (simQueryIso e G.W) _ lg).symm)

/-- **The slice of the simulated state at the logs `lg` reads the replies only at the requests of
`lg`.** -/
theorem wsSlice_simStateLog_congr (lg : LogReg Req (t + 1)) (hag : RepliesAgree (t + 1) lg a a') :
    wsSlice (simState e (G.instLog a)) lg = wsSlice (simState e (G.instLog a')) lg :=
  wsSlice_stage_congr e G (Fin.last t) lg hag fun lg' h' =>
    wsSlice_preVLog_congr e G t (by omega) lg' h'

/-! ### The law as a sum over the logs -/

open Classical in
/-- **The Born weight of a test of the first factor is the sum of the Born weights of the
slices.** -/
theorem bornWeight_eq_sum_wsSlice {W L : Type} [Fintype W] [DecidableEq W] [Fintype L]
    [DecidableEq L] (v : QState (SimRegister (W × L) I J m t)) (g : SimRegister W I J m t → Prop) :
    bornWeight v {b | g (wsSplit W L b).1} =
      ∑ l, ∑ x, if g x then ‖wsSlice v l x‖ₑ ^ 2 else 0 := by
  rw [bornWeight_apply_eq_sum, ← Equiv.sum_comp (wsSplit W L).symm, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [Set.indicator, Set.mem_ofPred_eq, Equiv.apply_symm_apply]
  rfl

open Classical in
/-- **The Born weight of a slice** on the outcomes whose output and database lie in `S`. -/
noncomputable def sliceWeight (S : Set (O × DB (Bits m) B)) (v : QState (SimRegister G.W I J m t)) :
    ℝ≥0∞ :=
  ∑ x : SimRegister G.W I J m t, if (G.out x.1.1, slotsDB e x.2) ∈ S then ‖v x‖ₑ ^ 2 else 0

omit [Fintype Resp] [DecidableEq Resp] [Inhabited Req] in
variable (a) in
/-- **`simLaw` of the instance as a sum over the logs** of the Born weights of the slices. -/
theorem simLaw_instLog_eq_sum (S : Set (O × DB (Bits m) B)) :
    simLaw e (G.instLog a) S =
      ∑ lg : LogReg Req (t + 1), sliceWeight e G S (wsSlice (simState e (G.instLog a)) lg) := by
  rw [simLaw, MeasureTheory.OuterMeasure.map_apply]
  exact bornWeight_eq_sum_wsSlice (simState e (G.instLog a))
    (fun x => (G.out x.1.1, slotsDB e x.2) ∈ S)

end Reindex

/-! ### The reindexing -/

section Sum

open GordieHowe.QROM

variable {m t : ℕ} {I J B Req Resp O : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Inhabited Req]
  (e : BitStr I J ≃ B) (G : ReqQueryAlg (Bits m) (BitStr I J) Req Resp t O)

/-- **The replies realizing given values at a request pattern**: `u k` at every request point
`k ≤ t`, whatever the earlier requests and the request. -/
def constReplies (u : Fin (t + 1) → Option Resp) : ℕ → List Req → Req → Option Resp :=
  fun k _ _ => if h : k < t + 1 then u ⟨k, h⟩ else none

/-- **The replies of `a` at the request pattern `L`**: at request point `k`, the reply to `L k`
after the requests `L` holds before `k`. -/
def repliesAt (a : ℕ → List Req → Req → Option Resp) (L : Fin (t + 1) → Req) :
    Fin (t + 1) → Option Resp :=
  fun k => a k (requestsBefore (fun j => some (L j)) k) (L k)

omit [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Inhabited Req] in
theorem repliesAgree_constReplies (a : ℕ → List Req → Req → Option Resp) (L : Fin (t + 1) → Req) :
    RepliesAgree (t + 1) (fun j => some (L j)) a (constReplies (Resp := Resp) (repliesAt a L)) := by
  intro j _ r hr
  simp only [Option.some.injEq] at hr
  subst hr
  simp [constReplies, repliesAt, j.2]

/-- **The reindexing of the coins of the replies** (module docstring). For two families of replies
`a c` and `a' c'`, drawn from the coins `μ` and `μ'`, whose replies at every request pattern `L`
of requests of `G` (`L k` is `G.req k w` for some `w`; `repliesAt`: the reply at request point `k`
to `L k` after the requests `L` holds before `k`) have the same law (`hlaw`), the coin averages of
`simLaw` of the instances agree on every event `S`.

The hypothesis quantifies over every pattern of requests that `G` can make at each step, also
patterns that no run of the instance produces. -/
theorem sum_simLaw_instLog_eq {κ κ' : Type} [Fintype κ] [Fintype κ'] (μ : PMF κ) (μ' : PMF κ')
    (a : κ → ℕ → List Req → Req → Option Resp) (a' : κ' → ℕ → List Req → Req → Option Resp)
    (hlaw : ∀ L : Fin (t + 1) → Req, (∀ k, ∃ w, L k = G.req k w) →
      μ.map (fun c => repliesAt (a c) L) = μ'.map (fun c' => repliesAt (a' c') L))
    (S : Set (O × DB (Bits m) B)) :
    ∑ c, μ c * simLaw e (G.instLog (a c)) S = ∑ c', μ' c' * simLaw e (G.instLog (a' c')) S := by
  classical
  set full : (Fin (t + 1) → Req) → LogReg Req (t + 1) := fun L j => some (L j) with hfull
  have hinj : Function.Injective full := fun L L' h => funext fun j => by
    simpa [hfull] using congrFun h j
  set F : (Fin (t + 1) → Req) → (Fin (t + 1) → Option Resp) → ℝ≥0∞ := fun L u =>
    sliceWeight e G S (wsSlice (simState e (G.instLog (constReplies u))) (full L)) with hF
  set poss : Finset (Fin (t + 1) → Req) := Finset.univ.filter fun L => ∀ k, ∃ w, L k = G.req k w
    with hposs
  -- `simLaw` of an instance is the sum, over the full patterns of requests of `G`, of `F` at its
  -- replies.
  have hsplit : ∀ α : ℕ → List Req → Req → Option Resp,
      simLaw e (G.instLog α) S = ∑ L ∈ poss, F L (repliesAt α L) := by
    intro α
    rw [simLaw_instLog_eq_sum]
    have hzero : ∀ lg ∈ (Finset.univ : Finset (LogReg Req (t + 1))),
        lg ∉ poss.image full →
          sliceWeight e G S (wsSlice (simState e (G.instLog α)) lg) = 0 := by
      intro lg _ hlg
      refine Finset.sum_eq_zero fun x _ => ?_
      have hx : wsSlice (simState e (G.instLog α)) lg x = 0 := by
        by_contra hne
        have hfl := simStateLog_supp e G α _ hne
        have hin := simStateLog_in e G α _ hne
        simp only [logsOf, Equiv.apply_symm_apply] at hfl hin
        refine hlg (Finset.mem_image.2 ⟨fun j => (lg j).get (hfl j), ?_, funext fun j => by
          simp [hfull]⟩)
        rw [hposs, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun k => ?_⟩
        obtain ⟨w, hw⟩ := hin k _ (Option.some_get (hfl k)).symm
        exact ⟨w, hw⟩
      simp [hx]
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero,
      Finset.sum_image fun L _ L' _ h => hinj h]
    refine Finset.sum_congr rfl fun L _ => ?_
    simp only [hF]
    rw [wsSlice_simStateLog_congr e G (full L) (repliesAgree_constReplies α L)]
  simp only [hsplit, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := κ'))]
  refine Finset.sum_congr rfl fun L hL => ?_
  rw [hposs, Finset.mem_filter] at hL
  rw [sum_mul_comp_eq_sum_map μ (fun c => repliesAt (a c) L) (F L),
    sum_mul_comp_eq_sum_map μ' (fun c' => repliesAt (a' c') L) (F L), hlaw L hL.2]

end Sum

end ReqQueryAlg

end GordieHowe.Quantum
