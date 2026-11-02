-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ReqBridgeLogs

@[expose] public section

-- The proofs below read the definition of the bridge (irreducible elsewhere).
set_option allowUnsafeReducibility true in
attribute [local reducible] GordieHowe.Quantum.bridgeAlg

/-!
# The requests of the bridge algorithm slot by slot

The slot form of `bridgeAlg_logs` (`GordieHowe/Model/Quantum/Interactive/ReqBridgeLogs.lean`):
the request of the bridge algorithm (`bridgeAlg`) at a request point is the dummy, or the outer
request of the absorbed log of the slot that the point answers (`answerSlot`). Since distinct
request points answer distinct slots, the bridge's requests satisfying a property the dummy lacks
are at most the absorbed logs whose outer requests satisfy it (`card_bridge_le`). Along the way, any
family of sets of the absorbed adversary's workspace and logs that its steps carry from slot to
slot (`AdaptiveIAlg.LogInv`) holds at the end, on every basis state of the simulated run.

- `ReqQueryAlg.instSetBy`, `ReqQueryAlg.inst_step_supp_by`, `ReqQueryAlg.inst_init_supp_by`,
  `ReqQueryAlg.supported_simState_inst_by`, `ReqQueryAlg.supported_simState_withPerm_inst_by`: the
  supports of the instance of a query algorithm with request points, read after permutations that
  keep them, for sets indexed by any summary of the logs.
- `AdaptiveIAlg.LogInv A F tab T`: the sets `T j` of workspaces, request registers and absorbed
  logs hold at the
  start, slot `j` carries `T j` into `T (j + 1)`, and the post steps keep `T slots`;
  `AdaptiveIAlg.LogInv.univ`.
- `AdaptiveIAlg.slotLogS`, `AdaptiveIAlg.slotLogS_succ`, `AdaptiveIAlg.slotLogS_post`,
  `AdaptiveIAlg.valid_slotLogS`: the certificate of the composition through the sets of absorbed
  logs blank from slot `n`, the pairs `(j, q)` of `N` realized by slot `j`'s log, inside `T`.
- `answerDelta_work`, `answerDelta_request`: the bridge's write keeps the adversary's workspace
  and request register.
- `bridgeAlg_req_slot`: a request of the bridge is the dummy or the outer request of the log of the
  slot it answers.
- `bridgeAlg_withPerm_slotLogs` (**the slot form**, stated once): for the bridge read after
  permutations that keep the supports of its steps, on every basis state of nonzero amplitude of
  the compressed-oracle simulation of its instance, the output's workspace and logs lie in
  `T slots`, and every logged request is the dummy or the outer request of the output's log of the
  slot that its request point answers. `bridgeAlg_slotLogs`: without permutations;
  `bridgeAlg_logs`: at the sets of all workspaces and logs, every logged request is the dummy or
  the outer request of a logged request of the output.
- `answerSlot_inj`, `countP_requests`, `card_bridge_le`: the count.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

/-! ### Supports of the instance for any summary of the logs -/

namespace ReqQueryAlg

variable {X Y Req Resp O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Req] [Fintype Req] [Fintype Resp] [DecidableEq Resp] {t : ℕ}
  (G : ReqQueryAlg X Y Req Resp t O) (a : ℕ → Req → Option Resp) {ν : Type}
  (WS : ν → ℕ → Set G.W) (nd : LogReg Req (t + 1) → ν)

/-- **The supports of the instance after step `k`** (proof-internal), for sets indexed by the
summary `nd` of the logs: the logs filled exactly up to `k`, the work register in `WS (nd lg) k`
(for a summary of the logs of any type). -/
def instSetBy (k : ℕ) : Set (G.W × LogReg Req (t + 1)) :=
  {p | FilledTo (k + 1) p.2 ∧ p.1 ∈ WS (nd p.2) k}

/-- **A step of the instance carries `instSetBy k` to `instSetBy (k + 1)`.** -/
theorem inst_step_supp_by
    (hstep : ∀ N k (hk : k + 1 < t + 1) v, Supported {r | r.1 ∈ WS N k} v →
      Supported {r | r.1 ∈ WS N (k + 1)} (G.step ⟨k + 1, hk⟩ v))
    (hreq : ∀ k (hk : k + 1 < t + 1) x w (lg : LogReg Req (t + 1)), FilledTo (k + 1) lg →
      w ∈ WS (nd lg) k → G.write ⟨k + 1, hk⟩ x w ∈
        WS (nd (Function.update lg ⟨k + 1, hk⟩ (some (G.req ⟨k + 1, hk⟩ w)))) k)
    {k : ℕ} (hk : k + 1 < t + 1) (v : QState (QueryReg (G.W × LogReg Req (t + 1)) 1 X Y))
    (hv : Supported {r | r.1 ∈ G.instSetBy WS nd k} v) :
    Supported {r | r.1 ∈ G.instSetBy WS nd (k + 1)} (G.instStep a ⟨k + 1, hk⟩ v) := by
  set π := (G.reqPerm a ⟨k + 1, hk⟩).prodCongr (Equiv.refl (Fin 1 → X × Y))
  have h1 : Supported {r : QueryReg (G.W × LogReg Req (t + 1)) 1 X Y | FilledTo (k + 2) r.1.2 ∧
      r.1.1 ∈ WS (nd r.1.2) k} (permOp π v) := by
    refine hv.permOp fun r hr => ?_
    obtain ⟨⟨w, lg⟩, qs⟩ := r
    obtain ⟨hl, hw⟩ := hr
    have hpk : lg ⟨k + 1, hk⟩ = none := FilledTo.eq_none (k := ⟨k + 1, hk⟩) hl
    change FilledTo (k + 2) (Function.update lg ⟨k + 1, hk⟩
        (Equiv.swap none (some (G.req ⟨k + 1, hk⟩ w)) (lg ⟨k + 1, hk⟩))) ∧
      G.write ⟨k + 1, hk⟩ _ w ∈ WS (nd (Function.update lg ⟨k + 1, hk⟩
        (Equiv.swap none (some (G.req ⟨k + 1, hk⟩ w)) (lg ⟨k + 1, hk⟩)))) k
    rw [hpk, Equiv.swap_apply_left]
    exact ⟨filledTo_update hk hl _, hreq k hk _ w lg hl hw⟩
  rw [instStep_eq]
  intro r hr
  rw [relabel_apply, Equiv.symm_symm]
  change controlled (fun _ => G.step ⟨k + 1, hk⟩) (relabel G.logSplit (permOp π v))
    ((G.logSplit r).1, (G.logSplit r).2) = 0
  rw [controlled_apply]
  by_cases hl : FilledTo (k + 2) r.1.2
  · refine hstep (nd r.1.2) k hk _ (fun r' hr' => ?_) _ fun h => hr ⟨hl, h⟩
    rw [relabel_apply]
    exact h1 _ fun h => hr' h.2
  · have h0 : (WithLp.toLp 2 fun i' => relabel G.logSplit (permOp π v) (i', (G.logSplit r).2) :
        QState (QueryReg G.W 1 X Y)) = 0 := by
      ext i'
      rw [relabel_apply]
      exact h1 _ fun h => hl h.1
    rw [h0, map_zero]
    rfl

/-- **The first step of the instance lands in `instSetBy 0`.** -/
theorem inst_init_supp_by (W0 : Set G.W) (N0 : ν)
    (h0 : Supported {r | r.1 ∈ W0} G.init)
    (hreq0 : ∀ x w, w ∈ W0 → G.write 0 x w ∈ W0 ∧
      nd (Function.update (fun _ => none) 0 (some (G.req 0 w))) = N0)
    (hstep0 : ∀ v, Supported {r | r.1 ∈ W0} v → Supported {r | r.1 ∈ WS N0 0} (G.step 0 v)) :
    Supported {r | r.1 ∈ G.instSetBy WS nd 0}
      (G.instStep a 0 (relabel G.logSplit.symm (tensorKet G.init (fun _ => none)))) := by
  set π := (G.reqPerm a 0).prodCongr (Equiv.refl (Fin 1 → X × Y))
  have hi : Supported {r : QueryReg (G.W × LogReg Req (t + 1)) 1 X Y | r.1.1 ∈ W0 ∧
      r.1.2 = fun _ => none} (relabel G.logSplit.symm (tensorKet G.init (fun _ => none))) := by
    intro r hr
    rw [relabel_apply, Equiv.symm_symm, tensorKet_apply]
    by_cases hl : r.1.2 = fun _ => none
    · rw [h0 _ fun h => hr ⟨h, hl⟩, zero_mul]
    · rw [if_neg (show ¬ (G.logSplit r).2 = fun _ => none from hl), mul_zero]
  have h1 : Supported {r : QueryReg (G.W × LogReg Req (t + 1)) 1 X Y | FilledTo 1 r.1.2 ∧
      r.1.1 ∈ W0 ∧ nd r.1.2 = N0}
      (permOp π (relabel G.logSplit.symm (tensorKet G.init (fun _ => none)))) := by
    refine hi.permOp fun r hr => ?_
    obtain ⟨⟨w, lg⟩, qs⟩ := r
    obtain ⟨hw, hl⟩ := hr
    change lg = fun _ => none at hl
    subst hl
    change FilledTo 1 (Function.update (fun _ => none) 0
        (Equiv.swap none (some (G.req 0 w)) none)) ∧ G.write 0 _ w ∈ W0 ∧
      nd (Function.update (fun _ => none) 0 (Equiv.swap none (some (G.req 0 w)) none)) = N0
    rw [Equiv.swap_apply_left]
    refine ⟨filledTo_update (k := 0) (by omega) (fun j => by simp) _,
      (hreq0 (a 0 (G.req 0 w)) w hw).1, (hreq0 none w hw).2⟩
  rw [instStep_eq]
  intro r hr
  rw [relabel_apply, Equiv.symm_symm]
  change controlled (fun _ => G.step 0) (relabel G.logSplit (permOp π (relabel G.logSplit.symm
    (tensorKet G.init (fun _ => none))))) ((G.logSplit r).1, (G.logSplit r).2) = 0
  rw [controlled_apply]
  by_cases hl : FilledTo 1 r.1.2 ∧ nd r.1.2 = N0
  · refine hstep0 _ (fun r' hr' => ?_) _ fun h => hr ⟨hl.1, by rw [hl.2]; exact h⟩
    rw [relabel_apply]
    exact h1 _ fun h => hr' h.2.1
  · have h0' : (WithLp.toLp 2 fun i' => relabel G.logSplit (permOp π (relabel G.logSplit.symm
        (tensorKet G.init (fun _ => none)))) (i', (G.logSplit r).2) :
        QState (QueryReg G.W 1 X Y)) = 0 := by
      ext i'
      rw [relabel_apply]
      exact h1 _ fun h => hl ⟨h.1, h.2.2⟩
    rw [h0', map_zero]
    rfl

end ReqQueryAlg

namespace ReqQueryAlg

open GordieHowe.QROM

variable {m t : ℕ} {I J B Req Resp O : Type} [Fintype I] [Fintype J] [DecidableEq I]
  [DecidableEq J] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (e : BitStr I J ≃ B) (G : ReqQueryAlg (Bits m) (BitStr I J) Req Resp t O)
  (a : ℕ → Req → Option Resp) {ν : Type} (WS : ν → ℕ → Set G.W)
  (nd : LogReg Req (t + 1) → ν)

/-- **The instance's simulated run lies on `instSetBy`** at its end
(for a summary of the logs of any type). -/
theorem supported_simState_inst_by (W0 : Set G.W) (N0 : ν)
    (h0 : Supported {r | r.1 ∈ W0} G.init)
    (hreq0 : ∀ x w, w ∈ W0 → G.write 0 x w ∈ W0 ∧
      nd (Function.update (fun _ => none) 0 (some (G.req 0 w))) = N0)
    (hstep0 : ∀ v, Supported {r | r.1 ∈ W0} v → Supported {r | r.1 ∈ WS N0 0} (G.step 0 v))
    (hstep : ∀ N k (hk : k + 1 < t + 1) v, Supported {r | r.1 ∈ WS N k} v →
      Supported {r | r.1 ∈ WS N (k + 1)} (G.step ⟨k + 1, hk⟩ v))
    (hreq : ∀ k (hk : k + 1 < t + 1) x w (lg : LogReg Req (t + 1)), FilledTo (k + 1) lg →
      w ∈ WS (nd lg) k → G.write ⟨k + 1, hk⟩ x w ∈
        WS (nd (Function.update lg ⟨k + 1, hk⟩ (some (G.req ⟨k + 1, hk⟩ w)))) k) :
    Supported (workSet (G.inst a).W t (G.instSetBy WS nd t)) (simState e (G.inst a)) := by
  refine QueryAlg.supported_simStage_of e (G.inst a) (fun k => G.instSetBy WS nd k) ?_ ?_ le_rfl
  · rw [OracleAlg.stepAt_of_lt _ (by omega)]
    exact G.inst_init_supp_by a WS nd W0 N0 h0 hreq0 hstep0
  · intro k hk v hv
    rw [OracleAlg.stepAt_of_lt _ (by omega)]
    exact G.inst_step_supp_by a WS nd hstep hreq (by omega) v hv

/-- **The simulated run of an instance of `G` read after permutations lies on `instSetBy`**
(`supported_simState_inst_by`), when the permutations keep the supports of the steps (`hb0`,
`hb`). -/
theorem supported_simState_withPerm_inst_by
    (b : Fin (t + 1) → Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J))) (W0 : Set G.W) (N0 : ν)
    (h0 : Supported {r | r.1 ∈ W0} G.init)
    (hreq0 : ∀ x w, w ∈ W0 → G.write 0 x w ∈ W0 ∧
      nd (Function.update (fun _ => none) 0 (some (G.req 0 w))) = N0)
    (hstep0 : ∀ v, Supported {r | r.1 ∈ W0} v → Supported {r | r.1 ∈ WS N0 0} (G.step 0 v))
    (hstep : ∀ N k (hk : k + 1 < t + 1) v, Supported {r | r.1 ∈ WS N k} v →
      Supported {r | r.1 ∈ WS N (k + 1)} (G.step ⟨k + 1, hk⟩ v))
    (hreq : ∀ k (hk : k + 1 < t + 1) x w (lg : LogReg Req (t + 1)), FilledTo (k + 1) lg →
      w ∈ WS (nd lg) k → G.write ⟨k + 1, hk⟩ x w ∈
        WS (nd (Function.update lg ⟨k + 1, hk⟩ (some (G.req ⟨k + 1, hk⟩ w)))) k)
    (hb0 : ∀ r : QueryReg G.W 1 (Bits m) (BitStr I J), r.1 ∈ W0 → (b 0 r).1 ∈ W0)
    (hb : ∀ N k (hk : k + 1 < t + 1) (r : QueryReg G.W 1 (Bits m) (BitStr I J)),
      r.1 ∈ WS N k → (b ⟨k + 1, hk⟩ r).1 ∈ WS N k) :
    Supported (workSet ((G.withPerm b).inst a).W t ((G.withPerm b).instSetBy WS nd t))
      (simState e ((G.withPerm b).inst a)) :=
  supported_simState_inst_by e (G.withPerm b) a WS nd W0 N0 h0 hreq0
    (fun _ hv => hstep0 _ (hv.permOp fun r hr => hb0 r hr))
    (fun N k hk _ hv => hstep N k hk _ (hv.permOp fun r hr => hb N k hk r hr)) hreq

end ReqQueryAlg

/-! ### Invariant sets of workspaces and logs; the slot-indexed logs -/

namespace AdaptiveIAlg

variable {X Y Req Resp O Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)
  (tab : A.OuterTab Req₂ Resp₂)

/-- **Sets of workspaces and absorbed logs carried by the steps** of the adversary absorbed with
a table, in its trace-preserving form: the workspace and absorbed logs of every initial basis state
lie in `T 0`, the step of slot `j` carries `T j` into `T (j + 1)`, and each step `k` after the
slots carries `T k` into `T (k + 1)`. -/
structure LogInv (T : ℕ → Set ((A.W × Req) × LogReg Req A.slots)) : Prop where
  /-- The initial workspaces and logs lie in `T 0`. -/
  init : ∀ d d', ((A.absorbTab F tab).toTPKindAlg.init).mat d d' ≠ 0 →
    ((d.workspace.1.1.work, d.workspace.1.1.request), d.workspace.1.1.logs) ∈ T 0
  /-- The step of slot `j` carries `T j` into `T (j + 1)`. -/
  slot : ∀ (j : Fin A.slots) z
    (y x : DReg (A.absorbTab F tab).toTPKindAlg.W A.width X Y Req₁ Resp₁),
    ((A.absorbTab F tab).toTPKindAlg.step (slotStep j)).op z y x ≠ 0 →
    ((x.workspace.1.1.work, x.workspace.1.1.request), x.workspace.1.1.logs) ∈ T j →
    ((y.workspace.1.1.work, y.workspace.1.1.request), y.workspace.1.1.logs) ∈ T (j + 1)
  /-- The step `k` after the slots carries `T k` into `T (k + 1)`. The sets are indexed by the
  step: re-applying a step need not keep a set (re-applying the relay's last step can wrap its
  clock), so a set kept by every step after the slots would lose what the last step gives. -/
  post : ∀ (k : StepIdx A.slots A.post), A.slots ≤ (k : ℕ) →
    ∀ z (y x : DReg (A.absorbTab F tab).toTPKindAlg.W A.width X Y Req₁ Resp₁),
    ((A.absorbTab F tab).toTPKindAlg.step k).op z y x ≠ 0 →
    ((x.workspace.1.1.work, x.workspace.1.1.request), x.workspace.1.1.logs) ∈ T k →
    ((y.workspace.1.1.work, y.workspace.1.1.request), y.workspace.1.1.logs) ∈ T (k + 1)

/-- **The whole space is carried by the steps.** -/
theorem LogInv.univ : A.LogInv F tab fun _ => Set.univ :=
  ⟨fun _ _ _ => trivial, fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ => trivial⟩

/-- **The workspaces with the absorbed logs blank from slot `n` on, for every `(o, q) ∈ N` a slot
`j` with `o = some j` whose log has the outer request `q`, and the workspace and logs in `T n`**
(proof-internal). -/
def slotLogS (T : ℕ → Set ((A.W × Req) × LogReg Req A.slots))
    (N : Set (Option (Fin A.slots) × Req₂)) (n : ℕ) : Set (A.absorbTab F tab).toTPKindAlg.W :=
  {w | (∀ j : Fin A.slots, n ≤ (j : ℕ) → w.1.1.logs j = none) ∧
    (∀ p ∈ N, ∃ j r, p.1 = some j ∧ w.1.1.logs j = some r ∧
      F.outer (A.reqCount w.1.1.logs j) r = some p.2) ∧
    ((w.1.1.work, w.1.1.request), w.1.1.logs) ∈ T n}

variable {A F tab} {T : ℕ → Set ((A.W × Req) × LogReg Req A.slots)}

/-- **The step of slot `j` carries `slotLogS N j` to `slotLogS N (j + 1)`.** -/
theorem slotLogS_succ (hA : A.TracePreserving) (hT : A.LogInv F tab T)
    (N : Set (Option (Fin A.slots) × Req₂)) (j : Fin A.slots)
    {z : (A.absorbTab F tab).R ⊕ ((A.absorbTab F tab).R ⊕ Fin (A.budget + 2))}
    {y x : DReg (A.absorbTab F tab).toTPKindAlg.W A.width X Y Req₁ Resp₁}
    (h : ((A.absorbTab F tab).toTPKindAlg.step (slotStep j)).op z y x ≠ 0)
    (hx : x.workspace ∈ A.slotLogS F tab T N j) :
    y.workspace ∈ A.slotLogS F tab T N (j + 1) := by
  obtain ⟨hb, he, hTx⟩ := hx
  refine ⟨fun j' hj' => ?_, fun p hp => ?_, hT.slot j z y x h hTx⟩
  · rw [tp_absorbTab_logs hA h j' (by simp; omega)]
    exact hb j' (by omega)
  · obtain ⟨j', r, hpj, hjr, hr⟩ := he p hp
    have hjn : (j' : ℕ) < j := by
      by_contra h'
      rw [hb j' (by omega)] at hjr
      exact absurd hjr (by simp)
    have hc : A.reqCount y.workspace.1.1.logs j' = A.reqCount x.workspace.1.1.logs j' :=
      congrArg List.length (requestsBefore_congr fun i hi =>
        tp_absorbTab_logs hA h i (by simp; omega))
    exact ⟨j', r, hpj, by rw [tp_absorbTab_logs hA h j' (by simp; omega)]; exact hjr,
      by rw [hc]; exact hr⟩

/-- **The step `k` after the slots carries `slotLogS N k` to `slotLogS N (k + 1)`.** -/
theorem slotLogS_post (hA : A.TracePreserving) (hT : A.LogInv F tab T)
    (N : Set (Option (Fin A.slots) × Req₂)) {k : StepIdx A.slots A.post} (hk : A.slots ≤ (k : ℕ))
    {z : (A.absorbTab F tab).R ⊕ ((A.absorbTab F tab).R ⊕ Fin (A.budget + 2))}
    {y x : DReg (A.absorbTab F tab).toTPKindAlg.W A.width X Y Req₁ Resp₁}
    (h : ((A.absorbTab F tab).toTPKindAlg.step k).op z y x ≠ 0)
    (hx : x.workspace ∈ A.slotLogS F tab T N k) :
    y.workspace ∈ A.slotLogS F tab T N (k + 1) := by
  have hne : ∀ j : Fin A.slots, (j : ℕ) ≠ k := fun j => by have := j.isLt; omega
  obtain ⟨hb, he, hTx⟩ := hx
  refine ⟨fun j hj => ?_, fun p hp => ?_, hT.post k hk z y x h hTx⟩
  · rw [tp_absorbTab_logs hA h j (hne j)]
    exact hb j (by omega)
  · obtain ⟨j', r, hpj, hjr, hr⟩ := he p hp
    have hc : A.reqCount y.workspace.1.1.logs j' = A.reqCount x.workspace.1.1.logs j' :=
      congrArg List.length (requestsBefore_congr fun i _ => tp_absorbTab_logs hA h i (hne i))
    exact ⟨j', r, hpj, by rw [tp_absorbTab_logs hA h j' (hne j')]; exact hjr,
      by rw [hc]; exact hr⟩

variable [Nonempty X] [AddCommGroup Y]

/-- **The certificate of the composition of the adversary absorbed with a table**, through the
sets `slotLogS N`. -/
theorem valid_slotLogS (hA : A.TracePreserving) (hT : A.LogInv F tab T)
    (N : Set (Option (Fin A.slots) × Req₂)) (C₁ : Challenger X Y Req₁ Resp₁) :
    ReprogrammedCircuit.Valid (fun _ => Set.univ)
      ((A.absorbTab F tab).toTPKindAlg.wsG C₁ (A.slotLogS F tab T N))
      ((A.absorbTab F tab).toTPKindAlg.fullCircBoth C₁) 0
      ((A.absorbTab F tab).toTPKindAlg.advIn C₁ (A.slotLogS F tab T N 0))
      ((A.absorbTab F tab).toTPKindAlg.advIn C₁
        (A.slotLogS F tab T N (A.slots + A.post + 1))) :=
  KindAlg.valid_fullCircBoth_ws (A.slotLogS F tab T N) (A.absorbTab F tab).stepsTP_toTPKindAlg
    (fun j _ _ _ h hx => slotLogS_succ hA hT N j h hx)
    (fun _ hk _ _ _ h hx => slotLogS_post hA hT N hk h hx)

end AdaptiveIAlg

/-! ### The bridge's writes keep the adversary's workspace -/

section Work

open GordieHowe.QROM

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)

omit [Fintype Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Fintype Req₂] [DecidableEq Req₂]
  [Fintype Resp₂] [DecidableEq Resp₂] in
/-- The handling of slot `j`'s reply from the table keeps the adversary's workspace. -/
theorem afterPermTab_work (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁) :
    (A.afterPermTab F t j d).1.1.work = d.1.1.work := by
  have h1 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁,
      (A.storePerm j d').1.1.work = d'.1.1.work := fun d' => by
    unfold AdaptiveIAlg.storePerm AlgShape.storePerm
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    by_cases h : (d'.1.1.logs j).isSome = true
    · rw [if_pos h]
    · rw [if_neg h]
  have h2 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁,
      (A.answerPermTab F t j d').1.1.work = d'.1.1.work := fun d' => by
    unfold AdaptiveIAlg.answerPermTab
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    split <;> rfl
  have h3 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁,
      (A.clearPerm F.base j d').1.1.work = d'.1.1.work := fun d' => by
    unfold AdaptiveIAlg.clearPerm AlgShape.clearPerm
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    split <;> rfl
  unfold AdaptiveIAlg.afterPermTab
  simp only [Equiv.trans_apply, h1, h2, h3]

/-- The handling of slot `k - 1`'s reply from the table keeps the adversary's workspace. -/
theorem afterAtTab_work (k : ℕ) (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    (A.afterAtTab F k d).1.1.1.work = d.1.1.1.work := by
  unfold AdaptiveIAlg.afterAtTab
  split
  · exact afterPermTab_work A F _ _ _
  · rfl

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] in
/-- Writing the reply to an outer request keeps the adversary's workspace. -/
theorem absOuterSwap_work (j : Fin A.slots) (x : Option Resp₂) (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    (absOuterSwap A F j x d).1.1.1.work = d.1.1.1.work := by
  unfold absOuterSwap
  dsimp only [Equiv.coe_fn_mk]
  split
  · rfl
  · split <;> rfl

/-- **The bridge's write at the answer step of slot `j` keeps the adversary's workspace.** -/
theorem answerDelta_work (j : Fin A.slots) (x : Option Resp₂) (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    (answerDelta A F j x d).1.1.1.work = d.1.1.1.work := by
  have hs : ∀ d' : AbsD A Req₁ Resp₁ Req₂ Resp₂,
      ((A.afterAtTab F (j + 1)).symm d').1.1.1.work = d'.1.1.1.work := fun d' => by
    rw [← afterAtTab_work A F (j + 1) ((A.afterAtTab F (j + 1)).symm d'), Equiv.apply_symm_apply]
  simp only [answerDelta, Equiv.trans_apply]
  rw [hs, absOuterSwap_work, afterAtTab_work]

omit [Fintype Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Fintype Req₂] [DecidableEq Req₂]
  [Fintype Resp₂] [DecidableEq Resp₂] in
/-- The handling of slot `j`'s reply from the table keeps the adversary's request register. -/
theorem afterPermTab_request (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁) :
    (A.afterPermTab F t j d).1.1.request = d.1.1.request := by
  have h1 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁,
      (A.storePerm j d').1.1.request = d'.1.1.request := fun d' => by
    unfold AdaptiveIAlg.storePerm AlgShape.storePerm
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    by_cases h : (d'.1.1.logs j).isSome = true
    · rw [if_pos h]
    · rw [if_neg h]
  have h2 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁,
      (A.answerPermTab F t j d').1.1.request = d'.1.1.request := fun d' => by
    unfold AdaptiveIAlg.answerPermTab
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    split <;> rfl
  have h3 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁,
      (A.clearPerm F.base j d').1.1.request = d'.1.1.request := fun d' => by
    unfold AdaptiveIAlg.clearPerm AlgShape.clearPerm
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    split <;> rfl
  unfold AdaptiveIAlg.afterPermTab
  simp only [Equiv.trans_apply, h1, h2, h3]

/-- The handling of slot `k - 1`'s reply from the table keeps the adversary's request register. -/
theorem afterAtTab_request (k : ℕ) (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    (A.afterAtTab F k d).1.1.1.request = d.1.1.1.request := by
  unfold AdaptiveIAlg.afterAtTab
  split
  · exact afterPermTab_request A F _ _ _
  · rfl

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] in
/-- Writing the reply to an outer request keeps the adversary's request register. -/
theorem absOuterSwap_request (j : Fin A.slots) (x : Option Resp₂)
    (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    (absOuterSwap A F j x d).1.1.1.request = d.1.1.1.request := by
  unfold absOuterSwap
  dsimp only [Equiv.coe_fn_mk]
  split
  · rfl
  · split <;> rfl

/-- **The bridge's write at the answer step of slot `j` keeps the adversary's request register.** -/
theorem answerDelta_request (j : Fin A.slots) (x : Option Resp₂)
    (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    (answerDelta A F j x d).1.1.1.request = d.1.1.1.request := by
  have hs : ∀ d' : AbsD A Req₁ Resp₁ Req₂ Resp₂,
      ((A.afterAtTab F (j + 1)).symm d').1.1.1.request = d'.1.1.1.request := fun d' => by
    rw [← afterAtTab_request A F (j + 1) ((A.afterAtTab F (j + 1)).symm d'), Equiv.apply_symm_apply]
  simp only [answerDelta, Equiv.trans_apply]
  rw [hs, absOuterSwap_request, afterAtTab_request]

end Work

/-! ### The slot form of the bridge's requests -/

section Bridge

open GordieHowe.QROM GordieHowe.QROM.ExpandAdv

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)
  (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)
  (T : ℕ → Set ((A.W × Req) × LogReg Req A.slots))

/-- The adversary's workspace and request register, read from the register of the run of the
composition. -/
noncomputable abbrev cohWork (c : (((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁
    id).toQueryAlgCoh.mapOut (extOut A C₁ F d₀ (tab₀ A))).W) : A.W × Req :=
  (c.1.1.1.adv.workspace.1.1.work, c.1.1.1.adv.workspace.1.1.request)

/-- **The supports of the run of the composition after step `k`** (proof-internal), for the slot
requests `N` and the sets `T` (`cohSet` through `slotLogS`). -/
def slotCohSet (N : Set (Option (Fin A.slots) × Req₂)) (k : ℕ) :
    Set ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A))).W) :=
  {c | c.1.1.1 ∈ ReprogrammedCircuit.segOut
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.wsG C₁ (A.slotLogS F (tab₀ A) T N))
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁
        (A.slotLogS F (tab₀ A) T N (A.slots + A.post + 1))) 0
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries k ∧
    c.1.2 = false ∧
    (k < ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries →
      MixedAlg.Clean (k + 1) c.2)}

/-- **The supports of the bridge's work register after step `k`** (proof-internal). -/
def slotWSet (N : Set (Option (Fin A.slots) × Req₂)) (k : ℕ) :
    Set (bridgeAlg e A C₁ F d₂ E kq d₀).W :=
  {w | w.1 ∈ slotCohSet A C₁ F d₀ T N k}

/-- **On `slotCohSet N k` every pair `(some j, q)` of `N` is realized by slot `j`'s log.** -/
theorem slotCohSet_outer {N : Set (Option (Fin A.slots) × Req₂)} {k : ℕ} {c}
    (hc : c ∈ slotCohSet A C₁ F d₀ T N k) :
    ∀ p ∈ N, ∃ j r, p.1 = some j ∧ cohLogs A C₁ F d₀ c j = some r ∧
      F.outer (A.reqCount (cohLogs A C₁ F d₀ c) j) r = some p.2 := by
  obtain ⟨h1, -, -⟩ := hc
  unfold ReprogrammedCircuit.segOut KindAlg.wsG at h1
  split_ifs at h1 <;> exact h1.2.1

/-- **At the end, the workspace and logs lie in `T (slots + post + 1)`.** -/
theorem slotCohSet_final {N : Set (Option (Fin A.slots) × Req₂)} {k : ℕ}
    (hk : ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries ≤ k) {c}
    (hc : c ∈ slotCohSet A C₁ F d₀ T N k) :
    (cohWork A C₁ F d₀ c, cohLogs A C₁ F d₀ c) ∈ T (A.slots + A.post + 1) := by
  obtain ⟨h1, -, -⟩ := hc
  unfold ReprogrammedCircuit.segOut at h1
  rw [if_neg (by omega)] at h1
  exact h1.2.2

/-- **`slotCohSet` reads the workspace, the absorbed logs, the halting flag and the ancilla**, the
slot requests through the logs. -/
theorem slotCohSet_congr {N N' : Set (Option (Fin A.slots) × Req₂)} {k : ℕ} {c c'}
    (hc : c ∈ slotCohSet A C₁ F d₀ T N k)
    (hl : cohLogs A C₁ F d₀ c' = cohLogs A C₁ F d₀ c)
    (hw : cohWork A C₁ F d₀ c' = cohWork A C₁ F d₀ c) (hf : c'.1.2 = c.1.2) (ha : c'.2 = c.2)
    (hE : ∀ p ∈ N', ∃ j r, p.1 = some j ∧ cohLogs A C₁ F d₀ c' j = some r ∧
      F.outer (A.reqCount (cohLogs A C₁ F d₀ c') j) r = some p.2) :
    c' ∈ slotCohSet A C₁ F d₀ T N' k := by
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨?_, by rw [hf]; exact h2, by rw [ha]; exact h3⟩
  unfold ReprogrammedCircuit.segOut KindAlg.wsG at h1 ⊢
  split_ifs at h1 ⊢ <;>
    exact ⟨fun j hj => (congrFun hl j).trans (h1.1 j hj), hE, by
      change (cohWork A C₁ F d₀ c', cohLogs A C₁ F d₀ c') ∈ _
      rw [hl, hw]
      exact h1.2.2⟩

/-- **Writing a reply of the bridge keeps the adversary's workspace and request register.** -/
theorem bridgeAlg_write_work (k : Fin ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut
      C₁ id).depth + kq) + 1)) (x : Option Resp₂) (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) :
    cohWork A C₁ F d₀ ((bridgeAlg e A C₁ F d₂ E kq d₀).write k x w).1 =
      cohWork A C₁ F d₀ w.1 := by
  rcases h : answerSlot A C₁ k with _ | j
  · have e1 : (bridgeAlg e A C₁ F d₂ E kq d₀).write k x = Equiv.refl _ := by
      change (match answerSlot A C₁ k with
        | none => Equiv.refl _
        | some j => liftAbs e A C₁ F E kq d₀ (answerDelta A F j x)) = _
      rw [h]
    rw [e1]
    rfl
  · have e1 : (bridgeAlg e A C₁ F d₂ E kq d₀).write k x =
        liftAbs e A C₁ F E kq d₀ (answerDelta A F j x) := by
      change (match answerSlot A C₁ k with
        | none => Equiv.refl _
        | some j => liftAbs e A C₁ F E kq d₀ (answerDelta A F j x)) = _
      rw [h]
    rw [e1]
    exact Prod.ext (answerDelta_work A F j x _) (answerDelta_request A F j x _)

/-- **A request of the bridge is the dummy or the outer request of the log of the slot it
answers.** -/
theorem bridgeAlg_req_slot (k : Fin ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁
      id).depth + kq) + 1)) (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).req k w = d₂ ∨ ∃ j r, answerSlot A C₁ k = some j ∧
      cohLogs A C₁ F d₀ w.1 j = some r ∧
      F.outer (A.reqCount (cohLogs A C₁ F d₀ w.1) j) r =
        some ((bridgeAlg e A C₁ F d₂ E kq d₀).req k w) := by
  generalize hv : (bridgeAlg e A C₁ F d₂ E kq d₀).req k w = v
  change (match answerSlot A C₁ k with
    | none => d₂
    | some j => match (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j with
      | none => d₂
      | some r => (F.outer (A.reqCount (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j) r).getD d₂) = v
      at hv
  subst hv
  rcases hs : answerSlot A C₁ k with _ | j
  · left
    simp only
  · rcases hr : (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j with _ | r
    · left
      simp only [hr]
    · rcases hq : F.outer (A.reqCount (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j) r with _ | q
      · left
        simp only [hr, hq, Option.getD_none]
      · right
        refine ⟨j, r, rfl, hr, ?_⟩
        change F.outer (A.reqCount (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j) r = _
        simp only [hr, hq, Option.getD_some]

/-- The pairs of the slot answered (if any) and the request of the entries of a log register other
than the dummy. -/
def ndSlot (lg : LogReg Req₂ ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth
    + kq) + 1)) : Set (Option (Fin A.slots) × Req₂) :=
  {p | ∃ i, lg i = some p.2 ∧ p.2 ≠ d₂ ∧ answerSlot A C₁ i = p.1}

/-- **The request point of the bridge keeps `slotWSet`** for the logs with the request added. -/
theorem slot_bridge_hreq (k : ℕ)
    (hk : k + 1 < (((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth + kq) + 1)
    (x : Option Resp₂) (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) (lg)
    (hw : w ∈ slotWSet e A C₁ F d₂ E kq d₀ T (ndSlot A C₁ F d₂ kq lg) k) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).write ⟨k + 1, hk⟩ x w ∈ slotWSet e A C₁ F d₂ E kq d₀ T
      (ndSlot A C₁ F d₂ kq (Function.update lg ⟨k + 1, hk⟩
        (some ((bridgeAlg e A C₁ F d₂ E kq d₀).req ⟨k + 1, hk⟩ w)))) k := by
  obtain ⟨hl, hf, ha⟩ := bridgeAlg_write_spec e A C₁ F d₂ E kq d₀ ⟨k + 1, hk⟩ x w
  refine slotCohSet_congr A C₁ F d₀ T hw hl
    (bridgeAlg_write_work e A C₁ F d₂ E kq d₀ ⟨k + 1, hk⟩ x w) hf ha ?_
  rintro ⟨o, x'⟩ ⟨i, hi, hne, hj⟩
  rw [hl]
  by_cases hik : i = ⟨k + 1, hk⟩
  · subst hik
    rw [Function.update_self, Option.some.injEq] at hi
    subst hi
    rcases bridgeAlg_req_slot e A C₁ F d₂ E kq d₀ ⟨k + 1, hk⟩ w with h | ⟨j, r, hs, hr, ho⟩
    · exact absurd h hne
    · exact ⟨j, r, hj.symm.trans hs, hr, ho⟩
  · rw [Function.update_of_ne hik] at hi
    exact slotCohSet_outer A C₁ F d₀ T hw (o, x') ⟨i, hi, hne, hj⟩

variable [Nonempty (Bits m)] {T}

/-- **A step of the run of the composition carries `slotCohSet N k` to
`slotCohSet N (k + 1)`.** -/
theorem slotCohStep_supp (hA : A.TracePreserving) (hT : A.LogInv F (tab₀ A) T)
    (N : Set (Option (Fin A.slots) × Req₂)) {k : ℕ}
    (hk : k + 1 ≤ ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries)
    (u : QState (QueryReg ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁
      id).toQueryAlgCoh.mapOut (extOut A C₁ F d₀ (tab₀ A))).W) 1 (Bits m) (BitStr I J)))
    (hu : Supported {r | r.1 ∈ slotCohSet A C₁ F d₀ T N k} u) :
    Supported {r | r.1 ∈ slotCohSet A C₁ F d₀ T N (k + 1)}
      (((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
        (extOut A C₁ F d₀ (tab₀ A))).toOracleAlg ∅).stepAt () (k + 1) u) := by
  have hv := A.valid_slotLogS (F := F) (tab := tab₀ A) hA hT N C₁
  refine stepAt_composeBothOut_supp _ _ _ hv hk ?_
  refine fun r hr => hu r fun h => hr ?_
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, h3 (by omega)⟩
  have e1 : ReprogrammedCircuit.segOut
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.wsG C₁ (A.slotLogS F (tab₀ A) T N))
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁
        (A.slotLogS F (tab₀ A) T N (A.slots + A.post + 1))) 0
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries k =
      (A.absorbTab F (tab₀ A)).toTPKindAlg.wsG C₁ (A.slotLogS F (tab₀ A) T N) (0 + k) := by
    unfold ReprogrammedCircuit.segOut
    rw [if_pos (by omega)]
  rw [e1] at h1
  exact h1

/-- After the composition's last query, `slotCohSet` only grows. -/
theorem slotCohSet_mono_of_le (N : Set (Option (Fin A.slots) × Req₂)) {k : ℕ}
    (hk : ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries ≤ k) :
    slotCohSet A C₁ F d₀ T N k ⊆ slotCohSet A C₁ F d₀ T N (k + 1) := by
  rintro c ⟨h1, h2, -⟩
  refine ⟨?_, h2, fun h => absurd h (by omega)⟩
  unfold ReprogrammedCircuit.segOut at h1 ⊢
  rw [if_neg (by omega)] at h1
  rw [if_neg (by omega)]
  exact h1

/-- **A step of the bridge carries `slotWSet N k` to `slotWSet N (k + 1)`.** -/
theorem slotBridgeStep_supp (hA : A.TracePreserving) (hT : A.LogInv F (tab₀ A) T)
    (N : Set (Option (Fin A.slots) × Req₂)) {k : ℕ}
    (hk : k + 1 < (((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth + kq) + 1)
    (v : QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)))
    (hv : Supported {r | r.1 ∈ slotWSet e A C₁ F d₂ E kq d₀ T N k} v) :
    Supported {r | r.1 ∈ slotWSet e A C₁ F d₂ E kq d₀ T N (k + 1)}
      ((bridgeAlg e A C₁ F d₂ E kq d₀).step ⟨k + 1, hk⟩ v) := by
  have hD : ((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth =
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries :=
    ReprogrammedCircuit.depth_compiledAlg _ _ _ _
  exact ExpandAdvSupp.expandAdv_step_supp e E kq
    ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A)))) (slotCohSet A C₁ F d₀ T N)
    (fun i hi u hu => slotCohStep_supp A C₁ F d₀ hA hT N (by omega) u hu)
    (fun i hi => slotCohSet_mono_of_le A C₁ F d₀ N (by omega)) hk hv

variable (T) in
/-- **The supports of the run of the composition at the start** (proof-internal): the composed
registers with blank absorbed logs and the workspace and logs in `T 0`, the halting flag down, the
ancilla clean. -/
def slotCohInit : Set ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁
    id).toQueryAlgCoh.mapOut (extOut A C₁ F d₀ (tab₀ A))).W) :=
  {c | c.1.1.1 ∈ (A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁ (A.slotLogS F (tab₀ A) T ∅ 0) ∧
    c.1.2 = false ∧ MixedAlg.Clean 0 c.2}

/-- **The initial state of the composition has blank absorbed logs, its workspace and logs in
`T 0`.** -/
theorem initSys_slot (hT : A.LogInv F (tab₀ A) T)
    (p : QueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) 1 (Bits m) (BitStr I J))
    (hp : ((A.absorbTab F (tab₀ A)).toTPKindAlg.initSys C₁).mat p p ≠ 0) :
    p.1 ∈ (A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁ (A.slotLogS F (tab₀ A) T ∅ 0) := by
  change (∑ ω, (_ : ℂ) • (MState.reindex ((A.absorbTab F (tab₀ A)).toTPKindAlg.advSplit C₁)
    (((A.absorbTab F (tab₀ A)).toTPKindAlg.init).tensorKet _)).mat) p p ≠ 0 at hp
  rw [Matrix.sum_apply] at hp
  obtain ⟨ω, -, hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  rw [Matrix.smul_apply, smul_eq_mul] at hω
  have h2 := right_ne_zero_of_mul hω
  rw [MState.reindex_tensorKet_mat] at h2
  obtain ⟨d, d', hd, -, hdd⟩ := embed_ne_zero_exists h2
  subst hd
  exact ⟨fun j _ => init_logs_none A F hdd j, fun x hx => absurd hx (Set.notMem_empty x),
    hT.init d d' hdd⟩

/-- **The initial state of the run of the composition lies on `slotCohInit`.** -/
theorem slotCohInit_supp (hT : A.LogInv F (tab₀ A) T) :
    Supported {r : QueryReg ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁
      id).toQueryAlgCoh.mapOut (extOut A C₁ F d₀ (tab₀ A)))).W 1 (Bits m) (BitStr I J) |
        r.1 ∈ slotCohInit A C₁ F d₀ T}
      ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A)))).init :=
  (GordieHowe.QROM.compiled_init_props (initSys_slot A C₁ F hT)).1.mono
      fun _ hr => ⟨hr.2.2.2, hr.2.1, hr.2.2.1⟩

variable (T) in
/-- The bridge's work register at the start (proof-internal): the run of the composition in
`slotCohInit`. -/
def slotInitW : Set (bridgeAlg e A C₁ F d₂ E kq d₀).W :=
  {w | w.1 ∈ slotCohInit A C₁ F d₀ T}

/-- **The bridge's initial state lies on `slotInitW`.** -/
theorem slot_bridge_init_supp (hT : A.LogInv F (tab₀ A) T) :
    Supported {r | r.1 ∈ slotInitW e A C₁ F d₂ E kq d₀ T} (bridgeAlg e A C₁ F d₂ E kq d₀).init := by
  intro r hr
  rw [bridgeAlg_init_eq, ExpandAdv.embed]
  erw [relabel_apply, Equiv.symm_symm, tensorKet_apply]
  erw [slotCohInit_supp A C₁ F d₀ hT ((r.1.1, r.2)) hr, zero_mul]

/-- Membership in `slotCohInit`, by its parts. -/
theorem mem_slotCohInit {c} : c ∈ slotCohInit A C₁ F d₀ T ↔
    (∀ j, cohLogs A C₁ F d₀ c j = none) ∧ (cohWork A C₁ F d₀ c, cohLogs A C₁ F d₀ c) ∈ T 0 ∧
      c.1.2 = false ∧ MixedAlg.Clean 0 c.2 := by
  constructor
  · rintro ⟨⟨hb, -, hT0⟩, h2, h3⟩
    exact ⟨fun j => hb j (Nat.zero_le _), hT0, h2, h3⟩
  · rintro ⟨hb, hT0, h2, h3⟩
    exact ⟨⟨fun j _ => hb j, fun x hx => absurd hx (Set.notMem_empty x), hT0⟩, h2, h3⟩

/-- **The bridge's write at step `0` keeps `slotCohInit`.** -/
theorem slot_bridge_write0_init (x : Option Resp₂) (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W)
    (hw : w.1 ∈ slotCohInit A C₁ F d₀ T) :
    ((bridgeAlg e A C₁ F d₂ E kq d₀).write 0 x w).1 ∈ slotCohInit A C₁ F d₀ T := by
  have hs := bridgeAlg_write_spec e A C₁ F d₂ E kq d₀ 0 x w
  have hwk := bridgeAlg_write_work e A C₁ F d₂ E kq d₀ 0 x w
  have hm := (mem_slotCohInit A C₁ F d₀ (T := T) (c := w.1)).1 hw
  have hT0' : (cohWork A C₁ F d₀ ((bridgeAlg e A C₁ F d₂ E kq d₀).write 0 x w).1,
      cohLogs A C₁ F d₀ ((bridgeAlg e A C₁ F d₂ E kq d₀).write 0 x w).1) ∈ T 0 :=
    (congrArg (fun p => p ∈ T 0) (Prod.ext hwk hs.1)).mpr hm.2.1
  exact (mem_slotCohInit A C₁ F d₀ (T := T)
    (c := ((bridgeAlg e A C₁ F d₂ E kq d₀).write 0 x w).1)).2
    ⟨fun j => (congrFun hs.1 j).trans (hm.1 j), hT0', hs.2.1.trans hm.2.2.1,
      (congrArg (MixedAlg.Clean 0) hs.2.2).mpr hm.2.2.2⟩

/-- **The request of step `0` adds no pair**: the logs are blank at the start. -/
theorem slot_bridge_req0_nd (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W)
    (hw : w.1 ∈ slotCohInit A C₁ F d₀ T) :
    ndSlot A C₁ F d₂ kq (Function.update (fun _ => none) 0
      (some ((bridgeAlg e A C₁ F d₂ E kq d₀).req 0 w))) = ∅ := by
  have hb := ((mem_slotCohInit A C₁ F d₀).1 hw).1
  refine Set.eq_empty_of_forall_notMem fun x' hx' => ?_
  obtain ⟨i, hi, hne, -⟩ := hx'
  by_cases hi0 : i = 0
  · rw [hi0, Function.update_self] at hi
    have hq : (bridgeAlg e A C₁ F d₂ E kq d₀).req 0 w = x'.2 := Option.some.inj hi
    rcases bridgeAlg_req_slot e A C₁ F d₂ E kq d₀ 0 w with h | ⟨j, r, -, hj, -⟩
    · exact hne (hq ▸ h)
    · exact absurd ((hb j).symm.trans hj) (Option.some_ne_none r).symm
  · rw [Function.update_of_ne hi0] at hi
    exact absurd hi (Option.some_ne_none x'.2).symm

/-- **The first step of the run of the composition carries `slotCohInit` into
`slotCohSet ∅ 0`.** -/
theorem slotCohInit_step0 (hA : A.TracePreserving) (hT : A.LogInv F (tab₀ A) T)
    (u : QState (QueryReg ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁
      id).toQueryAlgCoh.mapOut (extOut A C₁ F d₀ (tab₀ A))).W) 1 (Bits m) (BitStr I J)))
    (hu : Supported {r | r.1 ∈ slotCohInit A C₁ F d₀ T} u) :
    Supported {r | r.1 ∈ slotCohSet A C₁ F d₀ T ∅ 0}
      (((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
        (extOut A C₁ F d₀ (tab₀ A))).toOracleAlg ∅).stepAt () 0 u) := by
  have hv := A.valid_slotLogS (F := F) (tab := tab₀ A) hA hT ∅ C₁
  refine stepAt_composeBothOut_supp _ _ _ hv (Nat.zero_le _) ?_
  refine fun r hr => hu r fun h => hr ?_
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

/-- **The first step of the bridge carries `slotInitW` into `slotWSet ∅ 0`.** -/
theorem slot_bridge_hstep0 (hA : A.TracePreserving) (hT : A.LogInv F (tab₀ A) T)
    (v : QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)))
    (hv : Supported {r | r.1 ∈ slotInitW e A C₁ F d₂ E kq d₀ T} v) :
    Supported {r | r.1 ∈ slotWSet e A C₁ F d₂ E kq d₀ T ∅ 0}
      ((bridgeAlg e A C₁ F d₂ E kq d₀).step 0 v) := by
  have h := ExpandAdvSupp.expandAdv_step0_supp e E kq
    ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A)))) (slotCohInit_step0 A C₁ F d₀ hA hT) hv
  exact h

/-- **The slot form of the requests of the bridge read after permutations** (module docstring):
for permutations `π` keeping the supports of the bridge's steps (`hπ0`, `hπ`), a trace-preserving
adversary, sets `T` carried by its steps (`hT`) and every reply family `a`, on every basis state of
the compressed-oracle simulation of the bridge's instance, the workspace and the absorbed logs that
the output reads lie in `T (slots + post + 1)`, and every logged request is the dummy `d₂` or the
outer request of the output's log of the slot that its request point answers. -/
theorem bridgeAlg_withPerm_slotLogs
    (π : Fin ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth) + kq + 1) →
      Equiv.Perm (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)))
    (hπ0 : ∀ r : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J),
      r.1 ∈ slotInitW e A C₁ F d₂ E kq d₀ T → (π 0 r).1 ∈ slotInitW e A C₁ F d₂ E kq d₀ T)
    (hπ : ∀ N k (hk : k + 1 < (((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth)
        + kq + 1) (r : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)),
      r.1 ∈ slotWSet e A C₁ F d₂ E kq d₀ T N k →
        (π ⟨k + 1, hk⟩ r).1 ∈ slotWSet e A C₁ F d₂ E kq d₀ T N k)
    (hA : A.TracePreserving) (hT : A.LogInv F (tab₀ A) T)
    (a : ℕ → Req₂ → Option Resp₂)
    {b : SimRegister (((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm π).inst a).W I J m
      ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth) + kq)}
    (hb : simState e (((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm π).inst a) b ≠ 0) :
    ((((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.work,
        ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.request),
        ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.logs) ∈
          T (A.slots + A.post + 1) ∧
      ∀ i q, b.1.1.2 i = some q → q = d₂ ∨ ∃ j r, answerSlot A C₁ i = some j ∧
        ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.logs j = some r ∧
        F.outer (A.reqCount ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.logs j) r =
          some q := by
  have hs := ReqQueryAlg.supported_simState_withPerm_inst_by e (bridgeAlg e A C₁ F d₂ E kq d₀) a
    (slotWSet e A C₁ F d₂ E kq d₀ T) (ndSlot A C₁ F d₂ kq) π
    (slotInitW e A C₁ F d₂ E kq d₀ T) ∅
    (slot_bridge_init_supp e A C₁ F d₂ E kq d₀ hT)
    (fun x w hw => ⟨slot_bridge_write0_init e A C₁ F d₂ E kq d₀ x w hw,
      slot_bridge_req0_nd e A C₁ F d₂ E kq d₀ w hw⟩)
    (fun v hv => slot_bridge_hstep0 e A C₁ F d₂ E kq d₀ hA hT v hv)
    (fun N k hk v hv => slotBridgeStep_supp e A C₁ F d₂ E kq d₀ hA hT N hk v hv)
    (fun k hk x w lg _ hw => slot_bridge_hreq e A C₁ F d₂ E kq d₀ T k hk x w lg hw) hπ0 hπ
  have hmem : b.1.1 ∈ ((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm π).instSetBy (slotWSet e A C₁ F d₂ E kq d₀ T)
      (ndSlot A C₁ F d₂ kq) ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth)
        + kq) := by
    by_contra h
    exact hb (hs b h)
  obtain ⟨-, hw⟩ := hmem
  have hflag : b.1.1.1.1.1.2 = false := hw.2.1
  have hlogs : ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.logs =
      cohLogs A C₁ F d₀ b.1.1.1.1 := by
    change (extOut A C₁ F d₀ (tab₀ A) (Alg.haltOutCoh _ b.1.1.1.1)).adv.1.1.1.logs = _
    simp only [Alg.haltOutCoh, hflag]
    rfl
  have hwork : (((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.work,
      ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.request) =
      cohWork A C₁ F d₀ b.1.1.1.1 := by
    change ((extOut A C₁ F d₀ (tab₀ A) (Alg.haltOutCoh _ b.1.1.1.1)).adv.1.1.1.work,
      (extOut A C₁ F d₀ (tab₀ A) (Alg.haltOutCoh _ b.1.1.1.1)).adv.1.1.1.request) = _
    simp only [Alg.haltOutCoh, hflag]
    rfl
  have hD : ((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth =
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries :=
    ReprogrammedCircuit.depth_compiledAlg _ _ _ _
  rw [hlogs, hwork]
  refine ⟨slotCohSet_final A C₁ F d₀ T (by omega) hw, fun i q hq => ?_⟩
  by_cases hd : q = d₂
  · exact Or.inl hd
  · right
    exact slotCohSet_outer A C₁ F d₀ T hw (answerSlot A C₁ i, q) ⟨i, hq, hd, rfl⟩

-- The corollaries below read the bridge as a value, not through its definition.
set_option allowUnsafeReducibility true in
attribute [local irreducible] GordieHowe.Quantum.bridgeAlg

/-- **The slot form of the bridge's requests**: `bridgeAlg_withPerm_slotLogs` without
permutations. -/
theorem bridgeAlg_slotLogs (hA : A.TracePreserving) (hT : A.LogInv F (tab₀ A) T)
    (a : ℕ → Req₂ → Option Resp₂)
    {b : SimRegister ((bridgeAlg e A C₁ F d₂ E kq d₀).inst a).W I J m
      ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth) + kq)}
    (hb : simState e ((bridgeAlg e A C₁ F d₂ E kq d₀).inst a) b ≠ 0) :
    ((((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.work,
        ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.request),
        ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.logs) ∈
          T (A.slots + A.post + 1) ∧
      ∀ i q, b.1.1.2 i = some q → q = d₂ ∨ ∃ j r, answerSlot A C₁ i = some j ∧
        ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.logs j = some r ∧
        F.outer (A.reqCount ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.logs j) r =
          some q := by
  have hb' : simState e (((bridgeAlg e A C₁ F d₂ E kq d₀).withPerm fun _ => 1).inst a) b ≠ 0 :=
    hb
  exact bridgeAlg_withPerm_slotLogs e A C₁ F d₂ E kq d₀ (fun _ => 1) (fun _ hr => hr)
    (fun _ _ _ _ hr => hr) hA hT a hb'

/-- **Every logged request of the bridge is the dummy or an outer request** of a logged request
of the absorbed logs the output reads: `bridgeAlg_slotLogs` at the sets of all workspaces and
logs. -/
theorem bridgeAlg_logs (hA : A.TracePreserving) (a : ℕ → Req₂ → Option Resp₂)
    {b : SimRegister ((bridgeAlg e A C₁ F d₂ E kq d₀).inst a).W I J m
      ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth) + kq)}
    (hb : simState e ((bridgeAlg e A C₁ F d₂ E kq d₀).inst a) b ≠ 0)
    {i : Fin ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth + kq) + 1)}
    {q : Req₂} (hq : b.1.1.2 i = some q) :
    q = d₂ ∨ ∃ j r, ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.logs j = some r ∧
      F.outer (A.reqCount ((bridgeAlg e A C₁ F d₂ E kq d₀).out b.1.1.1).out.adv.1.1.1.logs j) r =
        some q := by
  rcases (bridgeAlg_slotLogs e A C₁ F d₂ E kq d₀ hA (AdaptiveIAlg.LogInv.univ A F (tab₀ A)) a
    hb).2 i q hq with h | ⟨j, r, -, hr, hq'⟩
  · exact Or.inl h
  · exact Or.inr ⟨j, r, hr, hq'⟩

end Bridge

end GordieHowe.Quantum
