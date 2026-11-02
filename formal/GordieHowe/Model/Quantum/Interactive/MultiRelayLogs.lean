-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.MultiRelay
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeSlots
public import GordieHowe.Model.Quantum.Pure.MultiRelayCount
public import GordieHowe.Model.Quantum.Interactive.RelayBlockSwap

@[expose] public section

/-!
# The logged requests of the relayed adversary

The relayed adversary `AdaptiveIAlg.relayAdv A F Q out'`
(`GordieHowe/Model/Quantum/Interactive/MultiRelay.lean`), absorbed with a table through any relay
`G` (`AdaptiveIAlg.absorbTab`), logs at most `K · Q` main requests satisfying a test `p` that the
idle request and the blank request fail: sets of its workspaces, request registers and absorbed
logs carried by its steps (`AdaptiveIAlg.LogInv`) end in the set of logs with at most `K · Q` such
requests (`relayAdv_logInv`). The sets read only the relay's record, stored answers, clock and main
request register (`Distinguisher.Booked`), which the relayed distinguisher's own steps keep.

- `AdaptiveIAlg.stepTab_rel`: a nonzero entry of a step of the adversary absorbed with a table is
  one of the adversary's step on the workspaces and request registers, the absorbed logs kept but
  at the step's slot, where the request is logged when the adversary's kind is a request.
- `AdaptiveIAlg.tp_absorbTab_rel`: the same for the trace-preserving form.
- `AdaptiveIAlg.afterPermTab_work_request`, `AdaptiveIAlg.afterAtTab_parts`,
  `AdaptiveIAlg.setAt_parts`: the absorbed bookkeeping of a step.
- `AdaptiveIAlg.supported_single_any`, `AdaptiveIAlg.relayA`, `AdaptiveIAlg.relayAdv_step_rel`: a
  nonzero entry of a step of the relayed adversary is a step of the relayed distinguisher on the
  registers outside the distinguisher's (`Distinguisher.relay_step_supp`).
- `AdaptiveIAlg.RelayFull`, `AdaptiveIAlg.CountLE`: the bookkeeping before each step (the carried
  sets) and the count; `AdaptiveIAlg.countLE_of_relayFull` (the count from
  the bookkeeping, `MultiRelay.card_asksAt_le`), `AdaptiveIAlg.ask_of_askOf`,
  `AdaptiveIAlg.log_cases`, `AdaptiveIAlg.relayFull_step`, `AdaptiveIAlg.relayFull_init`.
- `AdaptiveIAlg.relayAdv_logInv`, `AdaptiveIAlg.relayAdv_logs_le` (**the count of the relayed
  adversary's logged requests**).
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

namespace AdaptiveIAlg

section Tab

variable {X Y Req Resp O Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)

omit [Fintype Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Fintype Req₂] [DecidableEq Req₂]
  [Fintype Resp₂] [DecidableEq Resp₂] in
/-- The handling of a slot's reply from the table keeps the workspace and the request register. -/
theorem afterPermTab_work_request (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    (A.afterPermTab F t j d).1.1.work = d.1.1.work ∧
      (A.afterPermTab F t j d).1.1.request = d.1.1.request := by
  have h1 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁,
      (A.storePerm j d').1.1.work = d'.1.1.work ∧
        (A.storePerm j d').1.1.request = d'.1.1.request := fun d' => by
    unfold AdaptiveIAlg.storePerm AlgShape.storePerm
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    by_cases h : (d'.1.1.logs j).isSome = true
    · rw [if_pos h]
      exact ⟨rfl, rfl⟩
    · rw [if_neg h]
      exact ⟨rfl, rfl⟩
  have h2 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁,
      (A.answerPermTab F t j d').1.1.work = d'.1.1.work ∧
        (A.answerPermTab F t j d').1.1.request = d'.1.1.request := fun d' => by
    unfold AdaptiveIAlg.answerPermTab
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    split <;> exact ⟨rfl, rfl⟩
  have h3 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁,
      (A.clearPerm F.base j d').1.1.work = d'.1.1.work ∧
        (A.clearPerm F.base j d').1.1.request = d'.1.1.request := fun d' => by
    unfold AdaptiveIAlg.clearPerm AlgShape.clearPerm
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    split <;> exact ⟨rfl, rfl⟩
  unfold AdaptiveIAlg.afterPermTab
  simp only [Equiv.trans_apply]
  exact ⟨(h3 _).1.trans ((h2 _).1.trans (h1 _).1), (h3 _).2.trans ((h2 _).2.trans (h1 _).2)⟩

/-- The handling of slot `k - 1`'s reply from the table keeps the workspace, the request register
and the absorbed logs. -/
theorem afterAtTab_parts (k : ℕ)
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    (A.afterAtTab F k d).1.1.1.work = d.1.1.1.work ∧
      (A.afterAtTab F k d).1.1.1.request = d.1.1.1.request ∧
      (A.afterAtTab F k d).1.1.1.logs = d.1.1.1.logs := by
  refine ⟨?_, ?_, A.afterAtTab_logs' F k d⟩
  · unfold AdaptiveIAlg.afterAtTab
    split
    · exact (A.afterPermTab_work_request F _ _ _).1
    · rfl
  · unfold AdaptiveIAlg.afterAtTab
    split
    · exact (A.afterPermTab_work_request F _ _ _).2
    · rfl

omit [Fintype Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Fintype Req₂] [DecidableEq Req₂]
  [Fintype Resp₂] [DecidableEq Resp₂] in
/-- **The request of slot `k`**: logging the request keeps the workspace and the request register
and changes the absorbed logs only at slot `k`, where the request is logged when the kind is a
request. -/
theorem setAt_parts (k : ℕ) (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    (A.setAt F.base k d).1.1.work = d.1.1.work ∧ (A.setAt F.base k d).1.1.request = d.1.1.request ∧
      ∀ j : Fin A.slots, (A.setAt F.base k d).1.1.logs j =
        if (j : ℕ) = k ∧ A.kind d.1.1.work = true then
          Equiv.swap none (some d.1.1.request) (d.1.1.logs j)
        else d.1.1.logs j := by
  rw [AdaptiveIAlg.setAt_def]
  split
  · rename_i hk
    unfold AdaptiveIAlg.setPerm AlgShape.setPerm
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    split
    · rename_i hkd
      refine ⟨rfl, rfl, fun j => ?_⟩
      by_cases hj : (j : ℕ) = k
      · have : j = ⟨k, hk⟩ := Fin.ext hj
        subst this
        simp [hkd]
      · dsimp only
        rw [Function.update_of_ne (fun e => hj (by rw [e])), if_neg (fun h => hj h.1)]
    · rename_i hkd
      refine ⟨rfl, rfl, fun j => ?_⟩
      rw [if_neg (fun h => hkd h.2)]
  · rename_i hk
    refine ⟨rfl, rfl, fun j => ?_⟩
    rw [if_neg (fun (h : (j : ℕ) = k ∧ _) => hk (h.1 ▸ j.isLt))]
    rfl

/-- **A nonzero entry of a step of the adversary absorbed with a table** is a nonzero entry of the
adversary's step on its registers, whose workspaces and request registers are those of the
absorbed registers, the absorbed logs kept but at the step's slot, where the request is logged when
the adversary's kind is a request. -/
theorem stepTab_rel {k : StepIdx A.slots A.post} {r : (A.absorb F.base).R}
    {y x : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁}
    (h : (A.stepTab F k).op r y x ≠ 0) :
    ∃ (r' : A.R) (a b : DReg A.W A.width X Y Req Resp), (A.step k).op r' a b ≠ 0 ∧
      a.1.1 = y.1.1.1.work ∧ a.1.2.1 = y.1.1.1.request ∧
      b.1.1 = x.1.1.1.work ∧ b.1.2.1 = x.1.1.1.request ∧
      ∀ j : Fin A.slots, y.1.1.1.logs j =
        if (j : ℕ) = k ∧ A.kind y.1.1.1.work = true then
          Equiv.swap none (some y.1.1.1.request) (x.1.1.1.logs j)
        else x.1.1.1.logs j := by
  simp only [stepTab_eq, KrausMap.comp, Matrix.mul_apply] at h
  obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hyu : y = A.tabLift F (A.setAt F.base k) u := by
    have := left_ne_zero_of_mul hu
    rw [KrausMap.ofPerm_op_apply] at this
    by_contra hne
    exact this (if_neg hne)
  obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hu)
  have hvx : v = A.afterAtTab F k x := by
    have := right_ne_zero_of_mul hv
    rw [KrausMap.ofPerm_op_apply] at this
    by_contra hne
    exact this (if_neg hne)
  have hL := left_ne_zero_of_mul hv
  rw [KrausMap.tensorId_reindex_op_apply] at hL
  have h1 := right_ne_zero_of_mul hL
  have h2 := left_ne_zero_of_mul hL
  rw [liftedStep, AlgShape.liftedStep, KrausMap.tensorId_reindex_op_apply] at h2
  have h3 := right_ne_zero_of_mul h2
  have h4 := left_ne_zero_of_mul h2
  have hrest : u.1.1.1.logs = v.1.1.1.logs := by
    by_contra hne
    apply h3
    refine Matrix.one_apply_ne fun he => hne ?_
    exact congrArg (fun p => p.1) he
  obtain ⟨hs1, hs2, hs3⟩ := A.setAt_parts F k ((u.1.1.1, u.1.2), u.2)
  obtain ⟨ha1, ha2, ha3⟩ := A.afterAtTab_parts F k x
  refine ⟨r.1.2, _, _, h4, ?_, ?_, ?_, ?_, fun j => ?_⟩
  · rw [hyu]
    exact hs1.symm
  · rw [hyu]
    exact hs2.symm
  · change v.1.1.1.work = _
    rw [hvx, ha1]
  · change v.1.1.1.request = _
    rw [hvx, ha2]
  · rw [hyu]
    change (A.setAt F.base k ((u.1.1.1, u.1.2), u.2)).1.1.logs j = if (j : ℕ) = k ∧
      A.kind (A.setAt F.base k ((u.1.1.1, u.1.2), u.2)).1.1.work = true then
        Equiv.swap none (some (A.setAt F.base k ((u.1.1.1, u.1.2), u.2)).1.1.request)
          (x.1.1.1.logs j) else x.1.1.1.logs j
    rw [hs3 j, hs1, hs2]
    change (if (j : ℕ) = k ∧ A.kind u.1.1.1.work = true then
        Equiv.swap none (some u.1.1.1.request) (u.1.1.1.logs j) else u.1.1.1.logs j) = _
    rw [hrest, hvx, ha3]

/-- **A nonzero entry of a step of the trace-preserving form of the adversary absorbed with a
table** (`stepTab_rel` through `toTPKindAlg_op_ne_zero`), for a trace-preserving adversary. -/
theorem tp_absorbTab_rel (hA : A.TracePreserving) (tab : A.OuterTab Req₂ Resp₂)
    {k : StepIdx A.slots A.post}
    {z : (A.absorbTab F tab).R ⊕ ((A.absorbTab F tab).R ⊕ Fin (A.budget + 2))}
    {y x : DReg (A.absorbTab F tab).toTPKindAlg.W A.width X Y Req₁ Resp₁}
    (h : ((A.absorbTab F tab).toTPKindAlg.step k).op z y x ≠ 0) :
    ∃ (r' : A.R) (a b : DReg A.W A.width X Y Req Resp), (A.step k).op r' a b ≠ 0 ∧
      a.1.1 = y.workspace.1.1.work ∧ a.1.2.1 = y.workspace.1.1.request ∧
      b.1.1 = x.workspace.1.1.work ∧ b.1.2.1 = x.workspace.1.1.request ∧
      ∀ j : Fin A.slots, y.workspace.1.1.logs j =
        if (j : ℕ) = k ∧ A.kind y.workspace.1.1.work = true then
          Equiv.swap none (some y.workspace.1.1.request) (x.workspace.1.1.logs j)
        else x.workspace.1.1.logs j := by
  obtain ⟨r, hr⟩ := (A.absorbTab F tab).toTPKindAlg_op_ne_zero
    (fun k => TracePreserving.haltOp_eq_zero (A.absorbTab_tracePreserving F hA tab) k) h
  exact A.stepTab_rel F hr

end Tab

/-- **A basis vector is supported on its index**, for any decidable equality. -/
theorem supported_single_any {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (q : ι) :
    Supported {q} (@EuclideanSpace.single ι ℂ _ inst q 1) := fun x hx => by
  rw [PiLp.single_apply, if_neg (show x ≠ q from hx)]

section Relay

open Classical

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) [AddGroup Y]
  {Req' Resp' O' Xs Ys : Type} [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)
  (out' : A.RelayWS F → O')

/-- The adversary of the relayed distinguisher, before its aborting completion. -/
noncomputable abbrev relayA :=
  (A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out'

/-- **A nonzero entry of a step of the relayed adversary** is, on the relayed distinguisher's
registers (the counter dropped), the set-up and record of a state `z` that agrees outside the
distinguisher's registers with the earlier registers (step `0`) or with their tear-down, clock,
side additions and reply (the later steps). -/
theorem relayAdv_step_rel {k : StepIdx (A.relayAdv F Q out').slots (A.relayAdv F Q out').post}
    {r : (A.relayAdv F Q out').R}
    {a b : DReg (A.relayAdv F Q out').W (A.relayAdv F Q out').width X Y Req' Resp'}
    (h : ((A.relayAdv F Q out').step k).op r a b ≠ 0) :
    ∃ z, ((A.relayA F Q out').cntSplit a).1 = Distinguisher.setupFun F (A.budget + A.post) Q
          (Distinguisher.recordFun F (A.budget + A.post) Q A.pureD.kind z) ∧
      Distinguisher.rest F z = Distinguisher.rest F (if (k : ℕ) = 0 then
        ((A.relayA F Q out').cntSplit b).1 else
        Distinguisher.finalizeFun F (A.budget + A.post) Q (Distinguisher.sideAddsPerm F
          (A.budget + A.post) Q (Distinguisher.tickPerm F
          (Distinguisher.teardownFun F (A.budget + A.post) Q
            ((A.relayA F Q out').cntSplit b).1)))) := by
  obtain ⟨r', hr'⟩ := (A.relayA F Q out').toTPKindAlg_op_ne_zero
    (fun k => TracePreserving.haltOp_eq_zero
      (Distinguisher.toAdaptive_tracePreserving _ _ _ _) k) h
  simp only [relayA, Distinguisher.toAdaptive_step, KrausChannel.toKrausMap, KrausChannel.ofUnitary,
    unitaryMat] at hr'
  rw [Distinguisher.stepAt] at hr'
  split_ifs at hr' with hk
  · by_contra hne
    rw [A.relayD_step] at hr'
    exact hr' (Distinguisher.relay_step_supp F (A.budget + A.post) Q A.pureD ⟨k, hk⟩
      (supported_single_any _) _ fun ⟨z, hz⟩ => hne ⟨z, hz⟩)
  · exact absurd k.isLt hk

/-! ### The sets carried by the relayed adversary's steps -/

variable (p : Req' → Bool)

/-- **The bookkeeping of the relayed adversary before step `t`** (proof-internal), on its workspace,
its request register and its absorbed logs: before step `0`, the clock at `0`, a blank record, a
blank main request register and blank logs; before step `t + 1`, the relay's bookkeeping after the
set-up of sub-slot `t` with the started slots `es` (`Distinguisher.Booked`), the logs blank after
`t`, and every logged request satisfying `p` an ask of a relayed request (`MultiRelay.AsksAt`). -/
def RelayFull : ℕ → Set (((A.relayAdv F Q out').W × Req') ×
    LogReg Req' (A.relayAdv F Q out').slots)
  | 0 => {x | (x.1.1.1.time : ℕ) = 0 ∧ x.1.1.1.record = (fun _ => none) ∧ x.1.2 = default ∧
      (∀ j, x.2 j = none) ∧ x.1.1.1.side = 0}
  | t + 1 => {x | ∃ es, (x.1.1.1.time : ℕ) = t ∧
      Distinguisher.RecAt (n := (A.toTPKindAlg true).unitOut.width) F (A.budget + A.post) Q
        x.1.1.1.record es t ∧
      x.1.2 = Distinguisher.askOf (F.actAt (A.toTPKindAlg true).unitOut.width (A.budget + A.post) Q
        x.1.1.1.record x.1.1.1.store x.1.1.1.side x.1.1.1.time) ∧
      (∀ j : Fin (A.relayAdv F Q out').slots, t < (j : ℕ) → x.2 j = none) ∧
      (∀ j r', x.2 j = some r' → p r' = true →
        F.AsksAt (A.toTPKindAlg true).unitOut.width (A.budget + A.post) Q es x.1.1.1.store x.1.1.1.side
          j r') ∧
      x.1.1.1.side = F.consSide (A.toTPKindAlg true).unitOut.width (A.budget + A.post) Q x.1.1.1.record
        x.1.1.1.store x.1.1.1.time}

/-- The logs with at most `K · Q` requests satisfying `p`. -/
def CountLE : Set (((A.relayAdv F Q out').W × Req') × LogReg Req' (A.relayAdv F Q out').slots) :=
  {x | (Finset.univ.filter fun j => (x.2 j).any p = true).card ≤ F.K * Q}

/-- **The bookkeeping bounds the count**: before every step, the logged requests satisfying `p`
are at most `K · Q`. -/
theorem countLE_of_relayFull {t : ℕ} {x} (hx : x ∈ A.RelayFull F Q out' p t) :
    x ∈ A.CountLE F Q out' p := by
  classical
  rcases t with _ | t
  · obtain ⟨-, -, -, hl, -⟩ := hx
    change (Finset.univ.filter fun j => (x.2 j).any p = true).card ≤ F.K * Q
    rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun j _ => by simp [hl j])]
    exact Nat.zero_le _
  · obtain ⟨es, -, -, -, -, hask, -⟩ := hx
    refine (Finset.card_le_card fun j hj => ?_).trans
      (MultiRelay.card_asksAt_le (F := F) (n := (A.toTPKindAlg true).unitOut.width)
        (b := A.budget + A.post) (Q := Q) es x.1.1.1.store x.1.1.1.side p)
    have hj' := (Finset.mem_filter.1 hj).2
    rcases hx2 : x.2 j with _ | r'
    · rw [hx2] at hj'
      exact absurd hj' (by simp)
    · rw [hx2, Option.any_some] at hj'
      exact (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).2
        ⟨Finset.mem_univ _, r', hask j r' hx2 hj', hj'⟩

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Fintype Req]
  [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req']
  [Fintype Resp'] [DecidableEq Resp'] [Inhabited X] in
/-- **A main request satisfying `p` left by a set-up is the sub-slot's main request**, when the
blank and the idle requests fail `p`. -/
theorem ask_of_askOf (hpd : p default = false) (hpi : p F.idle = false) {n : ℕ}
    {a : SubAct X Req' n} {r' : Req'} (h : r' = Distinguisher.askOf a) (hp : p r' = true) :
    a = .ask r' ∧ r' ≠ F.idle := by
  cases a with
  | pair i =>
    simp only [Distinguisher.askOf] at h
    rw [h, hpd] at hp
    exact absurd hp Bool.false_ne_true
  | query x =>
    simp only [Distinguisher.askOf] at h
    rw [h, hpd] at hp
    exact absurd hp Bool.false_ne_true
  | ask r'' =>
    simp only [Distinguisher.askOf] at h
    subst h
    refine ⟨rfl, fun he => ?_⟩
    rw [he, hpi] at hp
    exact absurd hp Bool.false_ne_true

variable {Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁]
  [DecidableEq Resp₁] [Inhabited Req₁] [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂]
  [DecidableEq Resp₂] (G : TwoRelay Req' Resp' Req₁ Resp₁ Req₂ Resp₂)
  (tab : (A.relayAdv F Q out').OuterTab Req₂ Resp₂)

omit [Fintype Req'] [Inhabited Req'] in
/-- **A logged request after a step**: the request register at the step's slot, or a request
logged before. -/
theorem log_cases {S : ℕ} {k : ℕ} {kind : Bool} {rq : Req'} {lx ly : LogReg Req' S}
    (hlog : ∀ j : Fin S, ly j = if (j : ℕ) = k ∧ kind = true then
      Equiv.swap none (some rq) (lx j) else lx j)
    (hblank : ∀ j : Fin S, (j : ℕ) = k → lx j = none) {j : Fin S} {r' : Req'}
    (h : ly j = some r') : ((j : ℕ) = k ∧ r' = rq) ∨ ((j : ℕ) ≠ k ∧ lx j = some r') := by
  rw [hlog j] at h
  by_cases hj : (j : ℕ) = k
  · rw [hblank j hj] at h
    by_cases hk : (j : ℕ) = k ∧ kind = true
    · rw [if_pos hk, Equiv.swap_apply_left] at h
      exact Or.inl ⟨hj, (Option.some.inj h).symm⟩
    · rw [if_neg hk] at h
      exact absurd h (by simp)
  · right
    rw [if_neg (fun hk => hj hk.1)] at h
    exact ⟨hj, h⟩

/-- **The steps carry the bookkeeping**: step `j` carries `RelayFull j` into `RelayFull (j + 1)`,
when the blank and the idle requests fail `p`. -/
theorem relayFull_step (hpd : p default = false) (hpi : p F.idle = false)
    (j : StepIdx (A.relayAdv F Q out').slots (A.relayAdv F Q out').post) {z}
    {y x : DReg ((A.relayAdv F Q out').absorbTab G tab).toTPKindAlg.W
      (A.relayAdv F Q out').width X Y Req₁ Resp₁}
    (h : (((A.relayAdv F Q out').absorbTab G tab).toTPKindAlg.step j).op z y x ≠ 0)
    (hx : ((x.workspace.1.1.work, x.workspace.1.1.request), x.workspace.1.1.logs) ∈
      A.RelayFull F Q out' p j) :
    ((y.workspace.1.1.work, y.workspace.1.1.request), y.workspace.1.1.logs) ∈
      A.RelayFull F Q out' p (j + 1) := by
  obtain ⟨r', a, b, hab, ha1, ha2, hb1, hb2, hlog⟩ := (A.relayAdv F Q out').tp_absorbTab_rel G
    (A.relayAdv_tracePreserving F Q out') tab h
  obtain ⟨zz, hpa, hrest⟩ := A.relayAdv_step_rel F Q out' hab
  have hn : 0 < (A.toTPKindAlg true).unitOut.width := (A.toTPKindAlg true).unitOut.width_pos
  have hy1 : y.workspace.1.1.work.1 = (((A.relayA F Q out').cntSplit a).1).1.1 := by
    rw [← ha1]
    rfl
  have hy2 : y.workspace.1.1.request = (((A.relayA F Q out').cntSplit a).1).1.2.1 := by
    rw [← ha2]
    rfl
  have hx1 : x.workspace.1.1.work.1 = (((A.relayA F Q out').cntSplit b).1).1.1 := by
    rw [← hb1]
    rfl
  have hx2 : x.workspace.1.1.request = (((A.relayA F Q out').cntSplit b).1).1.2.1 := by
    rw [← hb2]
    rfl
  -- the new log is the request register, the others are kept
  have hcases := fun (hbl : ∀ j' : Fin (A.relayAdv F Q out').slots, (j' : ℕ) = j →
      x.workspace.1.1.logs j' = none) {j'} {r''} (hl : y.workspace.1.1.logs j' = some r'') =>
    log_cases hlog hbl hl
  -- the new log satisfying `p` is an ask
  have hnew : ∀ es', Distinguisher.Booked F (A.budget + A.post) Q (j : ℕ) es'
      ((A.relayA F Q out').cntSplit a).1 → ∀ r'', r'' = y.workspace.1.1.request → p r'' = true →
      F.AsksAt (A.toTPKindAlg true).unitOut.width (A.budget + A.post) Q es'
        y.workspace.1.1.work.1.store y.workspace.1.1.work.1.side j r'' := by
    intro es' hbk r'' hr hp
    obtain ⟨hbt, ⟨hbl, hbr, -⟩, hbq⟩ := hbk
    obtain ⟨hact, hidle⟩ := AdaptiveIAlg.ask_of_askOf F p hpd hpi (hr.trans (hy2.trans hbq)) hp
    have := MultiRelay.asksAt_of_actAt hact hidle
    rw [hbr, MultiRelay.recList_getElem? es' hbl, hbt] at this
    rw [hy1]
    exact this
  rcases hj : (j : ℕ) with _ | t
  · -- the first step
    rw [hj] at hx
    obtain ⟨ht0, hr0, hq0, hl0, hs0⟩ := hx
    have hrest' : Distinguisher.rest F zz =
        Distinguisher.rest F ((A.relayA F Q out').cntSplit b).1 := by
      simp only [hj, ↓reduceIte] at hrest
      exact hrest
    obtain ⟨es', hbk⟩ := Distinguisher.booked_zero F (A.budget + A.post) Q hn A.pureD.kind
      (hx1 ▸ ht0) (hx1 ▸ hr0) (hx2 ▸ hq0) hrest'
    rw [← hpa] at hbk
    refine ⟨es', ?_, ?_, ?_, fun j' hj' => ?_, fun j' r'' hl hp => ?_, ?_⟩
    rotate_right
    · rw [hy1, hpa]
      refine Distinguisher.side_setupFun_recordFun _ _
        (Distinguisher.side_consSide_of_rest hrest' ?_)
      rw [← hx1, hs0, hr0, F.consSide_blank]
    · rw [hy1]
      exact hbk.1
    · rw [hy1]
      exact hbk.2.1
    · rw [hy1, hy2]
      exact hbk.2.2
    · dsimp only
      rw [hlog j', if_neg (fun hk => by simp only at hk; omega)]
      exact hl0 j'
    · rcases hcases (fun j' _ => hl0 j') hl with ⟨hjj, hr⟩ | ⟨-, hl'⟩
      · rw [hjj]
        exact hnew es' (hj ▸ hbk) r'' hr hp
      · have h0 : x.workspace.1.1.logs j' = none := hl0 j'
        rw [h0] at hl'
        exact absurd hl' (by simp)
  · -- the later steps
    rw [hj] at hx
    obtain ⟨es, ht, hrec, hq, hbl, hask, hs⟩ := hx
    have hrest' : Distinguisher.rest F zz = Distinguisher.rest F (Distinguisher.finalizeFun F
        (A.budget + A.post) Q (Distinguisher.sideAddsPerm F (A.budget + A.post) Q
          (Distinguisher.tickPerm F (Distinguisher.teardownFun F
          (A.budget + A.post) Q ((A.relayA F Q out').cntSplit b).1)))) := by
      simp only [hj, Nat.add_one_ne_zero, ↓reduceIte] at hrest
      exact hrest
    have hbq : Distinguisher.Booked F (A.budget + A.post) Q t es
        ((A.relayA F Q out').cntSplit b).1 :=
      ⟨hx1 ▸ ht, hx1 ▸ hrec, by rw [← hx1, ← hx2]; exact hq⟩
    have htS : t < Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width
        ((A.toTPKindAlg true).unitOut.slots + A.post) F := by
      have := j.isLt
      change (j : ℕ) < Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width
        ((A.toTPKindAlg true).unitOut.slots + A.post) F + 0 + 1 at this
      omega
    obtain ⟨es', hes', hbk, hst, hsd⟩ := Distinguisher.booked_succ F (A.budget + A.post) Q hn
      A.pureD.kind htS hbq hrest'
    rw [← hpa] at hbk hst hsd
    refine ⟨es', ?_, ?_, ?_, fun j' hj' => ?_, fun j' r'' hl hp => ?_, ?_⟩
    rotate_right
    · rw [hy1, hpa]
      refine Distinguisher.side_setupFun_recordFun _ _
        (Distinguisher.side_consSide_of_rest hrest' ?_)
      have hpre := Distinguisher.side_preFun (F := F) (b := A.budget + A.post) (Q := Q) (t + 1)
        (Nat.add_one_ne_zero t) ((A.relayA F Q out').cntSplit b).1 (by rw [← hx1, ht]; exact hrec)
        (by rw [← hx1, ht]; exact htS) (by rw [← hx1]; exact hs)
      simpa only [Distinguisher.preFun, Nat.add_one_ne_zero, ↓reduceIte] using hpre
    · rw [hy1]
      exact hbk.1
    · rw [hy1]
      exact hbk.2.1
    · rw [hy1, hy2]
      exact hbk.2.2
    · dsimp only
      rw [hlog j', if_neg (fun hk => by simp only at hk; omega)]
      exact hbl j' (by omega)
    · rcases hcases (fun j' hj' => hbl j' (by omega)) hl with ⟨hjj, hr⟩ | ⟨hjj, hl'⟩
      · rw [hjj]
        exact hnew es' (hj ▸ hbk) r'' hr hp
      · have hle : (j' : ℕ) ≤ t := by
          by_contra hlt
          have h0 : x.workspace.1.1.logs j' = none := hbl j' (by omega)
          rw [h0] at hl'
          exact absurd hl' (by simp)
        have h1 := hask j' r'' hl' hp
        rw [hx1] at h1
        have h2 := hsd j' hle r'' h1
        have h3 : F.AsksAt (A.toTPKindAlg true).unitOut.width (A.budget + A.post) Q es'
            (((A.relayA F Q out').cntSplit a).1).1.1.store
            (((A.relayA F Q out').cntSplit a).1).1.1.side j' r'' := by
          rcases hes' with rfl | ⟨e, rfl⟩
          · exact h2
          · exact h2.append e
        rw [hy1]
        exact h3

/-- **The initial states have the bookkeeping before step `0`**: the relay's clock at `0`, a blank
record, a blank main request register and blank absorbed logs. -/
theorem relayFull_init
    {d d' : DReg ((A.relayAdv F Q out').absorbTab G tab).toTPKindAlg.W
      (A.relayAdv F Q out').width X Y Req₁ Resp₁}
    (h : (((A.relayAdv F Q out').absorbTab G tab).toTPKindAlg.init).mat d d' ≠ 0) :
    ((d.workspace.1.1.work, d.workspace.1.1.request), d.workspace.1.1.logs) ∈
      A.RelayFull F Q out' p 0 := by
  rw [AdaptiveIAlg.toTPKindAlg_init, AdaptiveIAlg.toKindAlg_init, AdaptiveIAlg.withConst_init,
    AdaptiveIAlg.absorb_init] at h
  erw [MState.reindex_tensorKet_mat, MState.reindex_tensorKet_mat, MState.reindex_tensorKet_mat,
    MState.reindex_tensorKet_mat, embed_embed, embed_embed, embed_embed] at h
  obtain ⟨c, c', rfl, -, hc⟩ := embed_ne_zero_exists h
  have hv : (A.relayD F Q).init c ≠ 0 := by
    intro h0
    apply hc
    rw [Distinguisher.toAdaptive_init_mat]
    change (A.relayD F Q).init c * star ((A.relayD F Q).init c') = 0
    rw [h0, zero_mul]
  obtain ⟨d0, rfl⟩ : c ∈ Set.range (Distinguisher.relayInit (W := (A.toTPKindAlg true).unitOut.DW × Bool)
      (Req := Req) (Resp := Resp) (n := (A.toTPKindAlg true).unitOut.width)
      (m := (A.toTPKindAlg true).unitOut.slots + A.post) F) := by
    by_contra hn
    rw [A.relayD_init] at hv
    exact hv (embV_apply_of_notMem _ hn)
  exact ⟨rfl, rfl, rfl, fun j => rfl, rfl⟩

/-- **The sets `RelayFull` are carried by the steps of the relayed adversary absorbed with a
table** (`LogInv`), when the blank and the idle requests fail `p`. -/
theorem relayAdv_logInv (hpd : p default = false) (hpi : p F.idle = false) :
    (A.relayAdv F Q out').LogInv G tab (A.RelayFull F Q out' p) where
  init _ _ h := A.relayFull_init F Q out' p G tab h
  slot j _ _ _ h hx := A.relayFull_step F Q out' p G tab hpd hpi (slotStep j) h hx
  post k _ _ _ _ h hx := A.relayFull_step F Q out' p G tab hpd hpi k h hx

/-- **The relayed adversary logs at most `K · Q` requests satisfying `p`** (module docstring):
absorbed with a table through any relay, sets of its workspaces, request registers and absorbed
logs carried by its steps (`LogInv`) end in the logs with at most `K · Q` requests satisfying `p`,
when the blank and the idle requests fail `p`. -/
theorem relayAdv_logs_le (hpd : p default = false) (hpi : p F.idle = false) :
    ∃ T, (A.relayAdv F Q out').LogInv G tab T ∧
      ∀ x ∈ T ((A.relayAdv F Q out').slots + (A.relayAdv F Q out').post + 1),
        (Finset.univ.filter fun j => (x.2 j).any p = true).card ≤ F.K * Q :=
  ⟨A.RelayFull F Q out' p, A.relayAdv_logInv F Q out' p G tab hpd hpi,
    fun _ hx => A.countLE_of_relayFull F Q out' p hx⟩

end Relay

end AdaptiveIAlg

end GordieHowe.Quantum
