-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AssignPatch

@[expose] public section

/-!
# The mixed game of the patched adversary, step by step

Proof tools for the law of `AdaptiveIAlg.patchTag`
(`GordieHowe/Model/Quantum/Interactive/AssignPatch.lean`).

- `patchCntSplit`, `patchWithCnt`, `patchGamePerm`: the patched registers with the query counter,
  and a permutation of the patched registers on the game registers.
- `patchTag_toKindAlg_step_apply`, `patchTag_liftG_apply`: the step of the patched adversary with
  its counter, and on the game registers, is the permutation after the previous slot, `B`'s step
  with its counter tensored with the identity (`patchGameStep`), and the permutation before the
  next slot.
- `patchPlace tg T₁`: the placement of `B`'s game registers with the ancillas in the patched game
  registers: the table register holds `tg` of the registers beside the query pairs, and each
  logged request `r` of slot `j` is tagged with `T₁` of the requests before slot `j`
  (`augLogs`). `patchPlace_injective`.
- `patchGameStep_embed`: `B`'s step with its counter, on a placed matrix with a blank table
  register, is placed `B`'s step tensored with the identity on the ancillas.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

/-! ### Tagged logs -/

section Aug

variable {Req Tab : Type*} {m : ℕ}

/-- **The logs with each request tagged** by `T₁` of the requests before its slot. -/
def augLogs (T₁ : List Req → Tab) (lg : LogReg Req m) : LogReg (Req × Tab) m :=
  fun j => (lg j).map fun r => (r, T₁ (requestsBefore lg j))

theorem augLogs_injective (T₁ : List Req → Tab) : Function.Injective (augLogs (m := m) T₁) := by
  intro lg lg' h
  funext j
  have := congrFun h j
  simp only [augLogs] at this
  rcases h1 : lg j with _ | r <;> rcases h2 : lg' j with _ | r' <;> simp_all

theorem requestsBefore_augLogs (T₁ : List Req → Tab) (lg : LogReg Req m) :
    ∀ k, (requestsBefore (augLogs T₁ lg) k).map Prod.fst = requestsBefore lg k
  | 0 => rfl
  | k + 1 => by
    rw [requestsBefore, requestsBefore, List.map_append, requestsBefore_augLogs T₁ lg k]
    split_ifs with hk
    · simp only [augLogs]
      rcases lg ⟨k, hk⟩ <;> rfl
    · rfl

end Aug

namespace AdaptiveIAlg

variable {X Y Req Resp O O' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) (tab : B.W → X → Option Y) (out' : B.W → O')
  [AddGroup Y] [Nonempty X] [Nonempty Y]

/-! ### The steps with the counter -/

/-- The patched registers with the counter, the counter beside the ancillas' workspace. -/
abbrev PatchCReg : Type :=
  DReg (B.patchTag tab out').CntW B.width X Y (Req × (X → Option Y)) Resp

/-- A permutation of the patched registers with the counter alongside. -/
noncomputable def patchWithCnt (π : Equiv.Perm B.PatchReg) : Equiv.Perm (B.PatchCReg tab out') :=
  (B.patchTag tab out').cntSplit.symm.permCongr (π.prodCongr (Equiv.refl _))

@[simp] theorem patchWithCnt_apply (π : Equiv.Perm B.PatchReg) (w : B.PatchW)
    (c : Fin ((B.patchTag tab out').budget + 2)) (rq : Req × (X → Option Y)) (rs : Option Resp)
    (qs : Fin B.width → X × Y) :
    B.patchWithCnt tab out' π (((AlgShape.CntW.mk w c), rq, rs), qs) =
      (((AlgShape.CntW.mk (π ((w, rq, rs), qs)).1.1 c), (π ((w, rq, rs), qs)).1.2.1,
        (π ((w, rq, rs), qs)).1.2.2), (π ((w, rq, rs), qs)).2) := rfl

theorem inBudget_patchWithCnt {π : Equiv.Perm B.PatchReg} (hπ : ∀ d, (π d).1.1.1 = d.1.1.1)
    (d : B.PatchCReg tab out') :
    (B.patchTag tab out').inBudget (B.patchWithCnt tab out' π d) =
      (B.patchTag tab out').inBudget d := by
  obtain ⟨⟨wc_, rq, rs⟩, qs⟩ := d
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  rw [patchWithCnt_apply, inBudget_mk, inBudget_mk]
  exact congrArg (· || _) (congrArg B.kind (hπ ((w, rq, rs), qs)))

theorem cntShift_patchWithCnt {π : Equiv.Perm B.PatchReg} (hπ : ∀ d, (π d).1.1.1 = d.1.1.1)
    (d : B.PatchCReg tab out') :
    (B.patchTag tab out').cntShift (B.patchWithCnt tab out' π d) =
      B.patchWithCnt tab out' π ((B.patchTag tab out').cntShift d) := by
  obtain ⟨⟨wc_, rq, rs⟩, qs⟩ := d
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  have hk : (B.patchTag tab out').kind (π ((w, rq, rs), qs)).1.1 = (B.patchTag tab out').kind w :=
    congrArg B.kind (hπ ((w, rq, rs), qs))
  rw [patchWithCnt_apply, cntShift_apply, cntShift_apply, patchWithCnt_apply, hk]

/-- **`B`'s step with the query counter, on the patched registers**: `B`'s step tensored with the
identity, then for `k < slots` the projection onto the branches within the budget and the counter
advanced on the query branches. -/
noncomputable def patchCntStep (k : StepIdx B.slots B.post) :
    KrausMap B.R (B.PatchCReg tab out') (B.PatchCReg tab out') :=
  if (k : ℕ) < B.slots then
    ((((B.patchLifted k).tensorId (Fin (B.budget + 2))).reindex
      (B.patchTag tab out').cntSplit.symm).restrict (B.patchTag tab out').inBudget).permConj
        (Equiv.refl _) (B.patchTag tab out').cntShift
  else ((B.patchLifted k).tensorId (Fin (B.budget + 2))).reindex (B.patchTag tab out').cntSplit.symm

omit [Nonempty X] [Nonempty Y] in
theorem workB_swapP (on : B.W → Bool) (d : B.PatchReg) : ((B.swapP tab on) d).1.1.1 = d.1.1.1 :=
  rfl

omit [Nonempty X] [Nonempty Y] in
theorem workB_finishP (on : B.W → Bool) (d : B.PatchReg) :
    ((B.finishP tab on) d).1.1.1 = d.1.1.1 :=
  rfl

omit [AddGroup Y] [Nonempty X] [Nonempty Y] in
theorem workB_tagP (on : B.W → Bool) (d : B.PatchReg) : ((B.tagP tab on) d).1.1.1 = d.1.1.1 := by
  change (if on d.1.1.1 then _ else d).1.1.1 = _
  split_ifs <;> rfl

omit [Nonempty X] [Nonempty Y] in
theorem workB_patchBefore (k : ℕ) (d : B.PatchReg) : ((B.patchBefore tab k) d).1.1.1 = d.1.1.1 := by
  rw [AdaptiveIAlg.patchBefore_def]
  split_ifs
  · rw [Equiv.trans_apply, workB_swapP, workB_tagP]
  · exact B.workB_swapP tab _ d
  · rfl

omit [Nonempty X] [Nonempty Y] in
theorem workB_patchAfter (k : ℕ) (d : B.PatchReg) : ((B.patchAfter tab k) d).1.1.1 = d.1.1.1 := by
  rw [AdaptiveIAlg.patchAfter_def]
  split_ifs
  · rw [Equiv.trans_apply, workB_finishP, workB_tagP]
  · exact B.workB_finishP tab _ d
  · rfl

/-- **The step of the patched adversary with its query counter** is the permutation after slot
`k - 1`, `B`'s step with its counter (`patchCntStep`), and the permutation before slot `k`. -/
theorem patchTag_toKindAlg_step_apply (k : StepIdx B.slots B.post)
    (ρ : Matrix (B.PatchCReg tab out') (B.PatchCReg tab out') ℂ) :
    (B.patchTag tab out').toKindAlg.step k ρ =
      ((B.patchCntStep tab out' k) (ρ.submatrix (B.patchWithCnt tab out' (B.patchAfter tab k)).symm
        (B.patchWithCnt tab out' (B.patchAfter tab k)).symm)).submatrix
        (B.patchWithCnt tab out' (B.patchBefore tab k)).symm
        (B.patchWithCnt tab out' (B.patchBefore tab k)).symm := by
  have hstep : (((B.patchTag tab out').step k).tensorId
      (Fin ((B.patchTag tab out').budget + 2))).reindex
      (B.patchTag tab out').cntSplit.symm =
        (KrausMap.ofPerm (B.patchWithCnt tab out' (B.patchBefore tab k))).comp
        ((((B.patchLifted k).tensorId (Fin (B.budget + 2))).reindex
          (B.patchTag tab out').cntSplit.symm).comp
          (KrausMap.ofPerm (B.patchWithCnt tab out' (B.patchAfter tab k)))) := by
    rw [patchTag_step]
    rw [KrausMap.tensorId_comp, KrausMap.tensorId_comp, KrausMap.reindex_comp,
      KrausMap.reindex_comp, KrausMap.ofPerm_tensorId, KrausMap.ofPerm_tensorId,
      KrausMap.ofPerm_reindex, KrausMap.ofPerm_reindex]
    rfl
  by_cases hk : (k : ℕ) < B.slots
  · have hs : (B.patchTag tab out').toKindAlg.step k = (((((B.patchTag tab out').step k).tensorId
        (Fin ((B.patchTag tab out').budget + 2))).reindex
            (B.patchTag tab out').cntSplit.symm).restrict
        (B.patchTag tab out').inBudget).permConj (Equiv.refl _) (B.patchTag tab out').cntShift := by
      exact AdaptiveIAlg.toKindAlg_step_of_lt _ hk
    rw [hs, hstep]
    refine (KrausMap.permConj_restrict_ofPerm_comp_apply _ _ _ _ ?hp ?hτ ρ).trans ?_
    case hp => exact B.inBudget_patchWithCnt tab out' (B.workB_patchBefore tab k)
    case hτ => exact B.cntShift_patchWithCnt tab out' (B.workB_patchBefore tab k)
    rw [KrausMap.restrict_comp, KrausMap.permConj_refl_comp, KrausMap.comp_apply,
      KrausMap.ofPerm_apply]
    simp only [patchCntStep, if_pos hk]
  · have hs : (B.patchTag tab out').toKindAlg.step k = (((B.patchTag tab out').step k).tensorId
        (Fin ((B.patchTag tab out').budget + 2))).reindex (B.patchTag tab out').cntSplit.symm := by
      exact AdaptiveIAlg.toKindAlg_step_of_not_lt _ hk
    rw [hs, hstep]
    refine (KrausMap.comp_apply _ _ ρ).trans ?_
    rw [KrausMap.comp_apply, KrausMap.ofPerm_apply, KrausMap.ofPerm_apply]
    simp only [patchCntStep, if_neg hk]

/-! ### The steps on the game registers -/

/-- The patched registers with the counter as `B`'s with the counter and the ancillas with the
table register. -/
noncomputable def patchCntSplit : B.PatchCReg tab out' ≃
    DReg B.CntW B.width X Y Req Resp ×
        (AncReg X Y B.width × (X → Option Y)) where
  toFun d := ((((AlgShape.CntW.mk d.1.1.work.1 d.1.1.cnt), d.1.2.1.1, d.1.2.2), d.2),
    (d.1.1.work.2, d.1.2.1.2))
  invFun p := (((AlgShape.CntW.mk (AlgShape.PatchWS.mk p.1.1.1.work p.2.1) p.1.1.1.cnt : (B.patchTag tab out').CntW),
    (p.1.1.2.1, p.2.2), p.1.1.2.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`B`'s step with its counter, on the patched registers, lifts its step with its counter.** -/
theorem patchCntStep_lifts (k : StepIdx B.slots B.post) :
    (B.patchCntStep tab out' k).Lifts (B.patchCntSplit tab out') (B.toKindAlg.step k) := by
  have hL : (B.patchLifted k).Lifts B.patchSplitB (B.step k) :=
    KrausMap.lifts_reindex_tensorId _ (B.step k)
  have hcnt : (((B.patchLifted k).tensorId (Fin (B.budget + 2))).reindex
      (B.patchTag tab out').cntSplit.symm).Lifts (B.patchCntSplit tab out')
      (((B.step k).tensorId (Fin (B.budget + 2))).reindex B.cntSplit.symm) :=
    (hL.tensorId (Fin (B.budget + 2)) (E₂ := liftProd B.patchSplitB (Fin (B.budget + 2)))
      fun _ _ => rfl).reindex fun _ => rfl
  rw [AdaptiveIAlg.toKindAlg_step_eq]
  change KrausMap.Lifts (B.patchCntSplit tab out') (if (k : ℕ) < B.slots then _ else _)
    (if (k : ℕ) < B.slots then _ else _)
  refine KrausMap.Lifts.ite (fun _ => ?_) fun _ => hcnt
  refine (hcnt.restrict fun x => ?_).permConj (fun _ => rfl) (perm_symm_lift _ fun x => ?_)
  · obtain ⟨⟨wc_, rq, rs⟩, qs⟩ := x
    obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
    rfl
  · obtain ⟨⟨wc_, rq, rs⟩, qs⟩ := x
    obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
    rfl

/-- A permutation of the patched registers with the counter, on the game registers. -/
noncomputable def patchGamePerm (π : Equiv.Perm B.PatchReg) :
    Equiv.Perm (B.patchTag tab out').toKindAlg.G :=
  splitLogs.symm.permCongr ((B.patchWithCnt tab out' π).prodCongr (Equiv.refl _))

/-- `B`'s step with its counter on the patched game registers. -/
noncomputable def patchGameStep (k : StepIdx B.slots B.post) :
    KrausMap B.R (B.patchTag tab out').toKindAlg.G (B.patchTag tab out').toKindAlg.G :=
  ((B.patchCntStep tab out' k).tensorId (LogReg (Req × (X → Option Y)) B.slots)).reindex
    splitLogs.symm

/-- **The step of the patched adversary on the game registers**: the permutation after slot
`k - 1`, `B`'s step with its counter, the permutation before slot `k`. -/
theorem patchTag_liftG_apply (k : StepIdx B.slots B.post)
    (M : Matrix (B.patchTag tab out').toKindAlg.G (B.patchTag tab out').toKindAlg.G ℂ) :
    (B.patchTag tab out').toKindAlg.liftG k M =
      ((B.patchGameStep tab out' k)
          (M.submatrix (B.patchGamePerm tab out' (B.patchAfter tab k)).symm
        (B.patchGamePerm tab out' (B.patchAfter tab k)).symm)).submatrix
        (B.patchGamePerm tab out' (B.patchBefore tab k)).symm
        (B.patchGamePerm tab out' (B.patchBefore tab k)).symm :=
  KrausMap.tensorId_reindex_apply_of_conj (B.patchTag_toKindAlg_step_apply tab out' k) _ _ M

instance : DecidableEq ((AncReg X Y B.width × (X → Option Y)) ×
    LogReg (Req × (X → Option Y)) B.slots) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

instance : DecidableEq (DReg B.CntW B.width X Y Req Resp ×
    (LogReg Req B.slots × AncReg X Y B.width)) :=
  @instDecidableEqProd _ _ DReg.instDecidableEq inferInstance

/-- The patched game registers as `B`'s registers with the counter and the rest. -/
noncomputable def patchGameSplit : (B.patchTag tab out').toKindAlg.G ≃
    DReg B.CntW B.width X Y Req Resp ×
      ((AncReg X Y B.width × (X → Option Y)) × LogReg (Req × (X → Option Y)) B.slots) where
  toFun g := ((((AlgShape.CntW.mk g.1.1.work.1 g.1.1.cnt), g.1.2.1.1, g.1.2.2.1), g.2),
    ((g.1.1.work.2, g.1.2.1.2), g.1.2.2.2))
  invFun p := (((AlgShape.CntW.mk (AlgShape.PatchWS.mk p.1.1.1.work p.2.1.1) p.1.1.1.cnt : (B.patchTag tab out').CntW),
    (p.1.1.2.1, p.2.1.2), p.1.1.2.2, p.2.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`B`'s step with its counter on the patched game registers acts as `B`'s step with its
counter tensored with the identity** on the rest. -/
theorem patchGameStep_apply (k : StepIdx B.slots B.post)
    (M : Matrix (B.patchTag tab out').toKindAlg.G (B.patchTag tab out').toKindAlg.G ℂ) :
    B.patchGameStep tab out' k M = (((B.toKindAlg.step k).tensorId
      ((AncReg X Y B.width × (X → Option Y)) × LogReg (Req × (X → Option Y)) B.slots)).reindex
        (B.patchGameSplit tab out').symm) M := by
  have h1 : (B.patchGameStep tab out' k).Lifts (B.patchGameSplit tab out') (B.toKindAlg.step k) :=
    ((B.patchCntStep_lifts tab out' k).tensorId_right (LogReg (Req × (X → Option Y)) B.slots)
      (E₂ := ((B.patchCntSplit tab out').prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))
      fun _ _ => rfl).reindex_left fun _ => rfl
  exact h1.apply_eq (KrausMap.lifts_reindex_tensorId _ _) M

/-! ### The placement -/

/-- **The placement of `B`'s game registers with the ancillas in the patched game registers**:
the table register holds `tg` of the registers beside the query pairs, the logs are tagged by
`T₁` (`augLogs`). -/
noncomputable def patchPlace
    (tg : B.CntW × Req × Option Resp × LogReg Req B.slots → X → Option Y)
    (T₁ : List Req → X → Option Y)
    (p : B.toKindAlg.G × AncReg X Y B.width) : (B.patchTag tab out').toKindAlg.G :=
  (((AlgShape.CntW.mk (AlgShape.PatchWS.mk p.1.1.1.work p.2) p.1.1.1.cnt : (B.patchTag tab out').CntW),
    (p.1.1.2.1, tg p.1.1), p.1.1.2.2.1, augLogs T₁ p.1.1.2.2.2), p.1.2)

theorem patchPlace_injective
    (tg : B.CntW × Req × Option Resp × LogReg Req B.slots → X → Option Y)
    (T₁ : List Req → X → Option Y) :
    Function.Injective (B.patchPlace tab out' tg T₁) := by
  rintro ⟨⟨⟨wc, rq, rs, lg⟩, qs⟩, a⟩ ⟨⟨⟨wc', rq', rs', lg'⟩, qs'⟩, a'⟩ h
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc
  obtain ⟨w', c', rfl⟩ := AlgShape.CntW.exists_eq_mk wc'
  simp only [patchPlace, Prod.mk.injEq, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk] at h
  obtain ⟨⟨hwac, ⟨h4, -⟩, h5, h6⟩, h7⟩ := h
  obtain ⟨hwa, h3⟩ := AlgShape.CntW.mk_inj.1 hwac
  obtain ⟨h1, h2⟩ := AlgShape.PatchWS.mk_inj.1 hwa
  have h6' := augLogs_injective T₁ h6
  subst h1 h2 h3 h4 h5 h6' h7
  rfl

/-- `B`'s game registers with the ancillas as `B`'s registers with the counter and the rest. -/
def bAncSplit : DReg B.CntW B.width X Y Req Resp ×
    (LogReg Req B.slots × AncReg X Y B.width) ≃ B.toKindAlg.G × AncReg X Y B.width where
  toFun p := (splitLogs.symm (p.1, p.2.1), p.2.2)
  invFun q := ((splitLogs q.1).1, ((splitLogs q.1).2, q.2))
  left_inv _ := rfl
  right_inv _ := rfl

omit [AddGroup Y] [Nonempty X] [Nonempty Y] in
theorem tensorId_reindex_bAncSplit (k : StepIdx B.slots B.post) :
    ((B.toKindAlg.step k).tensorId (LogReg Req B.slots × AncReg X Y B.width)).reindex
      (B.bAncSplit) = (B.toKindAlg.liftG k).tensorId (AncReg X Y B.width) := by
  refine KrausMap.ext_op (funext fun r => ?_)
  ext ⟨g, a⟩ ⟨g', a'⟩
  obtain ⟨⟨w, rq, rs, lg⟩, qs⟩ := g
  obtain ⟨⟨w', rq', rs', lg'⟩, qs'⟩ := g'
  simp only [KrausMap.reindex, KrausMap.tensorId, KindAlg.liftG, submatrix_apply,
    kroneckerMap_apply, Matrix.one_apply, bAncSplit, Equiv.coe_fn_symm_mk, Equiv.symm_symm,
    splitLogs, Equiv.coe_fn_mk, Prod.mk.injEq]
  by_cases h1 : lg = lg' <;> by_cases h2 : a = a' <;> simp [h1, h2]

/-- **`B`'s step with its counter on a placed matrix with a blank table register is the placed
step of `B` tensored with the identity on the ancillas.** -/
theorem patchGameStep_embed (k : StepIdx B.slots B.post) (T₁ : List Req → X → Option Y)
    (σ : Matrix (B.toKindAlg.G × AncReg X Y B.width) (B.toKindAlg.G × AncReg X Y B.width) ℂ) :
    B.patchGameStep tab out' k (embed (B.patchPlace tab out' (fun _ _ => none) T₁) σ) =
      embed (B.patchPlace tab out' (fun _ _ => none) T₁)
        (((B.toKindAlg.liftG k).tensorId (AncReg X Y B.width)) σ) := by
  have hp : B.patchPlace tab out' (fun _ _ => none) T₁ = (B.patchGameSplit tab out').symm ∘
      Prod.map _root_.id (fun p : LogReg Req B.slots × AncReg X Y B.width =>
        ((p.2, fun _ => none), augLogs T₁ p.1)) ∘ B.bAncSplit.symm := by
    funext p
    rfl
  rw [patchGameStep_apply, hp, KrausMap.tensorId_reindex_apply_embed, ← tensorId_reindex_bAncSplit]

end AdaptiveIAlg

end GordieHowe.Quantum
