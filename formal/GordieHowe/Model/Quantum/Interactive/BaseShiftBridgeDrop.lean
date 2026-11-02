-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftInstLog

@[expose] public section

-- The proofs below read the definition of the bridge (irreducible elsewhere).
set_option allowUnsafeReducibility true in
attribute [local reducible] GordieHowe.Quantum.bridgeAlg

/-!
# The bridge with the drops of additions

`bridgeAlgAdds`: the bridge of `A` with each step read after the drops of a sorted list of
additions `P` at `ω` (`addsDrop`). `simLaw_bridgeAdds_withSteps`: with the request points of a
table, it has the law of the composition read after the table's request points and then the
drops; `simLaw_bridgeAdds_instLog`: it is then the instance with the table's replies. The local
queries' bridge (`bridgeAlgDrop`, `bridgeDrop`, `dropE`, `bridgeStepsDrop` and their lemmas) is the
instance at `BaseW.toAddsW`.

`bridgeDropPerms`, `bridgeAlgDrops`, `bridgeStepsDrops`, `simLaw_bridgeDrops_withSteps`,
`simLaw_bridgeDrops_instLog` (with `bridgeDropPerms_bridgeWrite`, `bridgeDropPerms_goodS`,
`bridgeAlg_req_bridgeDropPerms`, `writeV_logs`, `bridgeWrite_goodS`): the same for any family of
drops that keeps the requests and the absorbed logs; the drops of additions are an instance.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

theorem equiv_cast_symm_apply_eq_iff {α β : Type} (h : α = β) (b : β) (a : α) :
    (Equiv.cast h).symm b = a ↔ HEq b a := by
  subst h
  exact ⟨fun h => heq_of_eq h, fun h => eq_of_heq h⟩

theorem equiv_cast_heq {α β : Type} (h : α = β) (a : α) : HEq (Equiv.cast h a) a := by
  subst h
  rfl

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  [Nonempty (Bits m)] {Y₁ : Type} [AddGroup Y₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)

/-- **The extraction run's output of `A.withStep st'`** is that of `A`, on the registers of the
composition written out. -/
theorem extOut_withStep
    (st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
      (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (d₀ : ExtReg (A.withStep st') C₁ Req₂ Resp₂) (tab : A.OuterTab Req₂ Resp₂)
    (o : Option (CWork (shA.absorbTabS Req₂ Resp₂ (Req₁ := Req₁) (Resp₁ := Resp₁)).CntW
      A.width (Bits m) (BitStr I J) Req₁ Resp₁ A.slots C₁.q C₁.Coins)) :
    extOut (A.withStep st') C₁ F d₀ tab o = extOut A C₁ F d₀ tab o := by
  cases o with
  | none => rfl
  | some v => rfl

variable (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)
  (P : A.AddsW Y₁) (D : A.BaseW Y₁) (ω : Bits m → Y₁)

/-- `goodW` reads the absorbed logs, the halting flag and the ancilla. -/
theorem goodW_congr (n : ℕ) {w w' : (bridgeAlg e A C₁ F d₂ E kq d₀).W}
    (hw : w ∈ goodW e A C₁ F d₂ E kq d₀ n) (hl : cohLogs A C₁ F d₀ w'.1 = cohLogs A C₁ F d₀ w.1)
    (hf : w'.1.1.2 = w.1.1.2) (ha : w'.1.2 = w.1.2) : w' ∈ goodW e A C₁ F d₂ E kq d₀ n := by
  cases n with
  | zero =>
    obtain ⟨h1, h2, h3⟩ := (mem_cohInit A C₁ F d₀).1 hw
    refine (mem_cohInit A C₁ F d₀).2 ⟨fun j => (congrFun hl j).trans (h1 j), ?_, ?_⟩
    · rw [hf]
      exact h2
    · rw [ha]
      exact h3
  | succ n => exact cohSet_congr A C₁ F d₀ hw hl hf ha fun x hx => absurd hx (Set.notMem_empty x)

/-! ### The bridge with any drops

The bridge with each step read after a family of drops `β` of the composition's registers, after
the table's request points, for drops that keep the request points (`hβr`) and the absorbed logs
(`hβl`). The drops of additions are an instance. -/

section Drops

variable (β : ℕ → Equiv.Perm (ReprogrammedQueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁)
  (Bits m) (BitStr I J)))

/-- **The drops `β` on the registers of the expanded coherent run**: on the core register and the
query register at the steps of the composition, the identity after them. -/
noncomputable abbrev dropEPerms :=
  cohDropAt e E kq ((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id)
    (extOut A C₁ F d₀ (tab₀ A)) fun j => β j

/-- **The drops `β` on the bridge's registers.** -/
noncomputable def bridgeDropPerms (i : Fin (bT A C₁ F kq + 1)) :
    Equiv.Perm (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :=
  castPerms e E kq ((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id)
    (extOut A C₁ F d₀ (tab₀ A)) (bridgeAlg e A C₁ F d₂ E kq d₀) (bridgeReg_eq e A C₁ F d₂ E kq d₀)
    (dropEPerms e A C₁ F E kq d₀ β) i

/-- **The bridge with the drops `β`.** -/
noncomputable def bridgeAlgDrops :
    ReqQueryAlg (Bits m) (BitStr I J) Req₂ Resp₂ (bT A C₁ F kq)
      (BaseGame.Tuple (Bits m) B (ExtReg A C₁ Req₂ Resp₂) kq) :=
  (bridgeAlg e A C₁ F d₂ E kq d₀).withPerm (bridgeDropPerms e A C₁ F d₂ E kq d₀ β)

/-- **The steps of the bridge with the drops `β`, with the request points of the table `tab`.** -/
noncomputable def bridgeStepsDrops (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1)) :
    QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ]
      QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :=
  (permOp (bridgeWrite e A C₁ F d₂ E kq d₀ tab k)).trans
    ((bridgeAlgDrops e A C₁ F d₂ E kq d₀ β).step k)

/-- **The bridge with the drops `β`, with the request points of a table**, has the law of the
expanded coherent run of the composition read after the table's request points and then `β`. -/
theorem simLaw_bridgeDrops_withSteps (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e ((bridgeAlg e A C₁ F d₂ E kq d₀).withSteps
        (bridgeStepsDrops e A C₁ F d₂ E kq d₀ β tab)) =
      simLaw e (expandAdv e E kq
        ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).precomp
        fun j => (queryWorkPerm (writeV A C₁ F d₂ tab (bT A C₁ F kq) j)).trans
          (β j)).toQueryAlgCoh.mapOut (extOut A C₁ F d₀ (tab₀ A)))) := by
  refine simLaw_withSteps_of_write_dropE e E kq
    ((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id) (extOut A C₁ F d₀ (tab₀ A))
    (fun j => writeV A C₁ F d₂ tab (bT A C₁ F kq) j) (fun j => β j)
    (bridgeCompose_tracePreserving A C₁ F) (bridgeAlg e A C₁ F d₂ E kq d₀) rfl
    (bridgeWrite e A C₁ F d₂ E kq d₀ tab) (bridgeReg_eq e A C₁ F d₂ E kq d₀)
    (fun i p _ => bridgeWrite_heq_lt e A C₁ F d₂ E kq d₀ tab i p)
    (fun i p h => bridgeWrite_apply_ge e A C₁ F d₂ E kq d₀ tab i p h)
    (dropEPerms e A C₁ F E kq d₀ β) (fun i => cohDropAt_eq e E kq _ _ _ i)
    (bridgeStepsDrops e A C₁ F d₂ E kq d₀ β tab) fun _ => rfl

/-- **The drops `β` on the bridge's registers at a step of the composition**, written out. -/
theorem bridgeDropPerms_apply_lt (k : Fin (bT A C₁ F kq + 1))
    (h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1)
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    bridgeDropPerms e A C₁ F d₂ E kq d₀ β k p =
      (((((β k (p.1.1.1.1, p.2)).1, p.1.1.1.2), p.1.1.2), p.1.2), (β k (p.1.1.1.1, p.2)).2) := by
  unfold bridgeDropPerms castPerms dropEPerms cohDropAt
  rw [Equiv.trans_apply, Equiv.trans_apply, dif_pos h]
  refine (equiv_cast_symm_apply_eq_iff _ _ _).2 ?_
  have hq := equiv_cast_heq (bridgeReg_eq e A C₁ F d₂ E kq d₀) p
  revert hq
  generalize Equiv.cast (bridgeReg_eq e A C₁ F d₂ E kq d₀) p = q
  intro hq
  with_reducible
    have hqp : q = p := eq_of_heq hq
  subst hqp
  rfl

/-- **The drops `β` on the bridge's registers after the steps of the composition** are the
identity. -/
theorem bridgeDropPerms_apply_ge (k : Fin (bT A C₁ F kq + 1))
    (h : ¬ (k : ℕ) < (bridgeCompose A C₁ F).depth + 1)
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    bridgeDropPerms e A C₁ F d₂ E kq d₀ β k p = p := by
  unfold bridgeDropPerms castPerms dropEPerms cohDropAt
  rw [Equiv.trans_apply, Equiv.trans_apply, dif_neg h, Equiv.Perm.one_apply]
  exact (equiv_cast_symm_apply_eq_iff _ _ _).2 (equiv_cast_heq _ p)

/-- **Drops that commute with the request points commute with the bridge's writes.** -/
theorem bridgeDropPerms_bridgeWrite (tab : A.OuterTab Req₂ Resp₂)
    (hβw : ∀ (Tb k n : ℕ) p, queryWorkPerm (writeV A C₁ F d₂ tab Tb k) (β n p) =
      β n (queryWorkPerm (writeV A C₁ F d₂ tab Tb k) p))
    (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    bridgeDropPerms e A C₁ F d₂ E kq d₀ β k (bridgeWrite e A C₁ F d₂ E kq d₀ tab k p) =
      bridgeWrite e A C₁ F d₂ E kq d₀ tab k (bridgeDropPerms e A C₁ F d₂ E kq d₀ β k p) := by
  by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDropPerms_apply_lt e A C₁ F d₂ E kq d₀ β k h
        (bridgeWrite e A C₁ F d₂ E kq d₀ tab k p),
      bridgeWrite_apply_lt₀ e A C₁ F d₂ E kq d₀ tab k (bridgeDropPerms e A C₁ F d₂ E kq d₀ β k p),
      bridgeDropPerms_apply_lt e A C₁ F d₂ E kq d₀ β k h p,
      bridgeWrite_apply_lt₀ e A C₁ F d₂ E kq d₀ tab k p]
    have h2 : β k (writeV A C₁ F d₂ tab (bT A C₁ F kq) k p.1.1.1.1, p.2) =
        (writeV A C₁ F d₂ tab (bT A C₁ F kq) k (β k (p.1.1.1.1, p.2)).1,
          (β k (p.1.1.1.1, p.2)).2) :=
      (hβw (bT A C₁ F kq) k k (p.1.1.1.1, p.2)).symm
    dsimp only
    rw [h2]
  · rw [bridgeDropPerms_apply_ge e A C₁ F d₂ E kq d₀ β k h,
      bridgeDropPerms_apply_ge e A C₁ F d₂ E kq d₀ β k h]

/-- **Drops that keep the request points keep every request of the bridge.** -/
theorem bridgeAlg_req_bridgeDropPerms
    (hβr : ∀ (j n : ℕ) x, reqV A C₁ F d₂ j (β n x).1 = reqV A C₁ F d₂ j x.1)
    (k j : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).req j (bridgeDropPerms e A C₁ F d₂ E kq d₀ β k p).1 =
      (bridgeAlg e A C₁ F d₂ E kq d₀).req j p.1 := by
  rw [bridgeAlg_req_eq, bridgeAlg_req_eq]
  by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDropPerms_apply_lt e A C₁ F d₂ E kq d₀ β k h]
    exact hβr j k (p.1.1.1.1, p.2)
  · rw [bridgeDropPerms_apply_ge e A C₁ F d₂ E kq d₀ β k h]

/-- **Drops that keep the absorbed logs keep the supports of the bridge's simulated run.** -/
theorem bridgeDropPerms_goodS
    (hβl : ∀ n q, (β n q).1.1.adv.workspace.1.1.logs = q.1.1.adv.workspace.1.1.logs)
    (k : Fin (bT A C₁ F kq + 1))
    (s : SimRegister (bridgeAlg e A C₁ F d₂ E kq d₀).W I J m (bT A C₁ F kq))
    (hs : s ∈ goodS e A C₁ F d₂ E kq d₀ k) :
    (bridgeDropPerms e A C₁ F d₂ E kq d₀ β k).prodCongr (Equiv.refl _) s ∈
      goodS e A C₁ F d₂ E kq d₀ k := by
  change (bridgeDropPerms e A C₁ F d₂ E kq d₀ β k s.1).1 ∈ goodW e A C₁ F d₂ E kq d₀ k
  by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDropPerms_apply_lt e A C₁ F d₂ E kq d₀ β k h]
    exact goodW_congr e A C₁ F d₂ E kq d₀ k hs (hβl k (s.1.1.1.1.1, s.1.2)) rfl rfl
  · rw [bridgeDropPerms_apply_ge e A C₁ F d₂ E kq d₀ β k h]
    exact hs

omit [Nonempty (Bits m)] in
/-- **The request points keep the absorbed logs.** -/
theorem writeV_logs (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) (c : (bridgeCompose A C₁ F).V) :
    (writeV A C₁ F d₂ tab T k c).1.adv.1.1.1.1.logs = c.1.adv.1.1.1.1.logs := by
  rcases h : answerSlot A C₁ k with _ | j
  · rw [writeV_of_none A C₁ F d₂ tab T h]
    rfl
  · rw [writeV_of_some A C₁ F d₂ tab T h]
    exact answerDelta_logs A F j _ (absV A C₁ F c)

/-- **The bridge's writes of the table's replies keep the supports of its simulated run**, both
ways. -/
theorem bridgeWrite_goodS (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1))
    (s : SimRegister (bridgeAlg e A C₁ F d₂ E kq d₀).W I J m (bT A C₁ F kq))
    (hs : s ∈ goodS e A C₁ F d₂ E kq d₀ k) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).simPerm ((bridgeAlg e A C₁ F d₂ E kq d₀).ctrlWrite k
        (bridgeRep e A C₁ F d₂ E kq d₀ tab k) (bridgeRep_write e A C₁ F d₂ E kq d₀ tab k)) s ∈
        goodS e A C₁ F d₂ E kq d₀ k ∧
      ((bridgeAlg e A C₁ F d₂ E kq d₀).simPerm ((bridgeAlg e A C₁ F d₂ E kq d₀).ctrlWrite k
        (bridgeRep e A C₁ F d₂ E kq d₀ tab k) (bridgeRep_write e A C₁ F d₂ E kq d₀ tab k))).symm s ∈
        goodS e A C₁ F d₂ E kq d₀ k := by
  have h1 : ∀ p, (bridgeWrite e A C₁ F d₂ E kq d₀ tab k p).1.1.1.1.1.adv.workspace.1.1.logs =
      p.1.1.1.1.1.adv.workspace.1.1.logs ∧
      (bridgeWrite e A C₁ F d₂ E kq d₀ tab k p).1.1.1.2 = p.1.1.1.2 ∧
      (bridgeWrite e A C₁ F d₂ E kq d₀ tab k p).1.1.2 = p.1.1.2 := fun p => by
    rw [bridgeWrite_apply_lt₀]
    exact ⟨writeV_logs A C₁ F d₂ tab (bT A C₁ F kq) k p.1.1.1.1, rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · change (bridgeWrite e A C₁ F d₂ E kq d₀ tab k s.1).1 ∈ goodW e A C₁ F d₂ E kq d₀ k
    obtain ⟨hl, hf, ha⟩ := h1 s.1
    exact goodW_congr e A C₁ F d₂ E kq d₀ k hs hl hf ha
  · change ((bridgeWrite e A C₁ F d₂ E kq d₀ tab k).symm s.1).1 ∈ goodW e A C₁ F d₂ E kq d₀ k
    obtain ⟨hl, hf, ha⟩ := h1 ((bridgeWrite e A C₁ F d₂ E kq d₀ tab k).symm s.1)
    rw [Equiv.apply_symm_apply] at hl hf ha
    exact goodW_congr e A C₁ F d₂ E kq d₀ k hs hl.symm hf.symm ha.symm

/-- **The bridge with the drops `β`, with the request points of a table**, has the law of its
instance with the replies of the table at the requests' counts, for drops that keep the
requests (`hβr`) and the absorbed logs (`hβl`); the drops act after the request points. -/
theorem simLaw_bridgeDrops_instLog (hA : A.TracePreserving) (tab : A.OuterTab Req₂ Resp₂)
    (hβr : ∀ (j n : ℕ) x, reqV A C₁ F d₂ j (β n x).1 = reqV A C₁ F d₂ j x.1)
    (hβl : ∀ n q, (β n q).1.1.adv.workspace.1.1.logs = q.1.1.adv.workspace.1.1.logs) :
    simLaw e ((bridgeAlgDrops e A C₁ F d₂ E kq d₀ β).withSteps
        (bridgeStepsDrops e A C₁ F d₂ E kq d₀ β tab)) =
      simLaw e ((bridgeAlgDrops e A C₁ F d₂ E kq d₀ β).instLog
        fun _ prev q => A.tabAt tab (ReqQueryAlg.countND d₂ prev) q) :=
  ReqQueryAlg.simLaw_withPerm_withSteps_eq_instLog e (bridgeAlg e A C₁ F d₂ E kq d₀)
    (bridgeDropPerms e A C₁ F d₂ E kq d₀ β)
    (fun _ prev q => A.tabAt tab (ReqQueryAlg.countND d₂ prev) q)
    (bridgeRep_write e A C₁ F d₂ E kq d₀ tab) (goodS e A C₁ F d₂ E kq d₀)
    (bridgeAlg_req_write e A C₁ F d₂ E kq d₀)
    (fun k s _ => bridge_hA e A C₁ F d₂ E kq d₀ tab k s)
    (bridge_hP e A C₁ F d₂ E kq d₀ hA tab) (bridge_h0 e A C₁ F d₂ E kq d₀ tab)
    (bridge_hG e A C₁ F d₂ E kq d₀ hA tab)
    (fun k s hs => bridgeWrite_goodS e A C₁ F d₂ E kq d₀ tab k s hs)
    (fun k s hs => bridgeDropPerms_goodS e A C₁ F d₂ E kq d₀ β hβl k s hs)
    (fun k j p => bridgeAlg_req_bridgeDropPerms e A C₁ F d₂ E kq d₀ β hβr k j p)

end Drops

/-- **The drops of the local queries on the registers of the expanded coherent run**:
`baseDrop` on the core register and the query register at the steps of the composition, the
identity after them. -/
noncomputable abbrev dropEAdds :=
  cohDropAt e E kq ((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id)
    (extOut A C₁ F d₀ (tab₀ A)) fun j => addsDrop C₁ F ω P (tab₀ A) j

/-- **The drops on the bridge's registers.** -/
noncomputable def bridgeDropAdds (i : Fin (bT A C₁ F kq + 1)) :
    Equiv.Perm (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :=
  castPerms e E kq ((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id)
    (extOut A C₁ F d₀ (tab₀ A)) (bridgeAlg e A C₁ F d₂ E kq d₀) (bridgeReg_eq e A C₁ F d₂ E kq d₀)
    (dropEAdds e A C₁ F E kq d₀ P ω) i

/-- **The bridge with the drops**: the bridge with each step read after the drops of the local
queries of `D` at `ω`. -/
noncomputable def bridgeAlgAdds :
    ReqQueryAlg (Bits m) (BitStr I J) Req₂ Resp₂ (bT A C₁ F kq)
      (BaseGame.Tuple (Bits m) B (ExtReg A C₁ Req₂ Resp₂) kq) :=
  (bridgeAlg e A C₁ F d₂ E kq d₀).withPerm (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω)

/-- **The steps of the bridge with the drops, with the request points of the table `tab`.** -/
noncomputable def bridgeStepsAdds (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1)) :
    QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ]
      QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :=
  (permOp (bridgeWrite e A C₁ F d₂ E kq d₀ tab k)).trans
    ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).step k)

/-- **The bridge with the drops, with the request points of a table**, has the law of the
expanded coherent run of the composition read after the table's request points and then the
drops. -/
theorem simLaw_bridgeAdds_withSteps (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e ((bridgeAlg e A C₁ F d₂ E kq d₀).withSteps
        (bridgeStepsAdds e A C₁ F d₂ E kq d₀ P ω tab)) =
      simLaw e (expandAdv e E kq
        ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).precomp
        fun j => (queryWorkPerm (writeV A C₁ F d₂ tab (bT A C₁ F kq) j)).trans
          (addsDrop C₁ F ω P (tab₀ A) j)).toQueryAlgCoh.mapOut (extOut A C₁ F d₀ (tab₀ A)))) :=
  simLaw_bridgeDrops_withSteps e A C₁ F d₂ E kq d₀ (fun j => addsDrop C₁ F ω P (tab₀ A) j) tab

/-- **The drops on the bridge's registers at a step of the composition**, written out. -/
theorem bridgeDropAdds_apply_lt (k : Fin (bT A C₁ F kq + 1))
    (h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1)
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k p =
      (((((addsDrop C₁ F ω P (tab₀ A) k (p.1.1.1.1, p.2)).1, p.1.1.1.2), p.1.1.2), p.1.2),
        (addsDrop C₁ F ω P (tab₀ A) k (p.1.1.1.1, p.2)).2) := by
  unfold bridgeDropAdds castPerms dropEAdds cohDropAt
  rw [Equiv.trans_apply, Equiv.trans_apply, dif_pos h]
  refine (equiv_cast_symm_apply_eq_iff _ _ _).2 ?_
  have hq := equiv_cast_heq (bridgeReg_eq e A C₁ F d₂ E kq d₀) p
  revert hq
  generalize Equiv.cast (bridgeReg_eq e A C₁ F d₂ E kq d₀) p = q
  intro hq
  with_reducible
    have hqp : q = p := eq_of_heq hq
  subst hqp
  rfl

/-- **The drops on the bridge's registers after the steps of the composition** are the
identity. -/
theorem bridgeDropAdds_apply_ge (k : Fin (bT A C₁ F kq + 1))
    (h : ¬ (k : ℕ) < (bridgeCompose A C₁ F).depth + 1)
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k p = p := by
  unfold bridgeDropAdds castPerms dropEAdds cohDropAt
  rw [Equiv.trans_apply, Equiv.trans_apply, dif_neg h, Equiv.Perm.one_apply]
  exact (equiv_cast_symm_apply_eq_iff _ _ _).2 (equiv_cast_heq _ p)

omit [Nonempty (Bits m)] in
/-- The request points read the logs, which replacing the workspace keeps. -/
theorem reqV_setWorkC (j : ℕ) (c : (bridgeCompose A C₁ F).V) (x : A.W) :
    reqV A C₁ F d₂ j (setWorkC C₁ F c x) = reqV A C₁ F d₂ j c := by
  have hl : (setWorkC C₁ F c x).1.adv.1.1.1.1.logs = c.1.adv.1.1.1.1.logs := rfl
  simp only [reqV, hl]

omit [Nonempty (Bits m)] in
theorem reqV_addsDrop (j n : ℕ) (x : QueryReg (bridgeCompose A C₁ F).V 1 (Bits m) (BitStr I J)) :
    reqV A C₁ F d₂ j (addsDrop C₁ F ω P (tab₀ A) n x).1 = reqV A C₁ F d₂ j x.1 :=
  addsDrop_induct C₁ F ω P (tab₀ A) n (fun q => reqV A C₁ F d₂ j q.1 = reqV A C₁ F d₂ j x.1)
    (fun q y hq => (reqV_setWorkC A C₁ F d₂ j q.1 y).trans hq) x rfl

/-- **The drops commute with the bridge's writes of the table's replies.** -/
theorem bridgeDropAdds_bridgeWrite (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k (bridgeWrite e A C₁ F d₂ E kq d₀ tab k p) =
      bridgeWrite e A C₁ F d₂ E kq d₀ tab k (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k p) := by
  by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDropAdds_apply_lt e A C₁ F d₂ E kq d₀ P ω k h
        (bridgeWrite e A C₁ F d₂ E kq d₀ tab k p),
      bridgeWrite_apply_lt₀ e A C₁ F d₂ E kq d₀ tab k (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k p),
      bridgeDropAdds_apply_lt e A C₁ F d₂ E kq d₀ P ω k h p,
      bridgeWrite_apply_lt₀ e A C₁ F d₂ E kq d₀ tab k p]
    have h2 : addsDrop C₁ F ω P (tab₀ A) k
        (writeV A C₁ F d₂ tab (bT A C₁ F kq) k p.1.1.1.1, p.2) =
        (writeV A C₁ F d₂ tab (bT A C₁ F kq) k (addsDrop C₁ F ω P (tab₀ A) k (p.1.1.1.1, p.2)).1,
          (addsDrop C₁ F ω P (tab₀ A) k (p.1.1.1.1, p.2)).2) :=
      (addsDrop_writeV A C₁ F d₂ ω P tab (bT A C₁ F kq) k k (p.1.1.1.1, p.2)).symm
    dsimp only
    rw [h2]
  · rw [bridgeDropAdds_apply_ge e A C₁ F d₂ E kq d₀ P ω k h,
      bridgeDropAdds_apply_ge e A C₁ F d₂ E kq d₀ P ω k h]

/-- **The drops keep every request of the bridge.** -/
theorem bridgeAlg_req_bridgeDropAdds (k j : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).req j (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k p).1 =
      (bridgeAlg e A C₁ F d₂ E kq d₀).req j p.1 := by
  rw [bridgeAlg_req_eq, bridgeAlg_req_eq]
  by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDropAdds_apply_lt e A C₁ F d₂ E kq d₀ P ω k h]
    exact reqV_addsDrop A C₁ F d₂ P ω j k (p.1.1.1.1, p.2)
  · rw [bridgeDropAdds_apply_ge e A C₁ F d₂ E kq d₀ P ω k h]

/-- **The drops keep the supports of the bridge's simulated run.** -/
theorem bridgeDropAdds_goodS (k : Fin (bT A C₁ F kq + 1))
    (s : SimRegister (bridgeAlg e A C₁ F d₂ E kq d₀).W I J m (bT A C₁ F kq))
    (hs : s ∈ goodS e A C₁ F d₂ E kq d₀ k) :
    (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k).prodCongr (Equiv.refl _) s ∈
      goodS e A C₁ F d₂ E kq d₀ k := by
  change (bridgeDropAdds e A C₁ F d₂ E kq d₀ P ω k s.1).1 ∈ goodW e A C₁ F d₂ E kq d₀ k
  by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDropAdds_apply_lt e A C₁ F d₂ E kq d₀ P ω k h]
    refine goodW_congr e A C₁ F d₂ E kq d₀ k hs ?_ rfl rfl
    change (addsDrop C₁ F ω P (tab₀ A) k (s.1.1.1.1.1, s.1.2)).1.1.adv.workspace.1.1.logs = _
    exact addsDrop_induct C₁ F ω P (tab₀ A) k
      (fun q => q.1.1.adv.workspace.1.1.logs = s.1.1.1.1.1.1.adv.workspace.1.1.logs)
      (fun q y hq => hq) _ rfl
  · rw [bridgeDropAdds_apply_ge e A C₁ F d₂ E kq d₀ P ω k h]
    exact hs

/-- **The bridge with the drops, with the request points of a table**, has the law of its
instance with the replies of the table at the requests' counts. -/
theorem simLaw_bridgeAdds_instLog (hA : A.TracePreserving) (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).withSteps
        (bridgeStepsAdds e A C₁ F d₂ E kq d₀ P ω tab)) =
      simLaw e ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).instLog
        fun _ prev q => A.tabAt tab (ReqQueryAlg.countND d₂ prev) q) :=
  simLaw_bridgeDrops_instLog e A C₁ F d₂ E kq d₀ (fun j => addsDrop C₁ F ω P (tab₀ A) j) hA tab
    (fun j n x => reqV_addsDrop A C₁ F d₂ P ω j n x)
    (fun n q => addsDrop_induct C₁ F ω P (tab₀ A) n
      (fun q' => q'.1.1.adv.workspace.1.1.logs = q.1.1.adv.workspace.1.1.logs)
      (fun q y hq => hq) q rfl)


/-! ### The local queries' drops as instances -/

/-- **The drops of the local queries on the registers of the expanded coherent run**: `baseDrop`
on the core register and the query register at the steps of the composition, the identity after
them (`dropEAdds` of `BaseW.toAddsW`). -/
noncomputable abbrev dropE :=
  dropEAdds e A C₁ F E kq d₀ D.toAddsW ω

/-- **The drops on the bridge's registers** (`bridgeDropAdds` of `BaseW.toAddsW`). -/
noncomputable abbrev bridgeDrop (i : Fin (bT A C₁ F kq + 1)) :
    Equiv.Perm (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :=
  bridgeDropAdds e A C₁ F d₂ E kq d₀ D.toAddsW ω i

/-- **The bridge with the drops**: the bridge with each step read after the drops of the local
queries of `D` at `ω` (`bridgeAlgAdds` of `BaseW.toAddsW`). -/
noncomputable abbrev bridgeAlgDrop :
    ReqQueryAlg (Bits m) (BitStr I J) Req₂ Resp₂ (bT A C₁ F kq)
      (BaseGame.Tuple (Bits m) B (ExtReg A C₁ Req₂ Resp₂) kq) :=
  bridgeAlgAdds e A C₁ F d₂ E kq d₀ D.toAddsW ω

/-- **The steps of the bridge with the drops, with the request points of the table `tab`.** -/
noncomputable abbrev bridgeStepsDrop (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1)) :
    QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ]
      QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :=
  bridgeStepsAdds e A C₁ F d₂ E kq d₀ D.toAddsW ω tab k

/-- **The bridge with the drops, with the request points of a table**, has the law of the
expanded coherent run of the composition read after the table's request points and then the
drops. -/
theorem simLaw_bridgeDrop_withSteps (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e ((bridgeAlg e A C₁ F d₂ E kq d₀).withSteps
        (bridgeStepsDrop e A C₁ F d₂ E kq d₀ D ω tab)) =
      simLaw e (expandAdv e E kq
        ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).precomp
        fun j => (queryWorkPerm (writeV A C₁ F d₂ tab (bT A C₁ F kq) j)).trans
          (baseDrop C₁ F D ω (tab₀ A) j)).toQueryAlgCoh.mapOut (extOut A C₁ F d₀ (tab₀ A)))) :=
  simLaw_bridgeAdds_withSteps e A C₁ F d₂ E kq d₀ D.toAddsW ω tab

/-- **The drops on the bridge's registers at a step of the composition**, written out. -/
theorem bridgeDrop_apply_lt (k : Fin (bT A C₁ F kq + 1))
    (h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1)
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    bridgeDrop e A C₁ F d₂ E kq d₀ D ω k p =
      (((((baseDrop C₁ F D ω (tab₀ A) k (p.1.1.1.1, p.2)).1, p.1.1.1.2), p.1.1.2), p.1.2),
        (baseDrop C₁ F D ω (tab₀ A) k (p.1.1.1.1, p.2)).2) :=
  bridgeDropAdds_apply_lt e A C₁ F d₂ E kq d₀ D.toAddsW ω k h p

/-- **The drops on the bridge's registers after the steps of the composition** are the
identity. -/
theorem bridgeDrop_apply_ge (k : Fin (bT A C₁ F kq + 1))
    (h : ¬ (k : ℕ) < (bridgeCompose A C₁ F).depth + 1)
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    bridgeDrop e A C₁ F d₂ E kq d₀ D ω k p = p :=
  bridgeDropAdds_apply_ge e A C₁ F d₂ E kq d₀ D.toAddsW ω k h p

/-- **The drops commute with the bridge's writes of the table's replies.** -/
theorem bridgeDrop_bridgeWrite (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    bridgeDrop e A C₁ F d₂ E kq d₀ D ω k (bridgeWrite e A C₁ F d₂ E kq d₀ tab k p) =
      bridgeWrite e A C₁ F d₂ E kq d₀ tab k (bridgeDrop e A C₁ F d₂ E kq d₀ D ω k p) :=
  bridgeDropAdds_bridgeWrite e A C₁ F d₂ E kq d₀ D.toAddsW ω tab k p

/-- **The drops keep every request of the bridge.** -/
theorem bridgeAlg_req_bridgeDrop (k j : Fin (bT A C₁ F kq + 1))
    (p : QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).req j (bridgeDrop e A C₁ F d₂ E kq d₀ D ω k p).1 =
      (bridgeAlg e A C₁ F d₂ E kq d₀).req j p.1 := by
  rw [bridgeAlg_req_eq, bridgeAlg_req_eq]
  by_cases h : (k : ℕ) < (bridgeCompose A C₁ F).depth + 1
  · rw [bridgeDrop_apply_lt e A C₁ F d₂ E kq d₀ D ω k h]
    exact reqV_addsDrop A C₁ F d₂ D.toAddsW ω j k (p.1.1.1.1, p.2)
  · rw [bridgeDrop_apply_ge e A C₁ F d₂ E kq d₀ D ω k h]

/-- **The drops keep the supports of the bridge's simulated run.** -/
theorem bridgeDrop_goodS (k : Fin (bT A C₁ F kq + 1))
    (s : SimRegister (bridgeAlg e A C₁ F d₂ E kq d₀).W I J m (bT A C₁ F kq))
    (hs : s ∈ goodS e A C₁ F d₂ E kq d₀ k) :
    (bridgeDrop e A C₁ F d₂ E kq d₀ D ω k).prodCongr (Equiv.refl _) s ∈
      goodS e A C₁ F d₂ E kq d₀ k :=
  bridgeDropAdds_goodS e A C₁ F d₂ E kq d₀ D.toAddsW ω k s hs

/-- **The bridge with the drops, with the request points of a table**, has the law of its
instance with the replies of the table at the requests' counts. -/
theorem simLaw_bridgeDrop_instLog (hA : A.TracePreserving) (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).withSteps
        (bridgeStepsDrop e A C₁ F d₂ E kq d₀ D ω tab)) =
      simLaw e ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).instLog
        fun _ prev q => A.tabAt tab (ReqQueryAlg.countND d₂ prev) q) :=
  simLaw_bridgeAdds_instLog e A C₁ F d₂ E kq d₀ D.toAddsW ω hA tab

omit [Nonempty (Bits m)] in
/-- The drops change the composition's register only on the part, or not at all. -/
theorem baseDrop_fst (n : ℕ) (x : QueryReg (bridgeCompose A C₁ F).V 1 (Bits m) (BitStr I J)) :
    (baseDrop C₁ F D ω (tab₀ A) n x).1 = x.1 ∨
      ∃ v, (baseDrop C₁ F D ω (tab₀ A) n x).1 = ((D.tp F (tab₀ A)).wLens (C := C₁)).set x.1 v := by
  rcases baseDrop_cases C₁ F D ω n with h0 | ⟨s, pend, h0⟩
  · rw [h0]
    exact Or.inl rfl
  · rw [h0]
    exact Or.inr ⟨_, rfl⟩

omit [Nonempty (Bits m)] in
/-- The request points read the logs, which writing the part keeps. -/
theorem reqV_wLens_set (j : ℕ) (c : (bridgeCompose A C₁ F).V) (v : Fin A.width → Y₁) :
    reqV A C₁ F d₂ j (((D.tp F (tab₀ A)).wLens (C := C₁)).set c v) = reqV A C₁ F d₂ j c := by
  have hl : (((D.tp F (tab₀ A)).wLens (C := C₁)).set c v).1.adv.1.1.1.1.logs =
      c.1.adv.1.1.1.1.logs := rfl
  simp only [reqV, hl]

omit [Nonempty (Bits m)] in
theorem reqV_baseDrop (j n : ℕ) (x : QueryReg (bridgeCompose A C₁ F).V 1 (Bits m) (BitStr I J)) :
    reqV A C₁ F d₂ j (baseDrop C₁ F D ω (tab₀ A) n x).1 = reqV A C₁ F d₂ j x.1 := by
  rcases baseDrop_fst A C₁ F D ω n x with h | ⟨v, h⟩
  · rw [h]
  · rw [h]
    exact reqV_wLens_set A C₁ F d₂ D j x.1 v

end GordieHowe.Quantum
