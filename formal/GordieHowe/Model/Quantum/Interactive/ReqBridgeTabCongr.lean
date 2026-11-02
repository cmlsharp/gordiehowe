-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ReqBridgeExt

@[expose] public section

/-!
# The extraction run depends on the table only through the relay's answers

`simLaw_extRun_congr_tab`: for two tables `tab` and `tab'` whose replies give the same answers
`F.answer₂` to every outer request, the extraction runs at `tab` and at `tab'` have the same law.

- `absTabSwapOf t t'`, `tabPOf t t'`, `tabWOf t t'`, `tabSwapOf t t'`: the swap of the table
  register between `t` and `t'` on the registers of the adversary absorbed with a table, on its
  registers other than the query pairs, on the trace-preserving form's workspace, and on the
  composition's registers.
- `tabAnswer_congr`, `afterPermTab_congr`, `afterAtTab_absTabSwapOf`: the table's handling of a
  slot reads the table only through the answers, so it commutes with the swap on the columns whose
  table register holds `t`; `stepTab_op_absTabSwapOf`: a step of the adversary absorbed with a
  table across the swap.
- `advKraus_tabRelOf`, `relAt_tabSwapOf`, `tabHopOf`, `tabKeepsOf`: the composition's Kraus maps
  along the swap on the columns whose table register holds `t`, and they keep these columns.
- `Alg.precomp_eq_self`: precomposition with identity permutations changes nothing.
-/

open Finset Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

/-- **Precomposition with identity permutations** is the algorithm itself. -/
theorem Alg.precomp_eq_self {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    [DecidableEq Y] (A : Alg X Y O) (σ : Fin (A.depth + 1) → Equiv.Perm (QueryReg A.V 1 X Y))
    (hσ : ∀ i, σ i = Equiv.refl _) : A.precomp σ = A := by
  obtain rfl : σ = fun _ => Equiv.refl _ := funext hσ
  rfl

open GordieHowe.QROM KrausRel ProdPerm KindAlg

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)
  (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)

/-- **Two tables give the same answers**: at every outer request `q` of a request `r` at request
number `c`, the answers of `F.answer₂` to the replies of `t` and `t'` at every count agree. -/
def SameAnswers (t t' : A.OuterTab Req₂ Resp₂) : Prop :=
  ∀ c c' r q, F.outer c r = some q →
    F.answer₂ c r (A.tabAt t c' q) = F.answer₂ c r (A.tabAt t' c' q)

/-! ### The adversary absorbed with a table, across the swap of two tables -/

section AbsTab

variable {A F}

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Fintype Req₂]
  [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁] in
/-- Tables with the same answers give the same replies of every slot. -/
theorem tabAnswer_congr {t t' : A.OuterTab Req₂ Resp₂} (h : SameAnswers A F t t')
    (lg : LogReg Req A.slots) (j : Fin A.slots) (r : Req) (a : Option Resp₁) :
    A.tabAnswer F t lg j r a = A.tabAnswer F t' lg j r a := by
  unfold AdaptiveIAlg.tabAnswer
  rcases hq : F.outer (A.reqCount lg j) r with _ | q
  · rfl
  · exact h _ _ r q hq

omit [Fintype Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Fintype Req₂] [DecidableEq Req₂]
  [Fintype Resp₂] [DecidableEq Resp₂] in
/-- **Tables with the same answers handle every slot alike.** -/
theorem afterPermTab_congr {t t' : A.OuterTab Req₂ Resp₂} (h : SameAnswers A F t t')
    (j : Fin A.slots) (s : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁) :
    A.afterPermTab F t j s = A.afterPermTab F t' j s := by
  rcases hl : s.1.1.logs j with _ | r
  · rw [afterPermTab_of_none A F _ j hl, afterPermTab_of_none A F _ j hl]
  · rw [afterPermTab_of_some A F _ j hl, afterPermTab_of_some A F _ j hl, tabAnswer_congr h]

variable (A) in
/-- **The swap of the table register between `t` and `t'`**, on the registers of the adversary
absorbed with a table. -/
def absTabSwapOf (t t' : A.OuterTab Req₂ Resp₂) : Equiv.Perm (AbsD A Req₁ Resp₁ Req₂ Resp₂) :=
  Function.Involutive.toPerm (fun d => (((d.1.1.1, Equiv.swap t t' d.1.1.2), d.1.2), d.2))
    fun d => by simp

/-- **The table's handling before a step commutes with the swap** on the columns whose table
register holds `t`, for tables with the same answers. -/
theorem afterAtTab_absTabSwapOf {t t' : A.OuterTab Req₂ Resp₂} (h : SameAnswers A F t t')
    (k : ℕ) (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) (hd : d.1.1.2 = t) :
    A.afterAtTab F k (absTabSwapOf A t t' d) = absTabSwapOf A t t' (A.afterAtTab F k d) := by
  by_cases hk : 0 < k ∧ k - 1 < A.slots
  · obtain ⟨j, rfl⟩ : ∃ j : Fin A.slots, k = (j : ℕ) + 1 := ⟨⟨k - 1, hk.2⟩, by simp; omega⟩
    have h2 : (absTabSwapOf A t t' d).1.1.2 = t' := by
      change Equiv.swap t t' d.1.1.2 = t'
      rw [hd, Equiv.swap_apply_left]
    rw [afterAtTab_succ, afterAtTab_succ, h2]
    have h3 : absTabSwapOf A t t' (absIns A d.1.1.2 (A.afterPermTab F d.1.1.2 j (absStrip A d))) =
        absIns A t' (A.afterPermTab F t j (absStrip A d)) := by
      rw [hd]
      change (((_, Equiv.swap t t' t), _), _) = _
      rw [Equiv.swap_apply_left]
    rw [h3, ← afterPermTab_congr h]
    rfl
  · rw [afterAtTab_of_not A F hk]
    rfl

/-- **A step of the adversary absorbed with a table across the swap of two tables**: its operator
at the swapped rows and a column `b'` whose handling before the step is the swapped handling of
`b` is the operator at `b`. -/
theorem stepTab_op_absTabSwapOf (t t' : A.OuterTab Req₂ Resp₂) (k : StepIdx A.slots A.post)
    (r : (A.absorb F.base).R) (a b b' : AbsD A Req₁ Resp₁ Req₂ Resp₂)
    (hb : A.afterAtTab F k b' = absTabSwapOf A t t' (A.afterAtTab F k b)) :
    (A.stepTab F k).op r (absTabSwapOf A t t' a) b' = (A.stepTab F k).op r a b := by
  rw [stepTab_op_apply, stepTab_op_apply, hb, KrausMap.tensorId_reindex_op_apply,
    KrausMap.tensorId_reindex_op_apply]
  change _ * (1 : Matrix (A.OuterTab Req₂ Resp₂) (A.OuterTab Req₂ Resp₂) ℂ)
      (Equiv.swap t t' ((A.tabLift F (A.setAt F.base k)).symm a).1.1.2)
      (Equiv.swap t t' (A.afterAtTab F k b).1.1.2) = _ * (1 : Matrix _ _ ℂ)
      ((A.tabLift F (A.setAt F.base k)).symm a).1.1.2 (A.afterAtTab F k b).1.1.2
  rw [Matrix.one_apply, Matrix.one_apply]
  simp only [(Equiv.swap t t').injective.eq_iff]
  rfl

end AbsTab

/-! ### The composition across the swap of two tables -/

section Bridge

variable (t t' : A.OuterTab Req₂ Resp₂)

/-- **The swap of the table register between `t` and `t'`**, on the adversary's registers other
than the query pairs. -/
def tabPOf (u : A.OuterTab Req₂ Resp₂) :
    Equiv.Perm ((A.absorbTab F u).W × Req₁ × Option Resp₁) :=
  Function.Involutive.toPerm (fun p => ((p.1.1, Equiv.swap t t' p.1.2), p.2))
    fun p => by
      simp only [Equiv.swap_apply_self]

/-- **The swap of the table register between `t` and `t'`** on the workspace of the
trace-preserving form. -/
noncomputable def tabWOf (u : A.OuterTab Req₂ Resp₂) : Equiv.Perm (A.absorbTab F u).toTPKindAlg.W :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl (A.AbsW (Resp' := Resp₁)))
    (Equiv.swap t t')) (Equiv.refl (Fin (A.budget + 2)))

/-- **The swap of the table register between `t` and `t'`** on the registers of the composition at
the table `t'`. -/
noncomputable abbrev tabSwapOf : Equiv.Perm ((A.absorbTab F t').toTPKindAlg.CW C₁ × (Bits m × BitStr I J × Bool)) :=
  WorkRel.wa ((A.absorbTab F t').toTPKindAlg.advOne C₁
    (wsOne (B := (A.absorbTab F t').toTPKindAlg) (tabWOf A F t t' t')))

/-- **The composition's registers whose table register holds `t`.** -/
noncomputable abbrev tabBlockOf : Set ((A.absorbTab F t').toTPKindAlg.CW C₁ × (Bits m × BitStr I J × Bool)) :=
  WorkRel.ancSet ((A.absorbTab F t').toTPKindAlg.advIn C₁ {w | w.1.2 = t})

/-- **The adversary's Kraus map `k` of the composition at `t'` across the swap**, and it keeps the
table register, for tables with the same answers. -/
theorem advKraus_tabRelOf (hA : A.TracePreserving) (h : SameAnswers A F t t')
    (k : StepIdx A.slots A.post) :
    WorkRel.Rel ((A.absorbTab F t').toTPKindAlg.advOne C₁
          (wsOne (B := (A.absorbTab F t').toTPKindAlg) (tabWOf A F t t' t')))
        ((A.absorbTab F t').toTPKindAlg.advOne C₁
          (wsOne (B := (A.absorbTab F t').toTPKindAlg) (tabWOf A F t t' t')))
        ((A.absorbTab F t').toTPKindAlg.advIn C₁ {w | w.1.2 = t})
        ((A.absorbTab F t').toTPKindAlg.advKraus C₁ k) ∧
      WorkRel.Keeps ((A.absorbTab F t').toTPKindAlg.advIn C₁ {w | w.1.2 = t})
        ((A.absorbTab F t').toTPKindAlg.advKraus C₁ k) := by
  have hA' : ∀ k, ((A.absorbTab F t').step k).haltOp = 0 := fun k =>
    AdaptiveIAlg.TracePreserving.haltOp_eq_zero (A.absorbTab_tracePreserving F hA t') k
  have hD := AdaptiveIAlg.drel_toTPKindAlg hA' (ρ' := tabPOf A F t t' t')
    (ρ := tabPOf A F t t' t') (fun _ => rfl) (Sd := {w | w.2 = t}) (k := k)
    fun r a b hb => stepTab_op_absTabSwapOf (F := F) t t' k r a b _
      (afterAtTab_absTabSwapOf h k b hb)
  have hK := AdaptiveIAlg.dkeeps_toTPKindAlg hA' (Sd := {w | w.2 = t}) (k := k)
    fun r a b hb hne => (stepTab_table A F hne).trans hb
  exact ⟨rel_advKraus fun z a b hb => hD z a b hb, keeps_advKraus hK⟩

/-- **The composition's circuit at `t'` is along the swap with trivial writes**, for tables with
the same answers. -/
theorem relAt_tabSwapOf (hA : A.TracePreserving) (h : SameAnswers A F t t') :
    ReprogrammedCircuit.RelAt ((A.absorbTab F t').toTPKindAlg.advOne C₁
        (wsOne (B := (A.absorbTab F t').toTPKindAlg) (tabWOf A F t t' t')))
      ((A.absorbTab F t').toTPKindAlg.wOf C₁ fun _ => Equiv.refl _)
      ((A.absorbTab F t').toTPKindAlg.advIn C₁ {w | w.1.2 = t})
      ((A.absorbTab F t').toTPKindAlg.fullCircBoth C₁) 0
      (((A.absorbTab F t').toTPKindAlg.advOne C₁
        (wsOne (B := (A.absorbTab F t').toTPKindAlg) (tabWOf A F t t' t'))).trans
        ((A.absorbTab F t').toTPKindAlg.wOf C₁ (fun _ => Equiv.refl _) 0))
      ((A.absorbTab F t').toTPKindAlg.advOne C₁
        (wsOne (B := (A.absorbTab F t').toTPKindAlg) (tabWOf A F t t' t'))) := by
  refine relAt_fullCircBoth (fun _ => rfl) (fun _ _ => rfl) (fun j => ?_) (fun b => ?_) ?_ <;>
  · rw [trans_wOf_of_refl rfl]
    exact advKraus_tabRelOf A C₁ F t t' hA h _

open QROM.KrausRel in
/-- **The composition's Kraus maps at `t'` along the swap**: on every column whose table register
holds `t`, Kraus map `i` along the swap is Kraus map `i`, for tables with the same answers. -/
theorem tabHopOf (hA : A.TracePreserving) (h : SameAnswers A F t t')
    (i : Fin (((A.absorbTab F t').toTPKindAlg.composeBothOut C₁ id).depth + 1)) :
    OpRel (queryWorkPerm (tabSwapOf A C₁ F t t')) {p | p.1 ∈ tabBlockOf A C₁ F t t'}
      (((A.absorbTab F t').toTPKindAlg.composeBothOut C₁ id).step i)
      ((((A.absorbTab F t').toTPKindAlg.composeBothOut C₁ id).step i).permConj
        (queryWorkPerm (WorkRel.wa ((A.absorbTab F t').toTPKindAlg.wOf C₁
          (fun _ => Equiv.refl _) i))) (Equiv.refl _)) := by
  have hR := ReprogrammedCircuit.relAt_toAlg_step (relAt_tabSwapOf A C₁ F t t' hA h)
    (MState.withAnc KindAlg.x₀ ((A.absorbTab F t').toTPKindAlg.initSys C₁)) (fun v => id v.1) i
  exact WorkRel.Rel.opRel_permConj fun r a b hb => hR.1 r a b hb

open QROM.KrausRel in
/-- **The composition's Kraus maps at `t'` keep the table register** at `t`. -/
theorem tabKeepsOf (hA : A.TracePreserving) (h : SameAnswers A F t t')
    (i : Fin (((A.absorbTab F t').toTPKindAlg.composeBothOut C₁ id).depth + 1)) :
    Keeps {p | p.1 ∈ tabBlockOf A C₁ F t t'}
      (((A.absorbTab F t').toTPKindAlg.composeBothOut C₁ id).step i) :=
  (ReprogrammedCircuit.relAt_toAlg_step (relAt_tabSwapOf A C₁ F t t' hA h)
    (MState.withAnc KindAlg.x₀ ((A.absorbTab F t').toTPKindAlg.initSys C₁))
    (fun v => id v.1) i).2.keeps

/-- The swap of the constant register's values along the composition is the table swap. -/
theorem vLift_constSwap_eq_tabSwapOf :
    ((A.absorbTab F t').toTPKindAlg.vLift C₁ ((A.absorb F.base).constSwap t t')).prodCongr
        (Equiv.refl _) = queryWorkPerm (m := m) (I := I) (J := J) (tabSwapOf A C₁ F t t') :=
  Equiv.ext fun _ => rfl

/-- **The extraction run depends on the table only through the relay's answers**: for a
trace-preserving adversary and two tables whose replies give the same answers `F.answer₂` to every
outer request, the extraction runs at the two tables have the same law. -/
theorem simLaw_extRun_congr_tab (hA : A.TracePreserving) (h : SameAnswers A F t t') :
    simLaw e (extRun e A C₁ F E kq d₀ t) = simLaw e (extRun e A C₁ F E kq d₀ t') := by
  rw [AdaptiveIAlg.simLaw_withConst_reinit C₁ e E kq (A.absorb F.base) (A.stepTab F) t t'
    (extOut A C₁ F d₀ t) (extOut A C₁ F d₀ t') (heq_of_eq (funext fun o => by cases o <;> rfl))]
  refine (simLaw_expandCoh_relabel e E kq ((A.absorbTab F t').toTPKindAlg.composeBothOut C₁ id)
    ((AdaptiveIAlg.stepsTP_toTPKindAlg _).tracePreserving_composeBothOut C₁ id) _ _ (extOut A C₁ F d₀ t')
    (tabSwapOf A C₁ F t t') (tabBlockOf A C₁ F t t') (tabHopOf A C₁ F t t' hA h)
    (tabKeepsOf A C₁ F t t' hA h)
    (fun a b hab => by
      have h' := KindAlg.composeBothOut_init_ne C₁ _ hab
      exact AdaptiveIAlg.toTPKindAlg_withConst_init_ne (A.absorb F.base) (A.stepTab F) t h')
    ((AdaptiveIAlg.composeBothOut_withConst_init C₁ (A.absorb F.base) (A.stepTab F) t t').trans
      (by rw [vLift_constSwap_eq_tabSwapOf]))
    (fun _ => rfl)).trans ?_
  refine congrArg (fun Q : Alg (Bits m) (BitStr I J) _ =>
    simLaw e (expandAdv e E kq (Q.toQueryAlgCoh.mapOut (extOut A C₁ F d₀ t')))) ?_
  exact Alg.precomp_eq_self _ _ fun _ => Equiv.ext fun _ => rfl

end Bridge

end GordieHowe.Quantum
