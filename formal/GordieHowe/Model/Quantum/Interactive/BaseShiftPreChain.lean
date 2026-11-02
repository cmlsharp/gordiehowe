-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftPreRun
public import GordieHowe.Model.Quantum.Interactive.BaseShiftChain

@[expose] public section

/-!
# The extraction run of an adversary with additions before and after its Kraus maps

For an adversary `A` whose Kraus maps `st₀` are `A`'s read after permutations `σ k`
(`KrausMap.RightPerm`), followed by a sorted list of additions `P` (`st'`), the extraction run at a
table is the expanded coherent run of the composition of `A` at the empty table, read after the
table's request points, the drops of `P` and the lifted permutations at the starts of the query
intervals.

- `AdaptiveIAlg.preT`: the permutations on the trace-preserving form of `A` absorbed with the
  empty table.
- `AdaptiveIAlg.AddsW.simLaw_extRun_bridgeAt`: the extraction run with additions after replaced
  Kraus maps as the bridge at those Kraus maps; `AdaptiveIAlg.simLaw_bridgeCompose_pre`;
  `AdaptiveIAlg.AddsW.simLaw_extRun_withSteps_pre`; `AdaptiveIAlg.AddsW.simLaw_extRun_instLog_pre`:
  as an instance of the bridge with drops (`bridgeAlgDrops`), with `AdaptiveIAlg.preTabPerm_logs`,
  `AdaptiveIAlg.prePerms_logs`, `addsDrop_logs`, `reqV_of_logs`; `AdaptiveIAlg.afterAtTab_pairs`,
  `AdaptiveIAlg.preTabPerm_pairs`, `AdaptiveIAlg.prePerms_keeps`.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  [Inhabited Req₂] [Nonempty (Bits m)] {Y₁ : Type} [AddGroup Y₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂) (ω : Bits m → Y₁)

/-- **The permutations at the inputs of the Kraus maps on the trace-preserving form of `A`
absorbed with the empty table** (`AdaptiveIAlg.preTabPerm`, `cntPerm`). -/
def AdaptiveIAlg.preT (σ : StepIdx A.slots A.post → Equiv.Perm (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (k : StepIdx A.slots A.post) :
    Equiv.Perm (DReg (A.absorbTab F (tab₀ A)).toTPKindAlg.W A.width (Bits m) (BitStr I J) Req₁
      Resp₁) :=
  (A.absorbTab F (tab₀ A)).cntPerm (AdaptiveIAlg.preTabPerm F (tab₀ A) k (σ k))

omit [Nonempty (Bits m)] in
/-- **The permutations at the inputs of the Kraus maps keep the absorbed logs.** -/
theorem AdaptiveIAlg.preTabPerm_logs (tab : A.OuterTab Req₂ Resp₂) (k : StepIdx A.slots A.post)
    (π : Equiv.Perm (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width (Bits m) (BitStr I J) Req₁
      Resp₁) :
    (AdaptiveIAlg.preTabPerm F tab k π d).1.1.1.logs = d.1.1.1.logs := by
  have h2 : ∀ d', ((A.afterAtTab F k).symm d').1.1.1.logs = d'.1.1.1.logs := fun d' => by
    rw [← A.afterAtTab_logs' F k ((A.afterAtTab F k).symm d'), Equiv.apply_symm_apply]
  change ((A.afterAtTab F k).symm (tabPerm F tab π (A.afterAtTab F k d))).1.1.1.logs = _
  exact (h2 _).trans ((show (tabPerm F tab π (A.afterAtTab F k d)).1.1.1.logs =
    (A.afterAtTab F k d).1.1.1.logs from rfl).trans (A.afterAtTab_logs' F k d))

omit [Nonempty (Bits m)] in
/-- **The lifted permutations at the starts of the query intervals keep the absorbed logs.** -/
theorem AdaptiveIAlg.prePerms_logs
    (σ : StepIdx A.slots A.post → Equiv.Perm (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (n : ℕ) (p : ReprogrammedQueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) (Bits m)
      (BitStr I J)) :
    (KindAlg.prePerms C₁ (A.preT F σ) n p).1.1.adv.workspace.1.1.logs =
      p.1.1.adv.workspace.1.1.logs := by
  have hT : ∀ m q, ((A.absorbTab F (tab₀ A)).toTPKindAlg.preTail C₁ m q).1.1.adv.workspace.1.1.logs
      = q.1.1.adv.workspace.1.1.logs := fun m q =>
    congrArg (fun x => x.1.1.1.logs) (KindAlg.preTail_adv (T := (A.absorbTab F (tab₀ A)).toTPKindAlg) (C := C₁) m q)
  have hTi : ∀ m q,
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.preTail C₁ m)⁻¹ q |>.1.1.adv.workspace.1.1.logs =
        q.1.1.adv.workspace.1.1.logs := fun m q => by
    rw [← hT m (((A.absorbTab F (tab₀ A)).toTPKindAlg.preTail C₁ m)⁻¹ q)]
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  unfold KindAlg.prePerms
  split
  · rfl
  · rename_i k _
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hTi]
    refine Eq.trans ?_ (hT (k : ℕ) p)
    exact A.preTabPerm_logs F (tab₀ A) k (σ k) _

omit [Nonempty (Bits m)] in
/-- **The handling of a slot's reply keeps the query pairs.** -/
theorem AdaptiveIAlg.afterAtTab_pairs (k : ℕ)
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width (Bits m) (BitStr I J) Req₁
      Resp₁) :
    (A.afterAtTab F k d).2 = d.2 := by
  unfold AdaptiveIAlg.afterAtTab
  split
  · change (((A.afterPermTab F d.1.1.2 _) ((d.1.1.1, d.1.2), d.2)).2) = d.2
    unfold AdaptiveIAlg.afterPermTab
    simp only [Equiv.trans_apply]
    have h1 : ∀ (j : Fin A.slots) (d' : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m)
        (BitStr I J) Req₁ Resp₁), (A.storePerm j d').2 = d'.2 := fun j d' => by
      unfold AdaptiveIAlg.storePerm AlgShape.storePerm
      dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
      split_ifs <;> rfl
    have h2 : ∀ t (j : Fin A.slots) (d' : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m)
        (BitStr I J) Req₁ Resp₁), (A.answerPermTab F t j d').2 = d'.2 := fun t j d' => by
      unfold AdaptiveIAlg.answerPermTab
      dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
      split <;> rfl
    have h3 : ∀ (j : Fin A.slots) (d' : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m)
        (BitStr I J) Req₁ Resp₁), (A.clearPerm F.base j d').2 = d'.2 := fun j d' => by
      unfold AdaptiveIAlg.clearPerm AlgShape.clearPerm
      dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
      split <;> rfl
    rw [h3, h2, h1]
  · rfl

omit [Nonempty (Bits m)] in
/-- **The permutations at the inputs of the Kraus maps keep the query pairs** when `π` does. -/
theorem AdaptiveIAlg.preTabPerm_pairs (tab : A.OuterTab Req₂ Resp₂) (k : StepIdx A.slots A.post)
    {π : Equiv.Perm (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)} (hπ : ∀ x, (π x).2 = x.2)
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width (Bits m) (BitStr I J) Req₁
      Resp₁) :
    (AdaptiveIAlg.preTabPerm F tab k π d).2 = d.2 := by
  have h2 : ∀ d', ((A.afterAtTab F k).symm d').2 = d'.2 := fun d' => by
    rw [← A.afterAtTab_pairs F k ((A.afterAtTab F k).symm d'), Equiv.apply_symm_apply]
  change ((A.afterAtTab F k).symm (tabPerm F tab π (A.afterAtTab F k d))).2 = _
  refine (h2 _).trans ?_
  refine Eq.trans ?_ (A.afterAtTab_pairs F k d)
  exact hπ _

omit [Nonempty (Bits m)] in
/-- **The lifted permutations at the starts of the query intervals keep the ancilla and the query
register** when `σ` keeps the query pairs. -/
theorem AdaptiveIAlg.prePerms_keeps
    (σ : StepIdx A.slots A.post → Equiv.Perm (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (hσ : ∀ k x, (σ k x).2 = x.2) (n : ℕ)
    (p : ReprogrammedQueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) (Bits m)
      (BitStr I J)) :
    (KindAlg.prePerms C₁ (A.preT F σ) n p).1.2 = p.1.2 ∧
      (KindAlg.prePerms C₁ (A.preT F σ) n p).2 = p.2 := by
  unfold KindAlg.prePerms
  split
  · exact ⟨rfl, rfl⟩
  · rename_i k _
    have hσ' : ∀ d, (A.preT F σ k d).2 = d.2 := fun d =>
      A.preTabPerm_pairs F (tab₀ A) k (hσ k) _
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, KindAlg.advLift_eq_setAdv1 (C := C₁) hσ',
      KindAlg.preTail_inv_setAdv1]
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    exact ⟨rfl, rfl⟩

/-- **The composition at the empty table at Kraus maps read after `σ`** (`hst₀`) has the law of
that of `A` read after the lifted permutations at the starts of the query intervals
(`KindAlg.simLaw_composeBothOut_pre` at the trace-preserving form of `A` absorbed with the empty
table, the Kraus maps at its registers by `AdaptiveIAlg.tpStepOf`). -/
theorem AdaptiveIAlg.simLaw_bridgeCompose_pre
    (σ : StepIdx A.slots A.post → Equiv.Perm (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (s₀ : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
      (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (hst₀ : ∀ k, KrausMap.RightPerm (σ k) (s₀ k) (A.step k))
    (hTP : A.TracePreserving) (hTP₀ : (A.withStep s₀).TracePreserving) {Z : Type}
    (E : Expansion (Bits m) B Z) (kq : ℕ)
    (W : ℕ → Equiv.Perm (ReprogrammedQueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁)
      (Bits m) (BitStr I J)))
    (g : Option ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) → Z) :
    simLaw e (expandAdv e E kq (((bridgeComposeAt A C₁ F
        ((A.absorbTab F (tab₀ A)).tpStepOf false ((A.withStep s₀).stepTab F))).precomp
          fun j => W j).toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E kq (((bridgeCompose A C₁ F).precomp fun j =>
        (W j).trans (KindAlg.prePerms C₁ (A.preT F σ) j)).toQueryAlgCoh.mapOut g)) :=
  KindAlg.simLaw_composeBothOut_pre (T := (A.absorbTab F (tab₀ A)).toTPKindAlg)
    (C := C₁) (st := (A.absorbTab F (tab₀ A)).tpStepOf false ((A.withStep s₀).stepTab F)) E e kq
    (σ := A.preT F σ)
    (fun k => AdaptiveIAlg.rightPerm_absorbTabStep_tpStepOf s₀ k (hst₀ k) hTP₀ hTP (tab₀ A))
    (AdaptiveIAlg.stepsTP_toTPKindAlg _)
    (fun k => (A.absorbTab F (tab₀ A)).tpStepOf_tp false _ k) W g

/-- **The extraction run of `A.withStep st'` as the bridge at replaced Kraus maps**: when `st'` is
`s₀` followed by the sorted list of additions `P` (`hst`), none after the last Kraus map (`hlast`),
trace-preserving Kraus maps and outer requests never `d₂`, the extraction run at `tab` has the law
of the composition of `A` absorbed with the empty table at the Kraus maps of `s₀`
(`bridgeComposeAt`, `AdaptiveIAlg.tpStepOf`), read after the table's request points and then the
drops of `P`, with the extraction run's output. -/
theorem AdaptiveIAlg.AddsW.simLaw_extRun_bridgeAt (P : A.AddsW Y₁)
    (s₀ st' : StepIdx A.slots A.post →
      KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
        (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (hst : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (s₀ k))
    (hTP₀ : (A.withStep s₀).TracePreserving) (hTP' : (A.withStep st').TracePreserving)
    (hlast : P.Off lastStep) (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (E : Expansion (Bits m) B (ExtReg (A.withStep st') C₁ Req₂ Resp₂)) (kq : ℕ)
    (d₀ : ExtReg (A.withStep st') C₁ Req₂ Resp₂) (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e (extRun e (A.withStep st') C₁ F E kq d₀ tab) =
      simLaw e (expandAdv e E kq (((bridgeComposeAt A C₁ F
        ((A.absorbTab F (tab₀ A)).tpStepOf false ((A.withStep s₀).stepTab F))).precomp fun j =>
          (queryWorkPerm (writeV A C₁ F d₂ tab (bT A C₁ F kq) j)).trans
            (addsDrop C₁ F ω P (tab₀ A) j)).toQueryAlgCoh.mapOut
              (extOut A C₁ F d₀ (tab₀ A)))) := by
  refine (AdaptiveIAlg.AddsW.simLaw_extRun_steps (e := e) (A := A) (C₁ := C₁) (F := F) (ω := ω)
    (st' := st') P s₀ hst hTP₀ hTP' hlast E kq d₀ tab).trans ?_
  have hK : (A.absorbTab F tab).toTPKindAlg.withStep
      ((A.absorbTab F tab).tpStepOf false (A.absorbTabStep F s₀)) =
      ({ (A.absorbTab F (tab₀ A)).toTPKindAlg with
        step := (A.absorbTab F (tab₀ A)).tpStepOf false ((A.withStep s₀).stepTab F),
        init := (A.absorbTab F tab).toTPKindAlg.init } :
          KindAlg _ O) := by
    unfold KindAlg.withStep
    congr 1
  refine (KindAlg.simLaw_congr_kindAlg_precomp C₁ e E kq hK _ _
    (addsDrop_heq (A := A) C₁ F ω P tab) _ (extOut A C₁ F d₀ (tab₀ A))
    (heq_of_eq (funext fun o => by
      rw [extOut_withStep A C₁ F st' d₀ tab o]
      cases o <;> rfl))).trans ?_
  exact P.simLaw_reinit_precomp_dropAt A C₁ F d₂ ω e E kq
    (bridgeStepsOK_steps A C₁ F d₂ s₀ hTP₀ hout) tab (extOut A C₁ F d₀ (tab₀ A)) fun _ => rfl

/-- **The extraction run of an adversary with additions before and after its Kraus maps** (module
docstring): for Kraus maps `s₀` that are `A`'s read after `σ` (`hst₀`), then `st'` that are those
followed by the sorted list `P` at `ω` (`hst`), none after the last Kraus map (`hlast`),
trace-preserving Kraus maps and outer requests never the dummy (`hout`). -/
theorem AdaptiveIAlg.AddsW.simLaw_extRun_withSteps_pre (P : A.AddsW Y₁)
    (σ : StepIdx A.slots A.post → Equiv.Perm (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (s₀ st' : StepIdx A.slots A.post →
      KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
        (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (hst₀ : ∀ k, KrausMap.RightPerm (σ k) (s₀ k) (A.step k))
    (hst : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (s₀ k))
    (hTP : A.TracePreserving) (hTP₀ : (A.withStep s₀).TracePreserving)
    (hTP' : (A.withStep st').TracePreserving) (hlast : P.Off lastStep)
    (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (E : Expansion (Bits m) B (ExtReg (A.withStep st') C₁ Req₂ Resp₂)) (kq : ℕ)
    (d₀ : ExtReg (A.withStep st') C₁ Req₂ Resp₂) (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e (extRun e (A.withStep st') C₁ F E kq d₀ tab) =
      simLaw e (expandAdv e E kq (((bridgeCompose A C₁ F).precomp fun j =>
        ((queryWorkPerm (writeV A C₁ F d₂ tab (bT A C₁ F kq) j)).trans
          (addsDrop C₁ F ω P (tab₀ A) j)).trans
            (KindAlg.prePerms C₁ (A.preT F σ) j)).toQueryAlgCoh.mapOut
          (extOut A C₁ F d₀ (tab₀ A)))) :=
  (P.simLaw_extRun_bridgeAt e A C₁ F d₂ ω s₀ st' hst hTP₀ hTP' hlast hout E kq d₀ tab).trans
    (AdaptiveIAlg.simLaw_bridgeCompose_pre e A C₁ F σ s₀ hst₀ hTP hTP₀ E kq
      (fun j => (queryWorkPerm (writeV A C₁ F d₂ tab (bT A C₁ F kq) j)).trans
        (addsDrop C₁ F ω P (tab₀ A) j)) (extOut A C₁ F d₀ (tab₀ A)))

omit [Nonempty (Bits m)] in
/-- **The drops of additions keep the absorbed logs.** -/
theorem addsDrop_logs (P : A.AddsW Y₁) (n : ℕ)
    (q : ReprogrammedQueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) (Bits m) (BitStr I J)) :
    (addsDrop C₁ F ω P (tab₀ A) n q).1.1.adv.workspace.1.1.logs = q.1.1.adv.workspace.1.1.logs :=
  addsDrop_induct C₁ F ω P (tab₀ A) n
    (fun q' => q'.1.1.adv.workspace.1.1.logs = q.1.1.adv.workspace.1.1.logs)
    (fun _ _ hq => hq) q rfl

omit [Nonempty (Bits m)] in
/-- **The request points read only the absorbed logs.** -/
theorem reqV_of_logs (j : ℕ) {c c' : (bridgeCompose A C₁ F).V}
    (h : c'.1.adv.1.1.1.1.logs = c.1.adv.1.1.1.1.logs) :
    reqV A C₁ F d₂ j c' = reqV A C₁ F d₂ j c := by
  simp only [reqV, h]

/-- **The extraction run of an adversary with additions before and after its Kraus maps is an
instance of the bridge with drops**: under the hypotheses of
`AdaptiveIAlg.AddsW.simLaw_extRun_withSteps_pre`, the extraction run at the table `tab` has the law
of the instance of the bridge read after the drops of the additions and then the lifted
permutations at the starts of the query intervals (`bridgeAlgDrops`), with the replies of `tab`
at the requests' counts. -/
theorem AdaptiveIAlg.AddsW.simLaw_extRun_instLog_pre (P : A.AddsW Y₁)
    (σ : StepIdx A.slots A.post → Equiv.Perm (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (s₀ st' : StepIdx A.slots A.post →
      KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
        (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (hst₀ : ∀ k, KrausMap.RightPerm (σ k) (s₀ k) (A.step k))
    (hst : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (s₀ k))
    (hTP : A.TracePreserving) (hTP₀ : (A.withStep s₀).TracePreserving)
    (hTP' : (A.withStep st').TracePreserving) (hlast : P.Off lastStep)
    (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)
    (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e (extRun e (A.withStep st') C₁ F E kq d₀ tab) =
      simLaw e ((bridgeAlgDrops e A C₁ F d₂ E kq d₀ fun j =>
        (addsDrop C₁ F ω P (tab₀ A) j).trans (KindAlg.prePerms C₁ (A.preT F σ) j)).instLog
          fun _ prev q => A.tabAt tab (ReqQueryAlg.countND d₂ prev) q) := by
  refine (P.simLaw_extRun_withSteps_pre e A C₁ F d₂ ω σ s₀ st' hst₀ hst hTP hTP₀ hTP' hlast hout
    E kq d₀ tab).trans ?_
  refine (simLaw_bridgeDrops_withSteps e A C₁ F d₂ E kq d₀
    (fun j => (addsDrop C₁ F ω P (tab₀ A) j).trans (KindAlg.prePerms C₁ (A.preT F σ) j))
    tab).symm.trans ?_
  have hl : ∀ n q, (((addsDrop C₁ F ω P (tab₀ A) n).trans
      (KindAlg.prePerms C₁ (A.preT F σ) n)) q).1.1.adv.workspace.1.1.logs =
        q.1.1.adv.workspace.1.1.logs := fun n q =>
    (A.prePerms_logs C₁ F σ n _).trans (addsDrop_logs A C₁ F ω P n q)
  exact simLaw_bridgeDrops_instLog e A C₁ F d₂ E kq d₀ _ hTP tab
    (fun j n x => reqV_of_logs A C₁ F d₂ j (hl n x)) hl

end GordieHowe.Quantum
