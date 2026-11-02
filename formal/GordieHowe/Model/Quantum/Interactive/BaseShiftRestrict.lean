-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftChain
public import GordieHowe.Model.Quantum.Interactive.SimChallenger
public import GordieHowe.Model.Quantum.Interactive.BaseShiftPre

@[expose] public section

/-!
# The extraction run of a restricted adversary is an instance of the bridge at the zero base

`simLaw_extRun_restrictAt_instLog`: for an adversary `A` over the whole oracle `X → Y` and the
split `sp : Y ≃+ Y₁ × Y₂`, the extraction run of `A.restrictAt sp ω` at a table has the law of the
instance of the bridge of `A.restrictAt sp 0` with the drops of the base parts at `ω`
(`bridgeAlgDrop` with `restrictBaseW`), with the replies of the table at the requests' counts.

- `AdaptiveIAlg.restrictBaseW`: the local queries of `A.restrictAt sp 0` that make up
  `A.restrictAt sp ω` (the `Y₁`-parts of the answers, on the branches `stepOn`).
- `StepAdds.fstLift`, `StepAdds.fstLift_perm`, `StepAdds.fstLift_keeps_kind`,
  `AdaptiveIAlg.leftPerm_restrictAt_side`: side reads on the adversary's workspace together with
  the restriction's local queries, as one sorted list (the side reads first).
- `AdaptiveIAlg.leftPerm_restrictAt_withStep`: side reads after the Kraus maps pass through the
  restriction; `AdaptiveIAlg.rightPerm_restrictAt_withStep`: side reads before the Kraus maps
  pass through it; `AdaptiveIAlg.withStep_restrictAt_eq`: the restriction with other Kraus maps as
  `A.restrictAt sp 0` with other Kraus maps. `AdaptiveIAlg.SideSteps`: side reads before the
  Kraus maps at every base component. `extRun_restrictAt_eq_withStep`: the extraction run of `A.restrictAt sp ω` as that
  of `A.restrictAt sp 0` with the steps of `A.restrictAt sp ω`.
- `simLaw_extRun_restrictAt_instLog_simExt`: the statement at the simulation-extraction challenger
  of a simulator over the second component (`QROM.simExtChallenger`), whose queries and
  assignments are on the second component.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Y Y₁ : Type} [Fintype Y] [DecidableEq Y] [Fintype Y₁] [DecidableEq Y₁] [AddGroup Y] [AddGroup Y₁]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  (sp : Y ≃+ Y₁ × BitStr I J) {shA : AlgShape (Bits m) Y Req Resp} (A : AdaptiveIAlg shA O)

/-- **The local queries of `A.restrictAt sp 0` that make up `A.restrictAt sp ω`**: on the
`Y₁`-parts of the answers in the workspace, on the branches `A` queries after each Kraus map. -/
def AdaptiveIAlg.restrictBaseW : (A.restrictAt sp 0).BaseW Y₁ where
  Lw := sndLens A.W (Fin A.width → Y₁)
  on k w := A.stepOn k w.1
  on_set _ _ _ := rfl
  kind_set _ _ := rfl

/-- **Additions on the first factor of a product.** -/
def StepAdds.fstLift {W K X V : Type} [AddGroup V] (S : StepAdds W K X V) (U : Type) :
    StepAdds (W × U) K X V where
  nb := S.nb
  L k i := (fstLens W U).comp (S.L k i)
  on k i z := S.on k i z.1
  x k i z := S.x k i z.1
  on_set k i z v := S.on_set k i z.1 v
  x_set k i z v := S.x_set k i z.1 v

omit [Fintype Y] [DecidableEq Y] [Fintype Y₁] [DecidableEq Y₁] [AddGroup Y] in
theorem StepAdds.fstLift_perm {W K X V : Type} [AddGroup V] (S : StepAdds W K X V) (U : Type)
    (ω : X → V) (k : K) : (S.fstLift U).perm ω k = (S.perm ω k).prodCongr (Equiv.refl U) := by
  unfold StepAdds.perm
  rw [seqPerm_map (fun π => π.prodCongr (Equiv.refl U)) (Equiv.ext fun _ => rfl)
    (fun _ _ => Equiv.ext fun _ => rfl)]
  exact congrArg _ (funext fun i => Equiv.ext fun _ => rfl)

theorem StepAdds.fstLift_keeps_kind (S : StepAdds A.W (StepIdx A.slots A.post) (Bits m) Y₁)
    (hk : S.Keeps A.kind) : (S.fstLift (Fin A.width → Y₁)).Keeps (A.restrictAt sp 0).kind :=
  fun k i z v => hk k i z.1 v

/-- **Side reads on the adversary's workspace, then the restriction's local queries**: when the
steps of `A.restrictAt sp ω` followed by the side reads `S` (which keep the kind) are `st'`, the
steps `st'` are those of `A.restrictAt sp 0` followed by the list of the side reads and then the
restriction's local queries (`AdaptiveIAlg.AddsW.append`, the side reads first: they read the
workspace alone, and they commute with the local queries, which write the answers' base parts and
read only the kind). -/
theorem AdaptiveIAlg.leftPerm_restrictAt_side (ω : Bits m → Y₁)
    (S : StepAdds A.W (StepIdx A.slots A.post) (Bits m) Y₁) (hk : S.Keeps A.kind)
    (st' : StepIdx A.slots A.post → KrausMap A.R
      (DReg (A.W × (Fin A.width → Y₁)) A.width (Bits m) (BitStr I J) Req Resp)
      (DReg (A.W × (Fin A.width → Y₁)) A.width (Bits m) (BitStr I J) Req Resp))
    (h : ∀ k, KrausMap.LeftPerm (dregPermOf A.width (Bits m) (BitStr I J) Req Resp
      ((S.fstLift (Fin A.width → Y₁)).perm ω k)) (st' k) ((A.restrictAt sp ω).step k))
    (k : StepIdx A.slots A.post) :
    KrausMap.LeftPerm ((((S.fstLift (Fin A.width → Y₁)).toAddsW
      (StepAdds.fstLift_keeps_kind sp A S hk)).append (A.restrictBaseW sp).toAddsW
        fun _ _ _ => Nat.zero_le _).toStepAdds.perm ω k) (st' k) ((A.restrictAt sp 0).step k) := by
  have h1 := (leftPerm_restrictAt_step sp ω A k).trans (h k)
  have e : (((S.fstLift (Fin A.width → Y₁)).toAddsW
      (StepAdds.fstLift_keeps_kind sp A S hk)).append (A.restrictBaseW sp).toAddsW
        fun _ _ _ => Nat.zero_le _).toStepAdds.perm ω k =
      (ysAdd ω (A.stepOn k) A.width Req Resp).perm * dregPermOf A.width (Bits m) (BitStr I J) Req
        Resp ((S.fstLift (Fin A.width → Y₁)).perm ω k) := by
    erw [AdaptiveIAlg.AddsW.perm_append, AdaptiveIAlg.BaseW.toStepAdds_perm,
      StepAdds.toStepAdds_perm]
    rfl
  have hcomm : (dregPermOf A.width (Bits m) (BitStr I J) Req Resp
      ((S.fstLift (Fin A.width → Y₁)).perm ω k)) * (ysAdd ω (A.stepOn k) A.width Req Resp).perm =
      (ysAdd ω (A.stepOn k) A.width Req Resp).perm * dregPermOf A.width (Bits m) (BitStr I J) Req
        Resp ((S.fstLift (Fin A.width → Y₁)).perm ω k) := by
    refine Equiv.ext fun d => ?_
    obtain ⟨⟨⟨w, ys⟩, rest⟩, p⟩ := d
    have hon : A.stepOn k (S.perm ω k w) = A.stepOn k w := by
      unfold AdaptiveIAlg.stepOn
      rw [S.comp_perm_eq ω hk]
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, StepAdds.fstLift_perm]
    change (((S.perm ω k w, ys + fun i => if A.stepOn k w then ω (p i).1 else 0), rest), p) =
      (((S.perm ω k w, ys + fun i => if A.stepOn k (S.perm ω k w) then ω (p i).1 else 0), rest), p)
    rw [hon]
  exact fun r a b => (congrArg (fun π : Equiv.Perm _ => (st' k).op r (π a) b)
    (e.trans hcomm.symm)).trans (h1 r a b)

/-- **Side reads on the workspace after the Kraus maps pass through the restriction**: when the
steps `st` are `A`'s followed by the additions `S` at `ω` on the workspace (`h`), which keep the
kind (`hk`), the Kraus maps of `(A.withStep st).restrictAt sp ω` are those of `A.restrictAt sp ω`
followed by `S` on the first factor of the restricted workspace (`StepAdds.fstLift`): the local
query of the restriction reads only the kind of the workspace, which `S` keeps. -/
theorem AdaptiveIAlg.leftPerm_restrictAt_withStep (ω : Bits m → Y₁)
    (S : StepAdds A.W (StepIdx A.slots A.post) (Bits m) Y₁) (hk : S.Keeps A.kind)
    (st : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) Y Req Resp)
      (DReg A.W A.width (Bits m) Y Req Resp))
    (h : ∀ k, KrausMap.LeftPerm (dregPermOf A.width (Bits m) Y Req Resp (S.perm ω k)) (st k)
      (A.step k))
    (k : StepIdx A.slots A.post) :
    KrausMap.LeftPerm (dregPermOf A.width (Bits m) (BitStr I J) Req Resp
      ((S.fstLift (Fin A.width → Y₁)).perm ω k)) (((A.withStep st).restrictAt sp ω).step k)
      ((A.restrictAt sp ω).step k) := fun r a b => by
  erw [AdaptiveIAlg.restrictAt_step_op sp ω (A.withStep st) k r,
    AdaptiveIAlg.restrictAt_step_op sp ω A k r]
  simp only [Matrix.submatrix_apply, Function.comp_apply]
  have e : splitReg sp A.W A.width (Bits m) Req Resp
      ((basePerm ω ((A.withStep st).stepOn k) A.width Req Resp).symm
        (dregPermOf A.width (Bits m) (BitStr I J) Req Resp
          ((S.fstLift (Fin A.width → Y₁)).perm ω k) a)) =
      dregPermOf A.width (Bits m) Y Req Resp (S.perm ω k)
        (splitReg sp A.W A.width (Bits m) Req Resp
          ((basePerm ω (A.stepOn k) A.width Req Resp).symm a)) := by
    obtain ⟨⟨⟨w, ys⟩, rest⟩, p⟩ := a
    have hon : A.stepOn k (S.perm ω k w) = A.stepOn k w := by
      unfold AdaptiveIAlg.stepOn
      rw [S.comp_perm_eq ω hk]
    rw [StepAdds.fstLift_perm]
    change (((S.perm ω k w, rest), fun i => ((p i).1, sp.symm
      ((if A.stepOn k (S.perm ω k w) then ys i - ω (p i).1 else ys i), (p i).2))) : DReg A.W
        A.width (Bits m) Y Req Resp) = (((S.perm ω k w, rest), fun i => ((p i).1, sp.symm
      ((if A.stepOn k w then ys i - ω (p i).1 else ys i), (p i).2))))
    rw [hon]
  exact (congrArg (fun x => (st k).op r x _) e).trans (h k r _ _)

variable [Nonempty (Bits m)] (e : BitStr I J ≃ B) (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)

/-- **Side reads before the Kraus maps at every base component** (the named prerequisite of the
side-read forms of the key-free reduction): additions `S` on `A`'s registers, keeping the kind,
the request and response registers and the query pairs (`keeps_kind`, `keeps_rr`, `keeps_pairs`),
such that the Kraus maps `st ω` are `A`'s read after `S` at `ω` (`rightPerm`) and are trace
preserving (`tracePreserving`). -/
structure AdaptiveIAlg.SideSteps (st : (Bits m → Y₁) → StepIdx A.slots A.post →
    KrausMap A.R (DReg A.W A.width (Bits m) Y Req Resp)
      (DReg A.W A.width (Bits m) Y Req Resp)) where
  /-- The side reads before each Kraus map. -/
  S : StepAdds (DReg A.W A.width (Bits m) Y Req Resp) (StepIdx A.slots A.post) (Bits m) Y₁
  keeps_kind : ∀ ω k d, A.kind (S.perm ω k d).1.1 = A.kind d.1.1
  keeps_rr : ∀ ω k d, (S.perm ω k d).1.2 = d.1.2
  keeps_pairs : ∀ ω k d, (S.perm ω k d).2 = d.2
  rightPerm : ∀ ω k, KrausMap.RightPerm (S.perm ω k) (st ω k) (A.step k)
  tracePreserving : ∀ ω, (A.withStep (st ω)).TracePreserving

/-- **A permutation read before the Kraus maps passes through the restriction**, transported along
`splitReg`: the restriction's local query reads only the kind, after the Kraus map. -/
theorem AdaptiveIAlg.rightPerm_restrictAt_withStep (ω : Bits m → Y₁)
    (st : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) Y Req Resp)
      (DReg A.W A.width (Bits m) Y Req Resp))
    {π : Equiv.Perm (DReg A.W A.width (Bits m) Y Req Resp)} (k : StepIdx A.slots A.post)
    (h : KrausMap.RightPerm π (st k) (A.step k)) :
    KrausMap.RightPerm ((splitReg sp A.W A.width (Bits m) Req Resp).symm.permCongr π)
      (((A.withStep st).restrictAt sp ω).step k) ((A.restrictAt sp ω).step k) := fun r a b => by
  erw [AdaptiveIAlg.restrictAt_step_op sp ω (A.withStep st) k r,
    AdaptiveIAlg.restrictAt_step_op sp ω A k r]
  simp only [Matrix.submatrix_apply, Function.comp_apply]
  refine (h r _ _).trans ?_
  simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

omit [Nonempty (Bits m)] in
/-- **Side reads through the restriction, as other Kraus maps**: the restriction of `A` with the
Kraus maps `st` is `A.restrictAt sp 0` with the Kraus maps of that restriction. -/
theorem AdaptiveIAlg.withStep_restrictAt_eq (ω : Bits m → Y₁)
    (st : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) Y Req Resp)
      (DReg A.W A.width (Bits m) Y Req Resp)) :
    (A.withStep st).restrictAt sp ω =
      (A.restrictAt sp 0).withStep ((A.withStep st).restrictAt sp ω).step :=
  rfl

omit [Nonempty (Bits m)] in
/-- **The extraction run of `A.restrictAt sp ω` is that of `A.restrictAt sp 0` with the steps of
`A.restrictAt sp ω`.** -/
theorem extRun_restrictAt_eq_withStep (ω : Bits m → Y₁)
    (E : Expansion (Bits m) B (ExtReg (A.restrictAt sp 0) C₁ Req₂ Resp₂)) (kq : ℕ)
    (d₀ : ExtReg (A.restrictAt sp 0) C₁ Req₂ Resp₂)
    (tab : (A.restrictAt sp 0).OuterTab Req₂ Resp₂) :
    extRun e (A.restrictAt sp ω) C₁ F E kq d₀ tab =
      extRun e ((A.restrictAt sp 0).withStep (A.restrictAt sp ω).step) C₁ F E kq d₀ tab :=
  rfl

/-- `simLaw_extRun_restrictAt_instLog` with `A.restrictAt sp ω` written as `A.restrictAt sp 0`
with the steps of `A.restrictAt sp ω`. -/
theorem simLaw_extRun_restrictAt_instLog' (ω : Bits m → Y₁) (hA : A.TracePreserving)
    (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (E : Expansion (Bits m) B (ExtReg (A.restrictAt sp 0) C₁ Req₂ Resp₂)) (kq : ℕ)
    (d₀ : ExtReg (A.restrictAt sp 0) C₁ Req₂ Resp₂) (tab : (A.restrictAt sp 0).OuterTab Req₂ Resp₂) :
    simLaw e (extRun e ((A.restrictAt sp 0).withStep (A.restrictAt sp ω).step) C₁ F E kq d₀ tab) =
      simLaw e ((bridgeAlgDrop e (A.restrictAt sp 0) C₁ F d₂ E kq d₀ (A.restrictBaseW sp) ω).instLog
        fun _ prev q => (A.restrictAt sp 0).tabAt tab (ReqQueryAlg.countND d₂ prev) q) :=
  simLaw_extRun_withStep_instLog e (A.restrictAt sp 0) C₁ F d₂ (A.restrictBaseW sp) ω
    (A.restrictAt sp ω).step (fun k => leftPerm_restrictAt_step sp ω A k)
    (AdaptiveIAlg.tracePreserving_restrictAt sp 0 A hA)
    (AdaptiveIAlg.tracePreserving_restrictAt sp ω A hA)
    (fun w => AdaptiveIAlg.stepOn_lastStep A w.1) hout E kq d₀ tab

/-- **The extraction run of `A.restrictAt sp ω` is an instance of the bridge of
`A.restrictAt sp 0` with the drops of the base parts at `ω`**, for a trace-preserving `A` and a
relay whose outer requests are never the dummy. -/
theorem simLaw_extRun_restrictAt_instLog (ω : Bits m → Y₁) (hA : A.TracePreserving)
    (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (E : Expansion (Bits m) B (ExtReg (A.restrictAt sp ω) C₁ Req₂ Resp₂)) (kq : ℕ)
    (d₀ : ExtReg (A.restrictAt sp ω) C₁ Req₂ Resp₂) (tab : (A.restrictAt sp ω).OuterTab Req₂ Resp₂) :
    simLaw e (extRun e (A.restrictAt sp ω) C₁ F E kq d₀ tab) =
      simLaw e ((bridgeAlgDrop e (A.restrictAt sp 0) C₁ F d₂ E kq d₀ (A.restrictBaseW sp) ω).instLog
        fun _ prev q => (A.restrictAt sp 0).tabAt tab (ReqQueryAlg.countND d₂ prev) q) :=
  simLaw_extRun_restrictAt_instLog' sp A e C₁ F d₂ ω hA hout E kq d₀ tab

/-- **At the simulation-extraction challenger** of a simulator over the second component
(`QROM.simExtChallenger`; `simLaw_extRun_restrictAt_instLog`, which holds for every inner
challenger). -/
theorem simLaw_extRun_restrictAt_instLog_simExt {Stmt Proof SimCoins : Type} [Fintype Stmt]
    [DecidableEq Stmt] [Inhabited Stmt] [Fintype Proof] [DecidableEq Proof] [Fintype SimCoins]
    [DecidableEq SimCoins] (S : NARG.Simulator (Bits m) (BitStr I J) Stmt Proof SimCoins) (Q : ℕ)
    (F' : TwoRelay Req Resp Stmt Proof Req₂ Resp₂) (ω : Bits m → Y₁) (hA : A.TracePreserving)
    (hout : ∀ c r q, F'.outer c r = some q → q ≠ d₂)
    (E : Expansion (Bits m) B (ExtReg (A.restrictAt sp ω) (QROM.simExtChallenger S Q) Req₂ Resp₂))
    (kq : ℕ) (d₀ : ExtReg (A.restrictAt sp ω) (QROM.simExtChallenger S Q) Req₂ Resp₂)
    (tab : (A.restrictAt sp ω).OuterTab Req₂ Resp₂) :
    simLaw e (extRun e (A.restrictAt sp ω) (QROM.simExtChallenger S Q) F' E kq d₀ tab) =
      simLaw e ((bridgeAlgDrop e (A.restrictAt sp 0) (QROM.simExtChallenger S Q) F' d₂ E kq d₀
        (A.restrictBaseW sp) ω).instLog
          fun _ prev q => (A.restrictAt sp 0).tabAt tab (ReqQueryAlg.countND d₂ prev) q) :=
  simLaw_extRun_restrictAt_instLog sp A e (QROM.simExtChallenger S Q) F' d₂ ω hA hout E kq d₀ tab

end GordieHowe.Quantum
