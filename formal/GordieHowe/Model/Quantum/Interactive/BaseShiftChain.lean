-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftBridgeDrop

@[expose] public section

/-!
# The extraction run of an adversary with local queries is an instance of the bridge with drops

`AdaptiveIAlg.AddsW.simLaw_extRun_instLog`: for `A.withStep st'`, whose Kraus maps are those of
`A` followed by a sorted list of additions `P` at `ω` (`hst`), the extraction run at a table has the
law of the instance of the bridge of `A` with the drops of the additions (`bridgeAlgAdds`), with the
replies of the table at the requests' counts. The chain: `AdaptiveIAlg.AddsW.simLaw_extRun`,
`AdaptiveIAlg.simLaw_withConst_reinit_precomp`, `AdaptiveIAlg.AddsW.simLaw_reinit_precomp_drop`,
`extOut_withStep`, `simLaw_bridgeAdds_withSteps`, `simLaw_bridgeAdds_instLog`.
`simLaw_extRun_withStep_instLog` is its instance at the local queries of `D` (`bridgeAlgDrop`).
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

/-- Equal outputs give expanded coherent runs with the same law. -/
theorem simLaw_mapOut_congr {m : ℕ} {I J B O' C' : Type} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : BitStr I J ≃ B) (E : Expansion (Bits m) B C') (k : ℕ)
    (Q : Alg (Bits m) (BitStr I J) O') {g g' : Option O' → C'} (h : g = g') :
    simLaw e (expandAdv e E k (Q.toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E k (Q.toQueryAlgCoh.mapOut g')) := by
  rw [h]

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  [Nonempty (Bits m)] {Y₁ : Type} [AddGroup Y₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂) (D : A.BaseW Y₁) (ω : Bits m → Y₁)
  (st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
    (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))

omit [Nonempty (Bits m)] in
/-- **The drops at a table are the drops at the empty table.** -/
theorem baseDrop_heq (tab : A.OuterTab Req₂ Resp₂) :
    HEq (baseDrop C₁ F D ω tab) (baseDrop C₁ F D ω (tab₀ A)) :=
  addsDrop_heq C₁ F ω D.toAddsW tab

/-- **The extraction run of `A.withStep st'` is an instance of the bridge of `A` with the drops of
additions**: for `A.withStep st'` whose Kraus maps are those of `A` followed by the sorted list of
additions `P` at `ω` (`hst`), none after the last one (`hlast`), and a relay whose outer requests
are never the dummy (`hout`), the extraction run at the table `tab` has the law of the instance of
`bridgeAlgAdds` with the replies of `tab` at the requests' counts. -/
theorem AdaptiveIAlg.AddsW.simLaw_extRun_instLog (P : A.AddsW Y₁)
    (hst : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (A.step k))
    (hTP : A.TracePreserving) (hTP' : (A.withStep st').TracePreserving) (hlast : P.Off lastStep)
    (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)
    (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e (extRun e (A.withStep st') C₁ F E kq d₀ tab) =
      simLaw e ((bridgeAlgAdds e A C₁ F d₂ E kq d₀ P ω).instLog
        fun _ prev q => A.tabAt tab (ReqQueryAlg.countND d₂ prev) q) := by
  refine (AdaptiveIAlg.AddsW.simLaw_extRun e A C₁ F ω st' P hst hTP hTP' hlast E kq d₀ tab).trans ?_
  refine (AdaptiveIAlg.simLaw_withConst_reinit_precomp C₁ e E kq (A.absorb F.base) (A.stepTab F)
    tab (tab₀ A) _ _ (addsDrop_heq C₁ F ω P tab) _ (extOut (A.withStep st') C₁ F d₀ (tab₀ A))
    (heq_of_eq (funext fun o => by cases o <;> rfl))).trans ?_
  have hx : (fun o => extOut (A.withStep st') C₁ F d₀ (tab₀ A) o) =
      fun (o : Option (CWork (shA.absorbTabS Req₂ Resp₂ (Req₁ := Req₁) (Resp₁ := Resp₁)).CntW
        A.width (Bits m) (BitStr I J) Req₁ Resp₁ A.slots C₁.q C₁.Coins)) =>
          extOut A C₁ F d₀ (tab₀ A) o :=
    funext fun o => extOut_withStep A C₁ F st' d₀ (tab₀ A) o
  refine (simLaw_mapOut_congr e E kq _ hx).trans ?_
  have ho : ∀ v, extOut A C₁ F d₀ (tab₀ A) (some ((bridgeCompose A C₁ F).out (tabSwap A C₁ F tab v))) =
      extOut A C₁ F d₀ (tab₀ A) (some ((bridgeCompose A C₁ F).out v)) := fun _ => rfl
  refine (AdaptiveIAlg.AddsW.simLaw_reinit_precomp_drop A C₁ F d₂ ω P e E kq hTP hout tab
    (extOut A C₁ F d₀ (tab₀ A)) ho).trans ?_
  refine (simLaw_bridgeAdds_withSteps e A C₁ F d₂ E kq d₀ P ω tab).symm.trans ?_
  exact simLaw_bridgeAdds_instLog e A C₁ F d₂ E kq d₀ P ω hTP tab


/-- **The extraction run of `A.withStep st'` is an instance of the bridge of `A` with the drops**:
for `A.withStep st'` whose Kraus maps are those of `A` followed by the local queries of `D` at
`ω` (`hst`) and a relay whose outer requests are never the dummy (`hout`), the extraction run at
the table `tab` has the law of the instance of
`bridgeAlgDrop` with the replies of `tab` at the requests' counts
(`AdaptiveIAlg.AddsW.simLaw_extRun_instLog` at `BaseW.toAddsW`). -/
theorem simLaw_extRun_withStep_instLog
    (hst : ∀ k, KrausMap.LeftPerm (wsAdd D.Lw (D.on k) (D.on_set k) ω Req Resp).perm (st' k)
      (A.step k)) (hTP : A.TracePreserving) (hTP' : (A.withStep st').TracePreserving)
    (hlast : ∀ w, D.on lastStep w = false)
    (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)
    (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e (extRun e (A.withStep st') C₁ F E kq d₀ tab) =
      simLaw e ((bridgeAlgDrop e A C₁ F d₂ E kq d₀ D ω).instLog
        fun _ prev q => A.tabAt tab (ReqQueryAlg.countND d₂ prev) q) :=
  AdaptiveIAlg.AddsW.simLaw_extRun_instLog e A C₁ F d₂ ω st' D.toAddsW
    (fun k => by rw [AdaptiveIAlg.BaseW.toStepAdds_perm A D ω k]; exact hst k) hTP hTP'
    (fun _ w => hlast w) hout E kq d₀ tab

end GordieHowe.Quantum
