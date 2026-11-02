-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ReqBridgeMain
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeCirc

@[expose] public section

-- The proofs below read the definition of the bridge (irreducible elsewhere).
set_option allowUnsafeReducibility true in
attribute [local reducible] GordieHowe.Quantum.bridgeAlg

/-!
# The bridge statement

`extBridge`: `ExtBridge` holds. The extraction run at a table `tab` has the law of the bridge with
the replies of `tab` at the requests' counts:

- the extraction run at `tab` has the law of the composition at the empty table started at the
  initial state of `tab` (`simLaw_extRun_reinit`);
- that run and the run of the composition with its Kraus maps read after the request points have
  the same law (`simLaw_reinit_precomp`, from `simLaw_expandCoh_relabel` with the table swap);
- the latter is the bridge with the table's request points (`simLaw_bridge_withSteps`), which has
  the law of the bridge's instance (`ReqQueryAlg.simLaw_withSteps_eq_instLog`).
-/

open Finset Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM KrausRel

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)
  (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)

/-- The initial state of the composition at the empty table started at the initial state of the
table `tab`. -/
noncomputable abbrev reinitState (tab : A.OuterTab Req₂ Resp₂) :=
  MState.withAnc KindAlg.x₀
    (({ (A.absorbTab F (tab₀ A)).toTPKindAlg with init := (A.absorbTab F tab).toTPKindAlg.init } :
      KindAlg _ O).initSys C₁)

/-- The swap of the constant register's values along the composition is the table swap. -/
theorem vLift_constSwap_eq (tab : A.OuterTab Req₂ Resp₂) :
    ((A.absorbTab F (tab₀ A)).toTPKindAlg.vLift C₁ ((A.absorb F.base).constSwap tab (tab₀ A))).prodCongr
        (Equiv.refl _) = queryWorkPerm (m := m) (I := I) (J := J) (tabSwap A C₁ F tab) :=
  Equiv.ext fun _ => rfl

-- TODO(unbundle-M4): `convert` where two instance paths are compared; remove once M1b's named
-- register types and shape-indexed AdaptiveIAlg make both sides one instance path
/-- **The extraction run at a table** has the law of the composition at the empty table started at
the initial state of the table. -/
theorem simLaw_extRun_reinit (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e (extRun e A C₁ F E kq d₀ tab) =
      simLaw e (expandAdv e E kq (({ bridgeCompose A C₁ F with init := reinitState A C₁ F tab } :
        Alg (Bits m) (BitStr I J) _).toQueryAlgCoh.mapOut (extOut A C₁ F d₀ (tab₀ A)))) := by
  have h := AdaptiveIAlg.simLaw_withConst_reinit C₁ e E kq (A.absorb F.base) (A.stepTab F) tab
    (tab₀ A) (extOut A C₁ F d₀ tab) (extOut A C₁ F d₀ (tab₀ A))
    (heq_of_eq (funext fun o => by cases o <;> rfl))
  convert h using 1

/-- **The composition started at the initial state of the table** and the composition with its
Kraus maps read after the table's request points have expanded coherent runs of the same law. -/
theorem simLaw_reinit_precomp (hA : A.TracePreserving)
    (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂) (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e (expandAdv e E kq (({ bridgeCompose A C₁ F with init := reinitState A C₁ F tab } :
        Alg (Bits m) (BitStr I J) _).toQueryAlgCoh.mapOut (extOut A C₁ F d₀ (tab₀ A)))) =
      simLaw e (expandAdv e E kq (((bridgeCompose A C₁ F).precomp fun j =>
        queryWorkPerm (writeV A C₁ F d₂ tab (bT A C₁ F kq) j)).toQueryAlgCoh.mapOut
          (extOut A C₁ F d₀ (tab₀ A)))) :=
  simLaw_expandCoh_relabel e E kq (bridgeCompose A C₁ F) (bridgeCompose_tracePreserving A C₁ F)
    (reinitState A C₁ F tab) _ (extOut A C₁ F d₀ (tab₀ A)) (tabSwap A C₁ F tab) (tabBlock A C₁ F tab)
    (bridgeHop A C₁ F d₂ hA hout tab (bT A C₁ F kq) (Nat.le_add_right _ _))
    (bridgeKeeps A C₁ F hA tab)
    (fun a b h => by
      have h' := KindAlg.composeBothOut_init_ne C₁ _ h
      exact AdaptiveIAlg.toTPKindAlg_withConst_init_ne (A.absorb F.base) (A.stepTab F) tab h')
    ((AdaptiveIAlg.composeBothOut_withConst_init C₁ (A.absorb F.base) (A.stepTab F) tab
      (tab₀ A)).trans (by rw [vLift_constSwap_eq]))
    (fun _ => rfl)


/-- **The bridge with the table's request points** has the law of the bridge's instance with the
replies of the table at the requests' counts. -/
theorem simLaw_bridge_instLog (hA : A.TracePreserving) (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e ((bridgeAlg e A C₁ F d₂ E kq d₀).withSteps (bridgeSteps e A C₁ F d₂ E kq d₀ tab)) =
      simLaw e ((bridgeAlg e A C₁ F d₂ E kq d₀).instLog
        fun _ prev q => A.tabAt tab (ReqQueryAlg.countND d₂ prev) q) :=
  ReqQueryAlg.simLaw_withSteps_eq_instLog e (bridgeAlg e A C₁ F d₂ E kq d₀)
    (fun _ prev q => A.tabAt tab (ReqQueryAlg.countND d₂ prev) q)
    (bridgeSteps e A C₁ F d₂ E kq d₀ tab) (bridgeRep_write e A C₁ F d₂ E kq d₀ tab)
    (goodS e A C₁ F d₂ E kq d₀) (bridgeAlg_req_write e A C₁ F d₂ E kq d₀)
    (fun k q _ => bridge_hS e A C₁ F d₂ E kq d₀ tab k q)
    (fun k s _ => bridge_hA e A C₁ F d₂ E kq d₀ tab k s)
    (bridge_hP e A C₁ F d₂ E kq d₀ hA tab) (bridge_h0 e A C₁ F d₂ E kq d₀ tab)
    (bridge_hG e A C₁ F d₂ E kq d₀ hA tab)

/-- **The bridge statement holds**: the extraction run at a table has the law of the bridge's
instance with the replies of the table at the requests' counts. -/
theorem extBridge : ExtBridge e A C₁ F d₂ E kq d₀ := fun hA hout tab S => by
  rw [simLaw_extRun_reinit e A C₁ F E kq d₀ tab,
    simLaw_reinit_precomp e A C₁ F d₂ E kq d₀ hA hout tab,
    ← simLaw_bridge_withSteps e A C₁ F d₂ E kq d₀ tab,
    simLaw_bridge_instLog e A C₁ F d₂ E kq d₀ hA tab]

end GordieHowe.Quantum
