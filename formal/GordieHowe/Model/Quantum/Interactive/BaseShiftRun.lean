-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftExt
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeExt
public import GordieHowe.Model.Quantum.Interactive.BaseShiftPreAbsorb

@[expose] public section

/-!
# The extraction run of an adversary with local queries

`simLaw_extRun_withStep`: the extraction run of `A.withStep st'`, whose Kraus maps are those of `A`
followed by local queries on a part of the workspace (`AdaptiveIAlg.BaseW`), has the law of the
composition of `A` absorbed with the table, with the local queries dropped after the queries
(`baseDrop`) and the output of the extraction run of `A.withStep st'`.

- `Alg.precomp_one`: the composition read after the identities.
- `AdaptiveIAlg.AddsW.leftPerm_tp_steps`, `AdaptiveIAlg.AddsW.simLaw_extRun_steps`: the additions
  and the extraction run against replaced Kraus maps.
- `AdaptiveIAlg.AddsW.simLaw_extRun`: for a sorted list of additions (`AdaptiveIAlg.AddsW`), the
  drops `addsDrop`; `simLaw_extRun_withStep` is its instance at the local queries.
- `KindAlg.composeBothOut_withStep_init`, `KindAlg.initSys_withStep`: the initial states do not
  read the steps.
- `addsDrop_tabSwap`, `addsDrop_writeV`, `addsDrop_tabBlock`,
  `AdaptiveIAlg.AddsW.simLaw_reinit_precomp_dropAt`: the drops against the table and the request
  points, at steps `st` with `BridgeStepsOK`; `AdaptiveIAlg.AddsW.simLaw_reinit_precomp_drop` at
  the base's steps; `baseDrop_tabSwap`, `baseDrop_writeV`, `baseDrop_tabBlock`,
  `simLaw_reinit_precomp_dropAt`, `simLaw_reinit_precomp_drop` their instances.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

/-- **An algorithm read after the identities** is the algorithm. -/
theorem Alg.precomp_one {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (Q : Alg X Y O) : (Q.precomp fun _ => 1) = Q :=
  rfl


section Run

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  [Nonempty (Bits m)] {Y₁ : Type} [AddGroup Y₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (D : A.BaseW Y₁) (ω : Bits m → Y₁)
  (st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
    (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))

/-- **The extraction run of `A.withStep st'`**, whose Kraus maps are those of `A` followed by the
sorted list of additions `P` (`hst`), none after the last Kraus map (`hlast`: no query follows it,
so no drop could make it), has the law of the composition of `A` absorbed with the table with the
additions dropped after their pairs' queries (`addsDrop`), read out as the extraction run of
`A.withStep st'`. -/
theorem AdaptiveIAlg.AddsW.simLaw_extRun (P : A.AddsW Y₁)
    (hst : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (A.step k))
    (hTP : A.TracePreserving) (hTP' : (A.withStep st').TracePreserving) (hlast : P.Off lastStep)
    (E : Expansion (Bits m) B (ExtReg (A.withStep st') C₁ Req₂ Resp₂)) (kq : ℕ)
    (d₀ : ExtReg (A.withStep st') C₁ Req₂ Resp₂) (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e (extRun e (A.withStep st') C₁ F E kq d₀ tab) =
      simLaw e (expandAdv e E kq ((((A.absorbTab F tab).toTPKindAlg.composeBothOut C₁ id).precomp
        fun j => addsDrop C₁ F ω P tab j).toQueryAlgCoh.mapOut
          (extOut (A.withStep st') C₁ F d₀ tab))) := by
  have hK := absorbTab_toTP_withStep F st' tab
  refine (KindAlg.simLaw_congr_kindAlg C₁ e E kq hK (extOut (A.withStep st') C₁ F d₀ tab)
    (extOut (A.withStep st') C₁ F d₀ tab) HEq.rfl).trans ?_
  have hβ : ∀ q : ((A.absorbTab F tab).toTPKindAlg).QueryPos C₁,
      addsDrop C₁ F ω P tab q.idx = (P.tp F tab).dropAt ω q := fun q => by
    cases q with
    | chal j i =>
      unfold addsDrop
      rw [KindShape.QueryPos.idx]
      erw [dropPos_chal (A := A) C₁ j i]
      rfl
    | pair j i =>
      unfold addsDrop
      rw [KindShape.QueryPos.idx]
      erw [dropPos_slot (A := A) C₁ j i]
      exact Equiv.ext fun q => (AdaptiveIAlg.AddsW.tp_block_eq C₁ F ω P tab _ _ _ q).symm
    | post b i =>
      unfold addsDrop
      rw [KindShape.QueryPos.idx]
      erw [dropPos_post (A := A) C₁ b i]
      exact Equiv.ext fun q => (AdaptiveIAlg.AddsW.tp_block_eq C₁ F ω P tab _ _ _ q).symm
  have h0 : addsDrop C₁ F ω P tab 0 = 1 := by
    unfold addsDrop
    rw [dropPos_zero]
  have h := KindShape.AddsAt.simLaw_composeBothOut_transport (T := (A.absorbTab F tab).toTPKindAlg)
    (C := C₁) (st' := ((A.withStep st').absorbTab F tab).toTPKindAlg.step)
    (P.tp F tab) ω E e kq (fun k => P.leftPerm_tp F ω st' hst hTP' hTP tab k)
    (AdaptiveIAlg.stepsTP_toTPKindAlg _) (hK ▸ AdaptiveIAlg.stepsTP_toTPKindAlg _)
    (fun i w => hlast i w.1.1.work) (fun _ => 1) (addsDrop C₁ F ω P tab) rfl h0 hβ
    (fun _ _ _ _ _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩) (extOut (A.withStep st') C₁ F d₀ tab)
  rw [Alg.precomp_one] at h
  simp only [Equiv.Perm.one_def, Equiv.refl_trans] at h
  exact h

/-- **`AdaptiveIAlg.AddsW.leftPerm_tp` against replaced Kraus maps `s₀`**: the trace-preserving
form of `A` absorbed with a table, with the Kraus maps `st'`, is that with the Kraus maps `s₀`
followed by the additions, when `st'` is `s₀` followed by them (`h`); both at the registers of `A`
absorbed with the table (`AdaptiveIAlg.tpStepOf`). -/
theorem AdaptiveIAlg.AddsW.leftPerm_tp_steps (P : A.AddsW Y₁)
    (s₀ : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
      (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (h : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (s₀ k))
    (hTP' : (A.withStep st').TracePreserving) (hTP₀ : (A.withStep s₀).TracePreserving)
    (tab : A.OuterTab Req₂ Resp₂) (k : StepIdx A.slots A.post) :
    KrausMap.LeftPerm ((P.tp F tab).toStepAdds.perm ω k)
      ((A.absorbTab F tab).tpStepOf false (A.absorbTabStep F st') k)
      ((A.absorbTab F tab).tpStepOf false (A.absorbTabStep F s₀) k) := by
  have h1 := AdaptiveIAlg.leftPerm_absorbTabStep_toTP_steps (B := A) (F := F) s₀ st' k (h k)
    (fun d => P.toStepAdds.comp_perm_eq ω (g := fun d => A.kind d.1.1)
      (fun k i d v => P.kind_set k i d.1.1 v) k d) (fun d => P.toStepAdds.comp_perm_eq ω
        (g := fun d => d.1.2.1) (fun _ _ _ _ => rfl) k d) hTP' hTP₀ tab
  have e : AdaptiveIAlg.tpPermOf F tab (P.toStepAdds.perm ω k) =
      (P.tp F tab).toStepAdds.perm ω k := by
    unfold StepAdds.perm
    rw [seqPerm_map (fun π => AdaptiveIAlg.tpPermOf F tab π) (Equiv.ext fun _ => rfl)
      (fun _ _ => Equiv.ext fun _ => rfl)]
    exact congrArg _ (funext fun i => Equiv.ext fun _ => rfl)
  rw [e] at h1
  exact h1

/-- **The extraction run of `A.withStep st'` against replaced Kraus maps `s₀`**: when `st'` is `s₀`
followed by the sorted list of additions `P` (`hst`), none after the last Kraus map (`hlast`), the
extraction run has the law of the composition of `A` absorbed with the table, with the Kraus maps
of `s₀` (`AdaptiveIAlg.tpStepOf`) and the additions dropped after their pairs' queries. -/
theorem AdaptiveIAlg.AddsW.simLaw_extRun_steps (P : A.AddsW Y₁)
    (s₀ : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
      (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (hst : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (s₀ k))
    (hTP₀ : (A.withStep s₀).TracePreserving) (hTP' : (A.withStep st').TracePreserving)
    (hlast : P.Off lastStep)
    (E : Expansion (Bits m) B (ExtReg (A.withStep st') C₁ Req₂ Resp₂)) (kq : ℕ)
    (d₀ : ExtReg (A.withStep st') C₁ Req₂ Resp₂) (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e (extRun e (A.withStep st') C₁ F E kq d₀ tab) =
      simLaw e (expandAdv e E kq (((((A.absorbTab F tab).toTPKindAlg.withStep
        ((A.absorbTab F tab).tpStepOf false (A.absorbTabStep F s₀))).composeBothOut C₁ id).precomp
          fun j => addsDrop C₁ F ω P tab j).toQueryAlgCoh.mapOut
            (extOut (A.withStep st') C₁ F d₀ tab))) := by
  have hK : ((A.withStep st').absorbTab F tab).toTPKindAlg =
      (A.absorbTab F tab).toTPKindAlg.withStep
        ((A.absorbTab F tab).tpStepOf false (A.absorbTabStep F st')) :=
    (absorbTab_toTP_withStep F st' tab).trans
      (congrArg (fun s => (A.absorbTab F tab).toTPKindAlg.withStep s)
        (by
          rw [AdaptiveIAlg.absorbTab_withStep (A := A) (F := F) (st' := st') tab]
          exact AdaptiveIAlg.toTPKindAlg_withStep_step (B := A.absorbTab F tab) false
            (A.absorbTabStep F st')))
  refine (KindAlg.simLaw_congr_kindAlg C₁ e E kq hK (extOut (A.withStep st') C₁ F d₀ tab)
    (extOut (A.withStep st') C₁ F d₀ tab) HEq.rfl).trans ?_
  have hβ : ∀ q : ((A.absorbTab F tab).toTPKindAlg).QueryPos C₁,
      addsDrop C₁ F ω P tab q.idx = (P.tp F tab).dropAt ω q := fun q => by
    cases q with
    | chal j i =>
      unfold addsDrop
      rw [KindShape.QueryPos.idx]
      erw [dropPos_chal (A := A) C₁ j i]
      rfl
    | pair j i =>
      unfold addsDrop
      rw [KindShape.QueryPos.idx]
      erw [dropPos_slot (A := A) C₁ j i]
      exact Equiv.ext fun q => (AdaptiveIAlg.AddsW.tp_block_eq C₁ F ω P tab _ _ _ q).symm
    | post b i =>
      unfold addsDrop
      rw [KindShape.QueryPos.idx]
      erw [dropPos_post (A := A) C₁ b i]
      exact Equiv.ext fun q => (AdaptiveIAlg.AddsW.tp_block_eq C₁ F ω P tab _ _ _ q).symm
  have h0 : addsDrop C₁ F ω P tab 0 = 1 := by
    unfold addsDrop
    rw [dropPos_zero]
  have h := KindShape.AddsAt.simLaw_withSteps_transport (T := (A.absorbTab F tab).toTPKindAlg)
    (C := C₁) (P.tp F tab) ω E e kq
    ((A.absorbTab F tab).tpStepOf false (A.absorbTabStep F s₀))
    ((A.absorbTab F tab).tpStepOf false (A.absorbTabStep F st'))
    (fun k => AdaptiveIAlg.AddsW.leftPerm_tp_steps (A := A) (F := F) (ω := ω) (st' := st') P s₀
      hst hTP' hTP₀ tab k)
    (fun k => (A.absorbTab F tab).tpStepOf_tp false _ k)
    (fun k => (A.absorbTab F tab).tpStepOf_tp false _ k)
    (fun i w => hlast i w.1.1.work) (fun _ => 1) (addsDrop C₁ F ω P tab) rfl h0 hβ
    (fun _ _ _ _ _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩) (extOut (A.withStep st') C₁ F d₀ tab)
  rw [Alg.precomp_one] at h
  simp only [Equiv.Perm.one_def, Equiv.refl_trans] at h
  exact h

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Nonempty (Bits m)] in
/-- The local queries as a list are the local query on the adversary's registers. -/
theorem AdaptiveIAlg.BaseW.toStepAdds_perm (k : StepIdx A.slots A.post) :
    (D.toAddsW.toStepAdds (Y := BitStr I J) (Req := Req) (Resp := Resp)).perm ω k =
      (wsAdd D.Lw (D.on k) (D.on_set k) ω Req Resp).perm :=
  wsAdds_perm D.Lw D.on D.on_set ω Req Resp k

/-- **The extraction run of `A.withStep st'`**, whose Kraus maps are those of `A` followed by the
local queries of `D`, has the law of the composition of `A` absorbed with the table with the local
queries dropped after the queries (`baseDrop`), read out as the extraction run of
`A.withStep st'` (`AdaptiveIAlg.AddsW.simLaw_extRun` at `BaseW.toAddsW`). -/
theorem simLaw_extRun_withStep
    (hst : ∀ k, KrausMap.LeftPerm (wsAdd D.Lw (D.on k) (D.on_set k) ω Req Resp).perm (st' k)
      (A.step k)) (hTP : A.TracePreserving) (hTP' : (A.withStep st').TracePreserving)
    (hlast : ∀ w, D.on lastStep w = false)
    (E : Expansion (Bits m) B (ExtReg (A.withStep st') C₁ Req₂ Resp₂)) (kq : ℕ)
    (d₀ : ExtReg (A.withStep st') C₁ Req₂ Resp₂) (tab : A.OuterTab Req₂ Resp₂) :
    simLaw e (extRun e (A.withStep st') C₁ F E kq d₀ tab) =
      simLaw e (expandAdv e E kq ((((A.absorbTab F tab).toTPKindAlg.composeBothOut C₁ id).precomp
        fun j => baseDrop C₁ F D ω tab j).toQueryAlgCoh.mapOut
          (extOut (A.withStep st') C₁ F d₀ tab))) :=
  AdaptiveIAlg.AddsW.simLaw_extRun e A C₁ F ω st' D.toAddsW
    (fun k => by rw [AdaptiveIAlg.BaseW.toStepAdds_perm A D ω k]; exact hst k) hTP hTP'
    (fun _ w => hlast w) E kq d₀ tab

end Run

section Reinit

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {Req Resp O T Z B' : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (C : Challenger (Bits m) (BitStr I J) Req Resp) (e : BitStr I J ≃ B')
  (E : Expansion (Bits m) B' Z) (k : ℕ)

/-- **Equal adversaries with drops and outputs equal up to the type** give expanded coherent runs
of their compositions read after the drops with the same law. -/
theorem KindAlg.simLaw_congr_kindAlg_precomp {ksK : KindShape (Bits m) (BitStr I J) Req Resp} {K K' : KindAlg ksK O}
    (h : K = K') (β : ℕ → Equiv.Perm (ReprogrammedQueryReg (K.CW C) (Bits m) (BitStr I J)))
    (β' : ℕ → Equiv.Perm (ReprogrammedQueryReg (K'.CW C) (Bits m) (BitStr I J))) (hβ : HEq β β')
    (g : Option (K.CW C) → Z) (g' : Option (K'.CW C) → Z) (hg : HEq g g') :
    simLaw e (expandAdv e E k ((((K.composeBothOut C id).precomp fun j => β j).toQueryAlgCoh).mapOut
      g)) =
      simLaw e (expandAdv e E k ((((K'.composeBothOut C id).precomp
        fun j => β' j).toQueryAlgCoh).mapOut g')) := by
  subst h
  cases hβ
  cases hg
  rfl

variable [Fintype T] [DecidableEq T] {shB : AlgShape (Bits m) (BitStr I J) Req Resp} (B : AdaptiveIAlg shB O)
  (st : StepIdx B.slots B.post →
      KrausMap B.R (DReg (B.W × T) B.width (Bits m) (BitStr I J) Req Resp)
        (DReg (B.W × T) B.width (Bits m) (BitStr I J) Req Resp))

/-- **The composition with the initial state replaced, read after drops**, is the composition
read after the drops with the initial state replaced. -/
theorem KindAlg.simLaw_composeBothOut_withInit_precomp [Nonempty (BitStr I J)]
    {ksK : KindShape (Bits m) (BitStr I J) Req Resp} (K : KindAlg ksK O)
    (ρ : MState (DReg K.W K.width (Bits m) (BitStr I J) Req Resp))
    (β : ℕ → Equiv.Perm (ReprogrammedQueryReg (K.CW C) (Bits m) (BitStr I J))) (g : Option (K.CW C) → Z) :
    simLaw e (expandAdv e E k (((({ K with init := ρ } : KindAlg _ O).composeBothOut
      C id).precomp fun j => β j).toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E k ((({ K.composeBothOut C id with
        init := MState.withAnc KindAlg.x₀
          (({ K with init := ρ } : KindAlg _ O).initSys C) } :
          Alg (Bits m) (BitStr I J) _).precomp fun j => β j).toQueryAlgCoh.mapOut g)) :=
  rfl

/-- **The composition at `t` read after drops** has the law of the composition at `t'` started at
the initial state at `t`, read after the same drops. -/
theorem AdaptiveIAlg.simLaw_withConst_reinit_precomp (t t' : T)
    (β : ℕ → Equiv.Perm (ReprogrammedQueryReg ((B.withConst T t st).toTPKindAlg.CW C) (Bits m)
      (BitStr I J)))
    (β' : ℕ → Equiv.Perm (ReprogrammedQueryReg ((B.withConst T t' st).toTPKindAlg.CW C) (Bits m)
      (BitStr I J))) (hβ : HEq β β')
    (g : Option ((B.withConst T t st).toTPKindAlg.CW C) → Z)
    (g' : Option ((B.withConst T t' st).toTPKindAlg.CW C) → Z) (hg : HEq g g') :
    simLaw e (expandAdv e E k (((((B.withConst T t st).toTPKindAlg.composeBothOut C id).precomp
      fun j => β j).toQueryAlgCoh).mapOut g)) =
      simLaw e (expandAdv e E k ((((({ (B.withConst T t' st).toTPKindAlg with
        init := (B.withConst T t st).toTPKindAlg.init } :
          KindAlg _ O).composeBothOut C id).precomp
            fun j => β' j).toQueryAlgCoh).mapOut g')) :=
  KindAlg.simLaw_congr_kindAlg_precomp C e E k (B.toTPKindAlg_withConst st t t') β β' hβ g g' hg

end Reinit

section Relabel

/-- **Kraus maps read after commuting permutations, in either order.** -/
theorem KrausMap.permConj_permConj_comm {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]
    (K : KrausMap R ι ι) {σ β : Equiv.Perm ι} (h : ∀ b, σ (β b) = β (σ b)) :
    (K.permConj σ (Equiv.refl _)).permConj β (Equiv.refl _) =
      (K.permConj β (Equiv.refl _)).permConj σ (Equiv.refl _) :=
  KrausMap.ext_op (funext fun r => by
    ext a b
    simp only [KrausMap.permConj, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.coe_refl, id, h])

end Relabel

/-- **Equal algorithms read after permutations equal up to the type** have expanded coherent runs
with the same law. -/
theorem simLaw_precomp_congr {m : ℕ} {I J B O' C' : Type} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : BitStr I J ≃ B) (E : Expansion (Bits m) B C') (k : ℕ)
    {Q Q' : Alg (Bits m) (BitStr I J) O'} (h : Q = Q')
    (σ : Fin (Q.depth + 1) → Equiv.Perm (QueryReg Q.V 1 (Bits m) (BitStr I J)))
    (σ' : Fin (Q'.depth + 1) → Equiv.Perm (QueryReg Q'.V 1 (Bits m) (BitStr I J)))
    (hσ : HEq σ σ') (g : Option O' → C') :
    simLaw e (expandAdv e E k ((Q.precomp σ).toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E k ((Q'.precomp σ').toQueryAlgCoh.mapOut g)) := by
  subst h
  cases hσ
  rfl

section WithStep

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  (C : Challenger X Y Req Resp) {ksK : KindShape X Y Req Resp} (K : KindAlg ksK O)
  (st : StepIdx K.slots K.post → KrausMap K.R (DReg K.W K.width X Y Req Resp)
    (DReg K.W K.width X Y Req Resp))

/-- **The composition's initial state does not read the steps.** -/
theorem KindAlg.composeBothOut_withStep_init :
    (({ K with step := st } : KindAlg _ O).composeBothOut C id).init =
      (K.composeBothOut C id).init :=
  rfl

/-- **The initial state of the composed registers does not read the steps.** -/
theorem KindAlg.initSys_withStep (ρ : MState (DReg K.W K.width X Y Req Resp)) :
    ({ K with step := st, init := ρ } : KindAlg _ O).initSys C =
      ({ K with init := ρ } : KindAlg _ O).initSys C :=
  rfl

end WithStep

section BridgeDrop

open KrausRel

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  {Y₁ : Type} [AddGroup Y₁]
  {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂) (D : A.BaseW Y₁) (ω : Bits m → Y₁)

/-- **The table swap commutes with the drops of additions.** -/
theorem addsDrop_tabSwap (P : A.AddsW Y₁) (tab : A.OuterTab Req₂ Resp₂) (n : ℕ) (p) :
    queryWorkPerm (tabSwap A C₁ F tab) (addsDrop C₁ F ω P (tab₀ A) n p) =
      addsDrop C₁ F ω P (tab₀ A) n (queryWorkPerm (tabSwap A C₁ F tab) p) :=
  addsDrop_comm C₁ F ω P (tab₀ A) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    n p

/-- **The request points commute with the drops of additions.** -/
theorem addsDrop_writeV (P : A.AddsW Y₁) (tab : A.OuterTab Req₂ Resp₂) (Tb k n : ℕ) (p) :
    queryWorkPerm (writeV A C₁ F d₂ tab Tb k) (addsDrop C₁ F ω P (tab₀ A) n p) =
      addsDrop C₁ F ω P (tab₀ A) n (queryWorkPerm (writeV A C₁ F d₂ tab Tb k) p) :=
  addsDrop_comm C₁ F ω P (tab₀ A)
    (fun q x => Prod.ext (writeV_setWorkC C₁ F d₂ tab Tb k q.1 x) rfl)
    (fun v => (writeV_work C₁ F d₂ tab Tb k v).1) (fun v => (writeV_work C₁ F d₂ tab Tb k v).2.1)
    (fun v => (writeV_work C₁ F d₂ tab Tb k v).2.2.2) n p

/-- **The drops of additions keep the table register.** -/
theorem addsDrop_tabBlock (P : A.AddsW Y₁) (tab : A.OuterTab Req₂ Resp₂) (n : ℕ) (p)
    (hp : p.1 ∈ tabBlock A C₁ F tab) :
    (addsDrop C₁ F ω P (tab₀ A) n p).1 ∈ tabBlock A C₁ F tab :=
  addsDrop_induct C₁ F ω P (tab₀ A) n (fun q => q.1 ∈ tabBlock A C₁ F tab)
    (fun _ _ hq => hq) p hp

/-- The table swap commutes with the drops. -/
theorem baseDrop_tabSwap (tab : A.OuterTab Req₂ Resp₂) (n : ℕ) (p) :
    queryWorkPerm (tabSwap A C₁ F tab) (baseDrop C₁ F D ω (tab₀ A) n p) =
      baseDrop C₁ F D ω (tab₀ A) n (queryWorkPerm (tabSwap A C₁ F tab) p) :=
  addsDrop_tabSwap A C₁ F ω D.toAddsW tab n p

/-- The request points commute with the drops. -/
theorem baseDrop_writeV (tab : A.OuterTab Req₂ Resp₂) (Tb k n : ℕ) (p) :
    queryWorkPerm (writeV A C₁ F d₂ tab Tb k) (baseDrop C₁ F D ω (tab₀ A) n p) =
      baseDrop C₁ F D ω (tab₀ A) n (queryWorkPerm (writeV A C₁ F d₂ tab Tb k) p) :=
  addsDrop_writeV A C₁ F d₂ ω D.toAddsW tab Tb k n p

/-- The drops keep the table register. -/
theorem baseDrop_tabBlock (tab : A.OuterTab Req₂ Resp₂) (n : ℕ) (p)
    (hp : p.1 ∈ tabBlock A C₁ F tab) : (baseDrop C₁ F D ω (tab₀ A) n p).1 ∈ tabBlock A C₁ F tab :=
  addsDrop_tabBlock A C₁ F ω D.toAddsW tab n p hp

/-- **The composition at the steps `st` started at the initial state of the table, read after the
drops of additions**, and the composition at the steps `st` read after the table's request points
and then the drops have expanded coherent runs of the same law, for steps with `BridgeStepsOK`. -/
theorem AdaptiveIAlg.AddsW.simLaw_reinit_precomp_dropAt (P : A.AddsW Y₁) (e : BitStr I J ≃ B)
    {Z : Type} (E : Expansion (Bits m) B Z) (kq : ℕ) {st : BridgeSteps A F}
    (hst : BridgeStepsOK A C₁ F d₂ st)
    (tab : A.OuterTab Req₂ Resp₂) (g : Option ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) → Z)
    (ho : ∀ v, g (some ((bridgeComposeAt A C₁ F st).out (tabSwap A C₁ F tab v))) =
      g (some ((bridgeComposeAt A C₁ F st).out v))) :
    simLaw e (expandAdv e E kq (((({ (A.absorbTab F (tab₀ A)).toTPKindAlg with
        step := st, init := (A.absorbTab F tab).toTPKindAlg.init } :
          KindAlg _ O).composeBothOut C₁ id).precomp
            fun j => addsDrop C₁ F ω P (tab₀ A) j).toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E kq (((bridgeComposeAt A C₁ F st).precomp fun j =>
        (queryWorkPerm (writeV A C₁ F d₂ tab (bT A C₁ F kq) j)).trans
          (addsDrop C₁ F ω P (tab₀ A) j)).toQueryAlgCoh.mapOut g)) :=
by
  have hT : (bridgeComposeAt A C₁ F st).depth ≤ bT A C₁ F kq := by
    rw [bT, depth_bridgeComposeAt, depth_bridgeCompose]
    exact Nat.le_add_right _ _
  refine (KindAlg.simLaw_composeBothOut_withInit_precomp C₁ e E kq
    ({ (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st } : KindAlg _ O)
    (A.absorbTab F tab).toTPKindAlg.init (addsDrop C₁ F ω P (tab₀ A)) g).trans ?_
  refine simLaw_expandCoh_relabel e E kq
    ((bridgeComposeAt A C₁ F st).precomp fun j => addsDrop C₁ F ω P (tab₀ A) j)
    (Alg.tracePreserving_precomp (hst.tp.tracePreserving_composeBothOut C₁ id) _)
    (MState.withAnc KindAlg.x₀ (({ (A.absorbTab F (tab₀ A)).toTPKindAlg with
      step := st, init := (A.absorbTab F tab).toTPKindAlg.init } :
        KindAlg _ O).initSys C₁))
    (fun j => queryWorkPerm (writeV A C₁ F d₂ tab (bT A C₁ F kq) j)) g
    (tabSwap A C₁ F tab) (tabBlock A C₁ F tab)
    (fun i => by
      have h1 := (bridgeHopAt A C₁ F d₂ hst tab (bT A C₁ F kq) hT i).permConj
        (σ := addsDrop C₁ F ω P (tab₀ A) i) (τ := Equiv.refl _)
        (fun b => (addsDrop_tabSwap A C₁ F ω P tab i b).symm) (fun _ => rfl)
        (fun b hb => addsDrop_tabBlock A C₁ F ω P tab i b hb)
      rw [KrausMap.permConj_permConj_comm _
        (fun b => addsDrop_writeV A C₁ F d₂ ω P tab (bT A C₁ F kq) i i b)] at h1
      exact h1)
    (fun i => (bridgeKeepsAt A C₁ F hst.keeps tab i).permConj
      (fun b hb => addsDrop_tabBlock A C₁ F ω P tab i b hb) fun _ ha => ha)
    (fun a b h => by
      rw [KindAlg.initSys_withStep C₁ (A.absorbTab F (tab₀ A)).toTPKindAlg st (A.absorbTab F tab).toTPKindAlg.init] at h
      have h' := KindAlg.composeBothOut_init_ne C₁ _ h
      exact AdaptiveIAlg.toTPKindAlg_withConst_init_ne (A.absorb F.base) (A.stepTab F) tab h')
    (by
      show (({ (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st } :
        KindAlg _ O).composeBothOut C₁ id).init.mat = _
      rw [KindAlg.composeBothOut_withStep_init C₁ (A.absorbTab F (tab₀ A)).toTPKindAlg st,
        KindAlg.initSys_withStep C₁ (A.absorbTab F (tab₀ A)).toTPKindAlg st (A.absorbTab F tab).toTPKindAlg.init]
      have hc := AdaptiveIAlg.composeBothOut_withConst_init C₁ (A.absorb F.base) (A.stepTab F) tab
        (tab₀ A)
      rw [vLift_constSwap_eq] at hc
      exact hc)
    ?_
  exact ho

/-- **The composition started at the initial state of the table, read after the drops of
additions**, and the composition read after the table's request points and then the drops have
expanded coherent runs of the same law (`AdaptiveIAlg.AddsW.simLaw_reinit_precomp_dropAt` at the
base's steps). -/
theorem AdaptiveIAlg.AddsW.simLaw_reinit_precomp_drop (P : A.AddsW Y₁) (e : BitStr I J ≃ B)
    {Z : Type} (E : Expansion (Bits m) B Z)
    (kq : ℕ) (hA : A.TracePreserving) (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (tab : A.OuterTab Req₂ Resp₂) (g : Option ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) → Z)
    (ho : ∀ v, g (some ((bridgeCompose A C₁ F).out (tabSwap A C₁ F tab v))) =
      g (some ((bridgeCompose A C₁ F).out v))) :
    simLaw e (expandAdv e E kq (((({ (A.absorbTab F (tab₀ A)).toTPKindAlg with
        init := (A.absorbTab F tab).toTPKindAlg.init } :
          KindAlg _ O).composeBothOut C₁ id).precomp
            fun j => addsDrop C₁ F ω P (tab₀ A) j).toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E kq (((bridgeCompose A C₁ F).precomp fun j =>
        (queryWorkPerm (writeV A C₁ F d₂ tab (bT A C₁ F kq) j)).trans
          (addsDrop C₁ F ω P (tab₀ A) j)).toQueryAlgCoh.mapOut g)) :=
  P.simLaw_reinit_precomp_dropAt A C₁ F d₂ ω e E kq (bridgeStepsOK_toTP A C₁ F d₂ hA hout) tab g ho

/-- **The composition at the steps `st` started at the initial state of the table, read after the
drops**, and the composition at `st` read after the table's request points and then the drops
have expanded coherent runs of the same law (`AdaptiveIAlg.AddsW.simLaw_reinit_precomp_dropAt` at
`BaseW.toAddsW`). -/
theorem simLaw_reinit_precomp_dropAt (e : BitStr I J ≃ B) {Z : Type} (E : Expansion (Bits m) B Z)
    (kq : ℕ) {st : BridgeSteps A F} (hst : BridgeStepsOK A C₁ F d₂ st)
    (tab : A.OuterTab Req₂ Resp₂) (g : Option ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) → Z)
    (ho : ∀ v, g (some ((bridgeComposeAt A C₁ F st).out (tabSwap A C₁ F tab v))) =
      g (some ((bridgeComposeAt A C₁ F st).out v))) :
    simLaw e (expandAdv e E kq (((({ (A.absorbTab F (tab₀ A)).toTPKindAlg with
        step := st, init := (A.absorbTab F tab).toTPKindAlg.init } :
          KindAlg _ O).composeBothOut C₁ id).precomp
            fun j => baseDrop C₁ F D ω (tab₀ A) j).toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E kq (((bridgeComposeAt A C₁ F st).precomp fun j =>
        (queryWorkPerm (writeV A C₁ F d₂ tab (bT A C₁ F kq) j)).trans
          (baseDrop C₁ F D ω (tab₀ A) j)).toQueryAlgCoh.mapOut g)) :=
  AdaptiveIAlg.AddsW.simLaw_reinit_precomp_dropAt A C₁ F d₂ ω D.toAddsW e E kq hst tab g ho

/-- **The composition started at the initial state of the table, read after the drops**, and the
composition read after the table's request points and then the drops have expanded coherent runs
of the same law (`AdaptiveIAlg.AddsW.simLaw_reinit_precomp_drop` at `BaseW.toAddsW`). -/
theorem simLaw_reinit_precomp_drop (e : BitStr I J ≃ B) {Z : Type} (E : Expansion (Bits m) B Z)
    (kq : ℕ) (hA : A.TracePreserving) (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (tab : A.OuterTab Req₂ Resp₂) (g : Option ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) → Z)
    (ho : ∀ v, g (some ((bridgeCompose A C₁ F).out (tabSwap A C₁ F tab v))) =
      g (some ((bridgeCompose A C₁ F).out v))) :
    simLaw e (expandAdv e E kq (((({ (A.absorbTab F (tab₀ A)).toTPKindAlg with
        init := (A.absorbTab F tab).toTPKindAlg.init } :
          KindAlg _ O).composeBothOut C₁ id).precomp
            fun j => baseDrop C₁ F D ω (tab₀ A) j).toQueryAlgCoh.mapOut g)) =
      simLaw e (expandAdv e E kq (((bridgeCompose A C₁ F).precomp fun j =>
        (queryWorkPerm (writeV A C₁ F d₂ tab (bT A C₁ F kq) j)).trans
          (baseDrop C₁ F D ω (tab₀ A) j)).toQueryAlgCoh.mapOut g)) :=
  AdaptiveIAlg.AddsW.simLaw_reinit_precomp_drop A C₁ F d₂ ω D.toAddsW e E kq hA hout tab g ho

end BridgeDrop

end GordieHowe.Quantum
