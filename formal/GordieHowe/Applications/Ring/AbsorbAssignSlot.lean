-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.AbsorbAssignBlock
public import GordieHowe.Applications.Ring.KeyFreeExtractBlock
public import GordieHowe.Model.Quantum.Interactive.RelayBlockAsk

@[expose] public section

/-!
# The block hypotheses of the absorbed adversary along the witness swap

For assigning relays whose multi-request relays differ by programs `p'` swapping the main
requests and results of one request `r₀` (`MultiRelay.ProgSwap`), the absorbed adversary at a
base part with another output satisfies the block hypotheses along the witness swap `jTrip` of
a workspace permutation and the slot of the main request of the block-`j` request
(`MultiRelay.askSlot`):

- `AdaptiveIAlg.absorbSlot`, `AdaptiveIAlg.absorbSwW`: the slot and the workspace part of the
  relay's swap `relaySwap` (`Distinguisher.relSwW`), on the workspace at the base part.
- `AdaptiveIAlg.blockRel_absorbAssign_jTrip`: `blockRel_absorbAssign` along `jTrip`
  (`BlockRel.congrPerm`), for programs off the test asking main requests fixed by the swap
  (`MultiRelay.OffTagFixed`).
- `AdaptiveIAlg.jSlotStep_absorbAssign`, `AdaptiveIAlg.swapFixAway_absorbAssign`: the slot changes
  only at its step, and away from it the requests are fixed by the swap.
- `AdaptiveIAlg.mapOut_restrictAt_withStep`, `AdaptiveIAlg.tracePreserving_restrictAt_withStep`,
  `AdaptiveIAlg.tracePreserving_mapOut_withStep`: trace preservation with other Kraus maps at a
  base part and with another output.
- `AdaptiveIAlg.tracePreserving_absorbAssign_withStep`, `AdaptiveIAlg.out_absorbSwW`: the
  adversary with the swapped programs' steps is trace preserving, and the swap keeps the output.
- **`RingSignature.KeyFree.kfSwapBlock_absorbAssign`**: the hypotheses `KFSwapBlock` of the block
  layers for the absorbed adversary at the base part, along `absorbSwW` and `absorbSlot`.
- `RingSignature.KeyFree.seAlgKF_mapOut_withStep`,
  `RingSignature.KeyFree.seAlgKF_absorbAssign_eq_withStep`: the extraction adversary of the
  absorbed adversary with the programs `p'` is that of `G`'s with other Kraus maps.
-/

set_option linter.unusedSectionVars false

namespace GordieHowe.Quantum

open GordieHowe.QROM

namespace AdaptiveIAlg

section WithStepTP

variable {X Y Req Resp O O' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)
  (st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width X Y Req Resp)
    (DReg A.W A.width X Y Req Resp))

/-- **`A` at a base part with the Kraus maps `restrictStep st'` is trace preserving** when
`A.withStep st'` is. -/
theorem tracePreserving_restrictAt_withStep {Y₁ Y₂ : Type} [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : Y ≃+ Y₁ × Y₂)
    (H₁ : X → Y₁) (h : (A.withStep st').TracePreserving) :
    ((A.restrictAt sp H₁).withStep (A.restrictStep st' sp H₁)).TracePreserving :=
  (A.withStep st').tracePreserving_restrictAt sp H₁ h

/-- **`A` with another output and the Kraus maps `st'` is trace preserving** when `A.withStep st'`
is. -/
theorem tracePreserving_mapOut_withStep (g : O → O') (h : (A.withStep st').TracePreserving) :
    ((A.mapOut g).withStep st').TracePreserving :=
  mapOut_tracePreserving h g

/-- **`A` with other Kraus maps at a base part with another output** is `A` at the base part with
another output with the Kraus maps `restrictStep st'`. -/
theorem mapOut_restrictAt_withStep {Y₁ Y₂ : Type} [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : Y ≃+ Y₁ × Y₂)
    (H₁ : X → Y₁) (g : O → O') :
    ((A.withStep st').restrictAt sp H₁).mapOut g =
      ((A.restrictAt sp H₁).mapOut g).withStep (A.restrictStep st' sp H₁) :=
  rfl

end WithStepTP


open Distinguisher Classical

variable {X Y Req Resp O O' Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req] [Inhabited X]
  [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)
  (p' : (Req × Fin (Q + 1)) × (X → Option Y) → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕
    Option Resp') (Option (AssignRelay.RespD X Y Resp Req' Resp')))
  {Y₁ Y₂ : Type} [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂]
  [AddGroup Y₁] [AddGroup Y₂] (sp : Y ≃+ Y₁ × Y₂) (H₁ : X → Y₁) (f : O × (X → Option Y) → O')
  (j : ℕ) (sw : Equiv.Perm Req') (swO : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp'))
  (r₀ : (Req × Fin (Q + 1)) × (X → Option Y))

set_option quotPrecheck false in
/-- The relayed absorbed adversary's steps with the programs `p'`. -/
local notation "STp" => (A.absorbAssignP Req' Resp' Q).relayStepWith (G.relayOf Q) Q p'
  ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q))

set_option quotPrecheck false in
/-- The output of the relayed absorbed adversary. -/
local notation "OUT" => (A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q)

set_option quotPrecheck false in
/-- The query bound of the absorbed adversary's relay. -/
local notation "BR" => (A.absorbAssignP Req' Resp' Q).budget + (A.absorbAssignP Req' Resp' Q).post

set_option quotPrecheck false in
/-- The width of the absorbed adversary's pure distinguisher. -/
local notation "NW" => ((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.width

set_option quotPrecheck false in
/-- The inner swap of the absorbed adversary's relay. -/
local notation "PI" =>
  A.innerπ Q (E := Bool × ((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut.DAnc)
  (c := (A.absorbAssignP Req' Resp' Q).budget + 2) j BR swO

/-- **The slot of the main request of the block-`j` request** on the absorbed adversary's
workspace at the base part (`MultiRelay.askSlot`). -/
noncomputable def absorbSlot : ((A.absorbAssign G Q).restrictAt sp H₁).W → Option ℕ :=
  fun w => (G.relayOf Q).askSlot NW BR Q (jTest Q j) (MultiRelay.recList w.1.1.record)
    w.1.1.store w.1.1.time

/-- **The workspace part of the relay's swap** (`relaySwap`) on the absorbed adversary's workspace
at the base part, the counter and the base answers kept. -/
noncomputable def absorbSwW : Equiv.Perm ((A.absorbAssign G Q).restrictAt sp H₁).W :=
  ((relSwW (G.relayOf Q) p' BR Q (jTest Q j) (· = r₀) PI).prodCongr
    (Equiv.refl _)).prodCongr (Equiv.refl _)

set_option quotPrecheck false in
/-- The well-formed registers after step `n` with `G`'s programs, at the base part. -/
local notation "GS" => fun n => (A.absorbAssign G Q).restrictSet sp H₁
  ((A.absorbAssignP Req' Resp' Q).relayGoodAt (G.relayOf Q) Q OUT (G.relayOf Q).prog (jTest Q j)
    (A.innerGin Req' Resp' Q j) n)

set_option quotPrecheck false in
/-- The well-formed initial registers with `G`'s programs, at the base part. -/
local notation "G0" => (A.absorbAssign G Q).restrictSet sp H₁
  ((A.absorbAssignP Req' Resp' Q).relayGood₀ (G.relayOf Q) Q OUT (G.relayOf Q).prog (A.innerGin Req'
      Resp' Q j))

variable {A G Q p' sp H₁ f j sw swO r₀}

/-- **The relay's swap is `jTrip` of `absorbSwW` and `absorbSlot` on the well-formed registers**
after step `n`, for programs off the test asking main requests fixed by `sw`. -/
theorem jTrip_absorbSwW_of_mem (hoffT : (G.relayOf Q).OffTagFixed (jTest Q j) sw)
    (hidle : sw (G.relayOf Q).idle = (G.relayOf Q).idle) (hdef : sw default = default) (n : ℕ)
    (x : ((A.absorbAssign G Q).restrictAt sp H₁).W × Req' × Option Resp') (hx : x ∈ GS n) :
    (((A.absorbAssign G Q).restrictAt sp H₁).mapOut f).jTrip (A.absorbSwW G Q p' sp H₁ j swO r₀)
        sw (A.absorbSlot G Q sp H₁ j) (some n) x =
      (A.absorbAssign G Q).restrictTrip sp H₁
        ((A.absorbAssignP Req' Resp' Q).relaySwap (G.relayOf Q) Q p' OUT (jTest Q j) (· = r₀) sw
            PI) x := by
  have hx' : (x.1.1.1, x.2) ∈ GoodAt (G.relayOf Q) BR Q (jTest Q j) (A.innerGin Req' Resp' Q
      j) n := hx
  have hor := goodAt_sw_or (F := G.relayOf Q) rfl hoffT hidle hdef hx'
  obtain ⟨es, ht, -⟩ := hx'
  change (A.absorbSwW G Q p' sp H₁ j swO r₀ x.1,
      swIf (Hit (A.absorbSlot G Q sp H₁ j) x.1 (some n)) sw x.2.1, x.2.2) =
    (A.absorbSwW G Q p' sp H₁ j swO r₀ x.1,
      (G.relayOf Q).curSw (jTest Q j) sw NW BR Q x.1.1.1.record x.1.1.1.time x.2.1, x.2.2)
  congr 2
  rcases hor with hfix | ⟨hc, hs⟩
  · rcases MultiRelay.curSw_eq_or (F := G.relayOf Q) (n := NW) (b := BR) (Q := Q)
      (J := jTest Q j) sw x.1.1.1.record x.1.1.1.time with e | e <;> rw [e] <;> unfold swIf <;>
      split_ifs <;> simp [hfix]
  · rw [hc]
    have hh : Hit (A.absorbSlot G Q sp H₁ j) x.1 (some n) := (hit_some _ _ _).2 (by
      change (G.relayOf Q).askSlot NW BR Q (jTest Q j) _ _ _ = _
      exact hs.trans (congrArg some ht))
    simp [swIf, hh]

/-- **The relay's swap is `jTrip` of `absorbSwW` at `none` on the well-formed initial
registers.** -/
theorem jTrip_absorbSwW_of_mem₀
    (x : ((A.absorbAssign G Q).restrictAt sp H₁).W × Req' × Option Resp') (hx : x ∈ G0) :
    (((A.absorbAssign G Q).restrictAt sp H₁).mapOut f).jTrip (A.absorbSwW G Q p' sp H₁ j swO r₀)
        sw (A.absorbSlot G Q sp H₁ j) none x =
      (A.absorbAssign G Q).restrictTrip sp H₁
        ((A.absorbAssignP Req' Resp' Q).relaySwap (G.relayOf Q) Q p' OUT (jTest Q j) (· = r₀) sw
            PI) x := by
  have hx' : (x.1.1.1, x.2) ∈ Good₀ (G.relayOf Q) (A.innerGin Req' Resp' Q j) := hx
  obtain ⟨-, hr, -⟩ := hx'
  change (A.absorbSwW G Q p' sp H₁ j swO r₀ x.1,
      swIf (Hit (A.absorbSlot G Q sp H₁ j) x.1 none) sw x.2.1, x.2.2) =
    (A.absorbSwW G Q p' sp H₁ j swO r₀ x.1,
      (G.relayOf Q).curSw (jTest Q j) sw NW BR Q x.1.1.1.record x.1.1.1.time x.2.1, x.2.2)
  rw [hr, curSw_blank, swIf_apply_of_not _ (not_hit_none _ _)]
  rfl


set_option quotPrecheck false in
/-- The well-formed registers after step `n` with the programs `p'`, at the base part. -/
local notation "GS'" => fun n => (A.absorbAssign G Q).restrictSet sp H₁
  ((A.absorbAssignP Req' Resp' Q).relayGoodAt (G.relayOf Q) Q OUT p' (jTest Q j) (A.innerGin Req'
      Resp' Q j) n)

set_option quotPrecheck false in
/-- The well-formed initial registers with the programs `p'`, at the base part. -/
local notation "G0'" => (A.absorbAssign G Q).restrictSet sp H₁
  ((A.absorbAssignP Req' Resp' Q).relayGood₀ (G.relayOf Q) Q OUT p' (A.innerGin Req' Resp' Q j))

/-- **The block hypotheses of the absorbed adversaries along `jTrip`** of `absorbSwW` and
`absorbSlot` (`blockRel_absorbAssign`, `BlockRel.congrPerm`), for programs off the test asking
main requests fixed by `sw`. -/
theorem blockRel_absorbAssign_jTrip (h : A.TracePreserving) (hj : j < Q)
    (hS : (G.relayOf Q).SameShape p')
    (hP : (G.relayOf Q).ProgSwap p' (jTest Q j) (· = r₀) sw swO)
    (hidle : sw (G.relayOf Q).idle = (G.relayOf Q).idle) (hdef : sw default = default)
    (hswO : ∀ x, (swO x).1 = x.1 ∧ (swO x).2.1 = x.2.1)
    (hoffT : (G.relayOf Q).OffTagFixed (jTest Q j) sw) :
    ((A.absorbAssign G Q).restrictAt sp H₁).mapOut f |>.BlockRel
      ((A.absorbAssign G Q).restrictStep STp sp H₁)
      (fun w => jLabel (G.relayOf Q) (jTest Q j) w.1.1) (GS) (GS') (G0) (G0')
      (fun n => (((A.absorbAssign G Q).restrictAt sp H₁).mapOut f).jTrip
        (A.absorbSwW G Q p' sp H₁ j swO r₀) sw (A.absorbSlot G Q sp H₁ j) (some n))
      ((((A.absorbAssign G Q).restrictAt sp H₁).mapOut f).jTrip
        (A.absorbSwW G Q p' sp H₁ j swO r₀) sw (A.absorbSlot G Q sp H₁ j) none) r₀ :=
  (blockRel_absorbAssign A sp H₁ f h hj hS hP hidle hdef hswO).congrPerm (fun _ _ => rfl)
    (fun _ => rfl) (fun n x _ hx => jTrip_absorbSwW_of_mem hoffT hidle hdef n x hx)
    (fun x _ hx => jTrip_absorbSwW_of_mem₀ x hx)

/-- **The slot of `absorbSlot` changes only at its step** (`Distinguisher.jSlotStep_relay`). -/
theorem jSlotStep_absorbAssign (h : A.TracePreserving) (hj : j < Q) :
    (((A.absorbAssign G Q).restrictAt sp H₁).mapOut f).JSlotStep (GS) (G0)
      (A.absorbSlot G Q sp H₁ j) := by
  have hR := jSlotStep_relayAdv (A.absorbAssignP Req' Resp' Q) (F := G.relayOf Q) Q (J := jTest Q j)
    (Gin := A.innerGin Req' Resp' Q j) ((A.absorbAssignP Req' Resp' Q).toTPKindAlg
        true).unitOut.width_pos
    (by convert A.innerSupp_pureD (Req' := Req') (Resp' := Resp') Q j h hj) OUT
  simp -proj only [relayGoodAt_prog, relayGood₀_prog]
  exact hR.restrictAt sp H₁

/-- **Away from the slot of `absorbSlot` the requests are fixed by `sw`.** -/
theorem swapFixAway_absorbAssign (hoffT : (G.relayOf Q).OffTagFixed (jTest Q j) sw)
    (hidle : sw (G.relayOf Q).idle = (G.relayOf Q).idle) (hdef : sw default = default) :
    (((A.absorbAssign G Q).restrictAt sp H₁).mapOut f).SwapFixAway sw (A.absorbSlot G Q sp H₁ j)
      (fun w => jLabel (G.relayOf Q) (jTest Q j) w.1.1) r₀ (GS) := by
  intro j' x hx _ _ hJ
  have hx' : (x.1.1.1, x.2) ∈ GoodAt (G.relayOf Q) BR Q (jTest Q j) (A.innerGin Req' Resp' Q
      j) j' := hx
  rcases goodAt_sw_or (F := G.relayOf Q) rfl hoffT hidle hdef hx' with hf | ⟨-, hs⟩
  · exact hf
  · obtain ⟨es, ht, -⟩ := hx'
    exact absurd (hs.trans (congrArg some ht)) hJ

/-- **The absorbed adversary with the steps of the programs `p'` is trace preserving**
(`relayAdv_withProg`). -/
theorem tracePreserving_absorbAssign_withStep (hS : (G.relayOf Q).SameShape p') :
    ((((A.absorbAssign G Q).restrictAt sp H₁).mapOut f).withStep
      ((A.absorbAssign G Q).restrictStep STp sp H₁)).TracePreserving := by
  have ht : ((A.absorbAssign G Q).withStep STp).TracePreserving := by
    -- TODO(unbundle-M4): `rw [← relayAdv_withProg]` misses the unfolded goal; transport instead
    exact relayAdv_withProg (A.absorbAssignP Req' Resp' Q) Q hS
      ((A.absorbAssignP Req' Resp' Q).relayOut (G.relayOf Q)) ▸ relayAdv_tracePreserving _ _ _ _
  exact tracePreserving_mapOut_withStep _ _ f (tracePreserving_restrictAt_withStep _ _ sp H₁ ht)

/-- **The workspace swap keeps the output**, for `swO` keeping the assignments. -/
theorem out_absorbSwW (hswO : ∀ x, (swO x).2.1 = x.2.1)
    (w : ((A.absorbAssign G Q).restrictAt sp H₁).W) :
    (((A.absorbAssign G Q).restrictAt sp H₁).mapOut f).out (A.absorbSwW G Q p' sp H₁ j swO r₀ w) =
      (((A.absorbAssign G Q).restrictAt sp H₁).mapOut f).out w := by
  change f (OUT (relSwW (G.relayOf Q) p' BR Q (jTest Q j) (· = r₀) PI w.1.1)) = f (OUT w.1.1)
  unfold relayOut
  simp only [relSwW, Equiv.coe_fn_mk, innerπ, wMove, Equiv.prodCongr_apply, Prod.map]
  rw [AbsorbedWork.mapStore_work]
  congr 2
  exact A.storeTab_mapStore _ (fun i x => by
    unfold storeSwOf
    split_ifs
    · exact hswO x
    · rfl) _

end AdaptiveIAlg

end GordieHowe.Quantum

namespace GordieHowe

open Quantum Signature QROM

namespace RingSignature.KeyFree

section AbsorbAssignKF

open GordieHowe.SPBCS IOP SPTerm Quantum.AdaptiveIAlg Classical

variable {k kN kS L e N n : ℕ} {Xb Yb : Type} [DecidableEq Xb] [DecidableEq Yb]
  {TB : BaseTypes} {B : BaseSigner Xb Yb N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ : Type} {M : SPBCS Mg P X₀ k kN kS L e} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {Stmt Wit R Frg : Type} [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt]
  [Fintype R] [DecidableEq R] [Inhabited R]
  {rel : Stmt → Wit → Prop} [DecidableRel rel]
  {enc : MURequest (SignOracle.none B) n ⊕ R → ProofQuery Stmt Wit} {dummyS : Stmt}
  [Inhabited M.NIProof] {SC' : Type} [Fintype SC'] [DecidableEq SC']

local notation "Xq" => Bits (queryBits k kN kS L)

local notation "MUR" => MURequest (SignOracle.none B) n



/-- **The hypotheses of the block layers of the absorbed assigning relay at the base part**
(`KFSwapBlock`): for a trace-preserving `A`, a block `j < Q`, programs `p'` of `G`'s shape moving
the main requests by the swap `σR` of the proof queries and the results by `swO` on the request
`r₀` (keeping the outer result and the assignments), with the programs off the test asking main
requests fixed by the swap, along `absorbSwW` and `absorbSlot`; `σR` keeping the statements, the
relation and the blank tagged statement, and a simulator that does not see it. -/
theorem kfSwapBlock_absorbAssign
    {Y Req Resp O Xs Ys : Type} [Fintype Y] [DecidableEq Y] [AddGroup Ys] [Fintype Ys]
    [DecidableEq Ys] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    [Inhabited Req] [AddGroup Y] [Nonempty Y]
    {shA : AlgShape Xq Y Req Resp} {A : AdaptiveIAlg shA O}
    {G : AssignRelay Xq Y Req Resp (MUR ⊕ R) (MUResponse B ⊕ M.Response b) Xs Ys} {Q : ℕ}
    {p' : (Req × Fin (Q + 1)) × (Xq → Option Y) → OracleProg ((Xq ⊕ Xs) ⊕ (MUR ⊕ R))
      ((Y ⊕ Ys) ⊕ Option (MUResponse B ⊕ M.Response b))
      (Option (AssignRelay.RespD Xq Y Resp (MUR ⊕ R) (MUResponse B ⊕ M.Response b)))}
    {Y₁ : Type} [Fintype Y₁] [DecidableEq Y₁] [AddGroup Y₁] {sp : Y ≃+ Y₁ × XOut k e}
    {H₁ : Xq → Y₁} {f : O × (Xq → Option Y) → Frg × X₀} {j : ℕ} {σR : Equiv.Perm R}
    {swO : Equiv.Perm (AssignRelay.RespD Xq Y Resp (MUR ⊕ R) (MUResponse B ⊕ M.Response b))}
    {r₀ : (Req × Fin (Q + 1)) × (Xq → Option Y)}
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (h : A.TracePreserving) (hj : j < Q) (hS : (G.relayOf Q).SameShape p')
    (hP : (G.relayOf Q).ProgSwap p' (jTest Q j) (· = r₀) (Equiv.sumCongr (Equiv.refl _) σR) swO)
    (hidle : Equiv.sumCongr (Equiv.refl _) σR (G.relayOf Q).idle = (G.relayOf Q).idle)
    (hdef : Equiv.sumCongr (Equiv.refl _) σR (default : MUR ⊕ R) = default)
    (hswO : ∀ x, (swO x).1 = x.1 ∧ (swO x).2.1 = x.2.1)
    (hoffT : (G.relayOf Q).OffTagFixed (jTest Q j) (Equiv.sumCongr (Equiv.refl _) σR))
    (stmt_eq : ∀ q, (enc (.inr (σR q))).stmt = (enc (.inr q)).stmt)
    (rel_iff : ∀ q, rel (enc (.inr (σR q))).stmt (enc (.inr (σR q))).wit ↔
      rel (enc (.inr q)).stmt (enc (.inr q)).wit)
    (default_eq : ((Equiv.refl Stmt).prodCongr (Equiv.sumCongr (Equiv.refl _) σR))
      (default : Stmt × (MUR ⊕ R)) = default)
    (sim : ∀ x c, Psim.prog (((Equiv.refl Stmt).prodCongr (Equiv.sumCongr (Equiv.refl _) σR)) x)
      c = Psim.prog x c) :
    KFSwapBlock (rel := rel) (enc := enc) prf (((A.absorbAssign G Q).restrictAt sp H₁).mapOut f)
      Psim ((A.absorbAssign G Q).restrictStep
        ((A.absorbAssignP _ _ Q).relayStepWith (G.relayOf Q) Q p'
          ((A.absorbAssignP _ _ Q).relayOut (G.relayOf Q))) sp H₁)
      (fun w => Distinguisher.jLabel (G.relayOf Q) (jTest Q j) w.1.1) r₀
      (fun n => (A.absorbAssign G Q).restrictSet sp H₁
        ((A.absorbAssignP _ _ Q).relayGoodAt (G.relayOf Q) Q
          ((A.absorbAssignP _ _ Q).relayOut (G.relayOf Q))
          (G.relayOf Q).prog (jTest Q j) (A.innerGin _ _ Q j) n))
      (fun n => (A.absorbAssign G Q).restrictSet sp H₁
        ((A.absorbAssignP _ _ Q).relayGoodAt (G.relayOf Q) Q
          ((A.absorbAssignP _ _ Q).relayOut (G.relayOf Q))
          p' (jTest Q j) (A.innerGin _ _ Q j) n))
      ((A.absorbAssign G Q).restrictSet sp H₁
        ((A.absorbAssignP _ _ Q).relayGood₀ (G.relayOf Q) Q
          ((A.absorbAssignP _ _ Q).relayOut (G.relayOf Q))
          (G.relayOf Q).prog (A.innerGin _ _ Q j)))
      ((A.absorbAssign G Q).restrictSet sp H₁
        ((A.absorbAssignP _ _ Q).relayGood₀ (G.relayOf Q) Q
          ((A.absorbAssignP _ _ Q).relayOut (G.relayOf Q)) p'
          (A.innerGin _ _ Q j)))
      (A.absorbSwW G Q p' sp H₁ j swO r₀) σR (A.absorbSlot G Q sp H₁ j) :=
  { blockRel := blockRel_absorbAssign_jTrip h hj hS hP hidle hdef hswO hoffT
    blockNone := blockNone_absorbAssign A sp H₁ f h hj hS hP.off
    closed := fun idx _ _ _ _ hx => by
      rcases idx with _ | m
      · exact hx
      · exact hx
    closed' := fun idx _ _ _ _ hx => by
      rcases idx with _ | m
      · exact hx
      · exact hx
    slot := jSlotStep_absorbAssign h hj
    fixAway := swapFixAway_absorbAssign hoffT hidle hdef
    tp := mapOut_tracePreserving
      ((A.absorbAssign G Q).tracePreserving_restrictAt sp H₁ (absorbAssign_tracePreserving _ _ _)) f
    tp' := tracePreserving_absorbAssign_withStep hS
    stmt_eq := stmt_eq
    rel_iff := rel_iff
    default_eq := default_eq
    sim := sim
    out := fun w => congrArg (claimOfOutX prf) (out_absorbSwW (fun x => (hswO x).2) w) }

variable (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Qk : ℕ)

/-- **The extraction adversary of an adversary with other Kraus maps and another output** is that
of the adversary with another output with the steps `absorbTabStep` (rfl). -/
theorem seAlgKF_mapOut_withStep {O₂ : Type}
    {shAb : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B ⊕ M.Response b)} (Ab : AdaptiveIAlg shAb O₂)
    (st : StepIdx Ab.slots Ab.post → KrausMap Ab.R
      (DReg Ab.W Ab.width Xq (XOut k e) (MUR ⊕ R) (MUResponse B ⊕ M.Response b))
      (DReg Ab.W Ab.width Xq (XOut k e) (MUR ⊕ R) (MUResponse B ⊕ M.Response b)))
    (g : O₂ → Frg × X₀) :
    seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Qk
        ((Ab.withStep st).mapOut g) =
      (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Qk
        (Ab.mapOut g)).withStep
        (AdaptiveIAlg.absorbTabStep (Ab.mapOut g)
          (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Qk) st) :=
  rfl

-- TODO(unbundle-M4): adversaries of two equal shapes are compared by `HEq`
/-- **Heterogeneously equal adversaries of equal shapes have heterogeneously equal extraction
adversaries** at the base part `H₁` and with the output `f`. -/
theorem seAlgKF_restrictAt_mapOut_heq {Y O : Type} [Fintype Y] [DecidableEq Y] [AddGroup Y]
    {Y₁ : Type} [Fintype Y₁] [DecidableEq Y₁] [AddGroup Y₁]
    {s₁ s₂ : AlgShape Xq Y (MUR ⊕ R) (MUResponse B ⊕ M.Response b)} (hs : s₁ = s₂)
    {A₁ : AdaptiveIAlg s₁ O} {A₂ : AdaptiveIAlg s₂ O} (h : A₁ ≍ A₂) (sp : Y ≃+ Y₁ × XOut k e)
    (H₁ : Xq → Y₁) (f : O → Frg × X₀) :
    seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Qk
        ((A₁.restrictAt sp H₁).mapOut f) ≍
      seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Qk
        ((A₂.restrictAt sp H₁).mapOut f) := by
  subst hs
  cases h
  rfl

/-- **The extraction adversary of the absorbed adversary with the programs `p'` at the base
part** is that of `G`'s with the steps `absorbTabStep` of `restrictStep` of the relay's steps
with `p'` (`absorbAssign_eq_withStep`, read through the rfl junctions). -/
theorem seAlgKF_absorbAssign_eq_withStep
    {Y Req Resp O Xs Ys : Type} [Fintype Y] [DecidableEq Y] [AddGroup Ys] [Fintype Ys]
    [DecidableEq Ys] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    [Inhabited Req] [AddGroup Y] [Nonempty Y]
    {shA : AlgShape Xq Y Req Resp} {A : AdaptiveIAlg shA O}
    {G : AssignRelay Xq Y Req Resp (MUR ⊕ R) (MUResponse B ⊕ M.Response b) Xs Ys} {Q : ℕ}
    {p' : (Req × Fin (Q + 1)) × (Xq → Option Y) → OracleProg ((Xq ⊕ Xs) ⊕ (MUR ⊕ R))
      ((Y ⊕ Ys) ⊕ Option (MUResponse B ⊕ M.Response b))
      (Option (AssignRelay.RespD Xq Y Resp (MUR ⊕ R) (MUResponse B ⊕ M.Response b)))}
    {Y₁ : Type} [Fintype Y₁] [DecidableEq Y₁] [AddGroup Y₁] {sp : Y ≃+ Y₁ × XOut k e}
    {H₁ : Xq → Y₁} {f : O × (Xq → Option Y) → Frg × X₀}
    {G' : AssignRelay Xq Y Req Resp (MUR ⊕ R) (MUResponse B ⊕ M.Response b) Xs Ys}
    (hG : G'.relayOf Q = (G.relayOf Q).withProg p') (hS : (G.relayOf Q).SameShape p') :
    seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Qk
        (((A.absorbAssign G' Q).restrictAt sp H₁).mapOut f) ≍
      (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Qk
        (((A.absorbAssign G Q).restrictAt sp H₁).mapOut f)).withStep
        (AdaptiveIAlg.absorbTabStep (((A.absorbAssign G Q).restrictAt sp H₁).mapOut f)
          (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Qk)
          ((A.absorbAssign G Q).restrictStep
            ((A.absorbAssignP _ _ Q).relayStepWith (G.relayOf Q) Q p'
              ((A.absorbAssignP _ _ Q).relayOut (G.relayOf Q))) sp H₁)) := by
  -- TODO(unbundle-M4): the two sides are typed at the shapes of `G'` and of `G`, which agree only
  -- through `hG`, so the equation is heterogeneous; transport along the equal shapes.
  exact (seAlgKF_restrictAt_mapOut_heq prf keys Qk (absorbAssignS_eq_of_relayOf hG)
    (A.absorbAssign_eq_withStep hG hS) sp H₁ f).trans <| heq_of_eq <|
    (congrArg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Qk)
      (AdaptiveIAlg.mapOut_restrictAt_withStep (A.absorbAssign G Q)
        ((A.absorbAssignP _ _ Q).relayStepWith (G.relayOf Q) Q p'
          ((A.absorbAssignP _ _ Q).relayOut (G.relayOf Q))) sp H₁ f)).trans
      (seAlgKF_mapOut_withStep prf keys Qk ((A.absorbAssign G Q).restrictAt sp H₁)
        ((A.absorbAssign G Q).restrictStep ((A.absorbAssignP _ _ Q).relayStepWith (G.relayOf Q)
            Q p'
          ((A.absorbAssignP _ _ Q).relayOut (G.relayOf Q))) sp H₁) f)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
-- TODO(unbundle-M4): the shapes of the two sides of `seAlgKF_absorbAssign_eq_withStep`, stated with
-- the same instance arguments so that callers can transport along them
/-- **The shapes of the two sides of `seAlgKF_absorbAssign_eq_withStep` are equal**
(`absorbAssignS_eq_of_relayOf`). -/
theorem seAlgKF_absorbAssign_toShape_eq
    {Y Req Resp O Xs Ys : Type} [Fintype Y] [DecidableEq Y] [AddGroup Ys] [Fintype Ys]
    [DecidableEq Ys] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    [Inhabited Req] [AddGroup Y] [Nonempty Y]
    {shA : AlgShape Xq Y Req Resp} {A : AdaptiveIAlg shA O}
    {G : AssignRelay Xq Y Req Resp (MUR ⊕ R) (MUResponse B ⊕ M.Response b) Xs Ys} {Q : ℕ}
    {p' : (Req × Fin (Q + 1)) × (Xq → Option Y) → OracleProg ((Xq ⊕ Xs) ⊕ (MUR ⊕ R))
      ((Y ⊕ Ys) ⊕ Option (MUResponse B ⊕ M.Response b))
      (Option (AssignRelay.RespD Xq Y Resp (MUR ⊕ R) (MUResponse B ⊕ M.Response b)))}
    {Y₁ : Type} [Fintype Y₁] [DecidableEq Y₁] [AddGroup Y₁] {sp : Y ≃+ Y₁ × XOut k e}
    {H₁ : Xq → Y₁} {f : O × (Xq → Option Y) → Frg × X₀}
    {G' : AssignRelay Xq Y Req Resp (MUR ⊕ R) (MUResponse B ⊕ M.Response b) Xs Ys}
    (hG : G'.relayOf Q = (G.relayOf Q).withProg p') :
    (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Qk
        (((A.absorbAssign G' Q).restrictAt sp H₁).mapOut f)).toShape =
      ((seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Qk
        (((A.absorbAssign G Q).restrictAt sp H₁).mapOut f)).withStep
        (AdaptiveIAlg.absorbTabStep (((A.absorbAssign G Q).restrictAt sp H₁).mapOut f)
          (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Qk)
          ((A.absorbAssign G Q).restrictStep
            ((A.absorbAssignP _ _ Q).relayStepWith (G.relayOf Q) Q p'
              ((A.absorbAssignP _ _ Q).relayOut (G.relayOf Q))) sp H₁))).toShape :=
  congrArg (fun s : AlgShape Xq Y (MUR ⊕ R) (MUResponse B ⊕ M.Response b) =>
    seAlgKFS (Stmt := Stmt) (M := M) (B := B) (s.restrictAtS Y₁ (XOut k e)))
    (AdaptiveIAlg.absorbAssignS_eq_of_relayOf (shA := shA) hG)

end AbsorbAssignKF

end RingSignature.KeyFree

end GordieHowe
