-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.CompressedSimReq
public import GordieHowe.Model.Quantum.Interactive.ConstReg
public import GordieHowe.Model.Quantum.Interactive.AbsorbBudget
public import GordieHowe.Model.QROM.ExpandAdv
public import GordieHowe.Model.QROM.CoherentBridgeCore

@[expose] public section

/-!
# The bridge from an extraction run with an outer challenger to a query algorithm with request points

`ExtBridge` is the statement of the bridge between the extraction runs of the
simulation-extraction games and the query algorithms with request points
(`GordieHowe/Model/Quantum/Interactive/CompressedSimReq.lean`); `extBridge`
(`GordieHowe/Model/Quantum/Interactive/ReqBridgeExt.lean`) proves it. The file also proves that the adversary absorbed with a table has the law of the adversary
absorbed through the relay at the table's replies (`toOuterMeasure_outLaw_absorbTab`).

- `TwoRelay`: a relay of an adversary's requests to an inner challenger (`route₁`, `answer₁`), with
  outer requests (`outer r = some q`) answered from an outer reply (`answer₂`). `TwoRelay.base`:
  every outer request answered by the reply to `none`; `TwoRelay.atC b`: request number `c` with
  outer request `q` answered by `b c q`.
- `ReqQueryAlg.instLog`: the instance with replies that read the earlier requests
  (`requestsBefore`); `ReqQueryAlg.inst_eq_instLog`: replies that do not read them give `inst`.
- `AdaptiveIAlg.absorbTab A F tab`: `A` absorbed through `F.base` with a table of outer replies
  (`AdaptiveIAlg.withConst`). The table is a classical register written once, at initialization,
  and read only by the controlled permutations of `stepTab`: after slot `j`, a logged outer request
  is answered from the table at the count of the earlier outer requests (`afterPermTab`, keyed on
  the absorbed copy of the logs). The table enters only the initial state, so the run's types do
  not depend on it. Its shape is `AlgShape.absorbTabS` (`absorbTab_toShape`).
- `AdaptiveIAlg.toOuterMeasure_outLaw_absorbTab`: when the table at the count of the earlier outer
  requests is `b` at the count of the earlier requests, the law of the composed registers of
  `absorbTab` against every challenger, the table register dropped, is that of `A.absorb (F.atC b)`;
  the cases of a relay whose every request is outer (`…_of_forall`, `b := tabAt tab`) and of a
  table that ignores the count (`…_const`).
- `extRun`: the expanded purified extraction run of `A.absorbTab F tab` against `C₁`.
  `bridgeAlg`: the query algorithm with request points of the bridge, an explicit definition: the
  run at the empty table, with at the step after slot `j` (`answerSlot`) a request point whose
  request is the outer request of the logged request of slot `j` and whose reply replaces the
  reply to `none` (`answerDelta`), and the dummy `d₂` elsewhere; `bridgeAlg_req`: its requests are
  outer requests or `d₂`.
- `ExtBridge`: for every table `tab`, `simLaw` of `extRun` at `tab` is `simLaw` of `bridgeAlg` at the
  table's replies at the count of the earlier outer requests (`countND`), for outer requests other
  than the dummy.
-/

namespace GordieHowe.Quantum

namespace ReqQueryAlg

variable {X Y Req Resp O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Req] [Fintype Req] {t : ℕ} (G : ReqQueryAlg X Y Req Resp t O)

/-- **The request point of step `k` with replies that read the earlier requests**: as `reqPerm`,
with the reply `a k (requestsBefore lg k) r` to the request `r`, `requestsBefore lg k` the requests
logged before step `k`. -/
def reqPermLog (a : ℕ → List Req → Req → Option Resp) (k : Fin (t + 1)) :
    Equiv.Perm (G.W × LogReg Req (t + 1)) where
  toFun p := (G.write k (a k (requestsBefore p.2 k) (G.req k p.1)) p.1,
    Function.update p.2 k (Equiv.swap none (some (G.req k p.1)) (p.2 k)))
  invFun p := ((G.write k (a k (requestsBefore p.2 k) (G.req k p.1))).symm p.1,
    Function.update p.2 k (Equiv.swap none (some (G.req k p.1)) (p.2 k)))
  left_inv p := by
    obtain ⟨w, lg⟩ := p
    have hrb : ∀ x, requestsBefore (Function.update lg k x) k = requestsBefore lg k := fun x =>
      requestsBefore_congr fun k' hk' => Function.update_of_ne (fun h => by subst h; simp at hk') _ _
    simp only [hrb, G.req_write, Equiv.symm_apply_apply, Function.update_self, Equiv.swap_apply_self,
      Function.update_idem, Function.update_eq_self]
  right_inv p := by
    obtain ⟨w, lg⟩ := p
    have hrb : ∀ x, requestsBefore (Function.update lg k x) k = requestsBefore lg k := fun x =>
      requestsBefore_congr fun k' hk' => Function.update_of_ne (fun h => by subst h; simp at hk') _ _
    simp only [hrb, G.req_write_symm, Equiv.apply_symm_apply, Function.update_self,
      Equiv.swap_apply_self, Function.update_idem, Function.update_eq_self]

/-- Step `k` of the instance with replies that read the earlier requests. -/
noncomputable def instStepLog (a : ℕ → List Req → Req → Option Resp) (k : Fin (t + 1)) :
    QState (QueryReg (G.W × LogReg Req (t + 1)) 1 X Y) ≃ₗᵢ[ℂ]
      QState (QueryReg (G.W × LogReg Req (t + 1)) 1 X Y) :=
  (permOp ((G.reqPermLog a k).prodCongr (Equiv.refl _))).trans
    ((relabel G.logSplit).trans ((controlled fun _ => G.step k).trans (relabel G.logSplit.symm)))

/-- **The query algorithm with replies that read the earlier requests**: as `inst`, the reply at
the request point of step `k` to the request `r` being `a k (requestsBefore lg k) r`. -/
noncomputable def instLog (a : ℕ → List Req → Req → Option Resp) : QueryAlg X Y t O where
  W := G.W × LogReg Req (t + 1)
  init := relabel G.logSplit.symm (tensorKet G.init (fun _ => none))
  norm_init := by rw [LinearIsometryEquiv.norm_map, norm_tensorKet, G.norm_init]
  step k := G.instStepLog a k
  out p := G.out p.1

/-- **Replies that do not read the earlier requests**: `instLog` at `a` that ignores them is
`inst`. -/
theorem inst_eq_instLog (a : ℕ → Req → Option Resp) : G.inst a = G.instLog fun k _ r => a k r :=
  rfl

/-- The number of the requests of a list other than `d`. -/
def countND (d : Req) (prev : List Req) : ℕ :=
  (prev.filter fun r => r ≠ d).length

end ReqQueryAlg

/-- **A relay of requests to an inner challenger, with outer requests**: request number `c` with
request `r` is sent to the inner challenger as `route₁ c r`; a request with an outer request
`outer r = some q` is answered by `answer₂ c r b` from the outer reply `b`, the others by
`answer₁ c r a` from the inner reply `a`. -/
structure TwoRelay (Req Resp Req₁ Resp₁ Req₂ Resp₂ : Type) where
  /-- The inner request. -/
  route₁ : ℕ → Req → Req₁
  /-- The reply to a request without an outer request, from the inner reply. -/
  answer₁ : ℕ → Req → Option Resp₁ → Option Resp
  /-- The outer request of request number `c`, if any. -/
  outer : ℕ → Req → Option Req₂
  /-- The reply to request number `c` with an outer request, from the outer reply. -/
  answer₂ : ℕ → Req → Option Resp₂ → Option Resp

namespace TwoRelay

variable {Req Resp Req₁ Resp₁ Req₂ Resp₂ : Type} (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)

/-- **The relay with every outer request answered by the reply to `none`.** -/
def base : SideRelay Req Resp Req₁ Resp₁ where
  route := F.route₁
  answer c r a := match F.outer c r with
    | some _ => F.answer₂ c r none
    | none => F.answer₁ c r a

/-- **The relay with the outer replies `b`** at the request count: request number `c` with an
outer request `q` answered from `b c q`. -/
def atC (b : ℕ → Req₂ → Option Resp₂) : SideRelay Req Resp Req₁ Resp₁ where
  route := F.route₁
  answer c r a := match F.outer c r with
    | some q => F.answer₂ c r (b c q)
    | none => F.answer₁ c r a

/-- **The reply to `r`'s outer request from the outer reply `x` in place of the reply to `none`**:
the swap of `none` and `answer₂ c r none` (which undoes the writing of the reply to `none` into a
blank register), then the swap of `none` and `answer₂ c r x`. -/
def replyFix [DecidableEq Resp] (c : ℕ) (r : Req) (x : Option Resp₂) : Equiv.Perm (Option Resp) :=
  (Equiv.swap none (F.answer₂ c r none)).trans (Equiv.swap none (F.answer₂ c r x))

end TwoRelay

open GordieHowe.QROM

/-! ### The adversary absorbed with a table of outer replies -/

/-- **A permutation controlled by a classical register**: `π t` on the first factor at `t`. -/
def ctrlPerm {D T : Type*} (π : T → Equiv.Perm D) : Equiv.Perm (D × T) where
  toFun p := (π p.2 p.1, p.2)
  invFun p := ((π p.2).symm p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp

namespace AdaptiveIAlg

variable {X Y Req Resp O Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)

/-- **A table of outer replies**: for each count of outer requests and outer request, a reply. -/
abbrev OuterTab (Req₂ Resp₂ : Type) : Type := Fin A.slots → Req₂ → Option Resp₂

instance OuterTab.instFintype : Fintype (A.OuterTab Req₂ Resp₂) := Pi.instFintype

instance OuterTab.instDecidableEq : DecidableEq (A.OuterTab Req₂ Resp₂) :=
  fun f g => Fintype.decidablePiFintype f g

/-- The table's reply at the count `c` (none from the count `slots` on). -/
def tabAt (tab : A.OuterTab Req₂ Resp₂) (c : ℕ) (q : Req₂) : Option Resp₂ :=
  if h : c < A.slots then tab ⟨c, h⟩ q else none

/-- The number of outer requests before slot `j` in a log register: the earlier requests with an
outer request at their request number. -/
def outerCount (lg : LogReg Req A.slots) (j : Fin A.slots) : ℕ :=
  (((requestsBefore lg j).zipIdx).filter fun p => (F.outer p.2 p.1).isSome).length

/-- **The reply of slot `j` from the table** `t`, at the logs `lg`, for the request `r` with the
stored inner reply `a`: from the table at the count of the earlier outer requests for an outer
request, from the inner reply otherwise. -/
def tabAnswer (t : A.OuterTab Req₂ Resp₂) (lg : LogReg Req A.slots) (j : Fin A.slots) (r : Req)
    (a : Option Resp₁) : Option Resp :=
  match F.outer (A.reqCount lg j) r with
  | some q => F.answer₂ (A.reqCount lg j) r (A.tabAt t (A.outerCount F lg j) q)
  | none => F.answer₁ (A.reqCount lg j) r a

/-- **Writing the reply of slot `j` from the table** `t` (`answerPerm` with `tabAnswer`). -/
def answerPermTab (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots) :
    Equiv.Perm (DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :=
  Function.Involutive.toPerm
    (fun d => match d.1.1.logs j with
      | none => d
      | some r => ((⟨d.1.1.work, d.1.1.request,
          Equiv.swap none (A.tabAnswer F t d.1.1.logs j r (d.1.1.store j)) d.1.1.response,
          d.1.1.logs, d.1.1.store⟩, d.1.2), d.2))
    fun d => by
      rcases h : d.1.1.logs j with _ | r
      · simp [h]
      · simp [h]

/-- **After slot `j`, with the table** `t` (`afterPerm` with `answerPermTab`). -/
def afterPermTab (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots) :
    Equiv.Perm (DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :=
  ((A.storePerm j).trans (A.answerPermTab F t j)).trans (A.clearPerm F.base j)

/-- **With a table matching `b` on the logged outer requests, the table's handling of slot `j` is
the relay's at `b`**: `afterPermTab t j = afterPerm (F.atC b) j` when `t` at the count of the
earlier outer requests is `b` at the count of the earlier requests. -/
theorem afterPermTab_eq {t : A.OuterTab Req₂ Resp₂} {b : ℕ → Req₂ → Option Resp₂}
    (hb : ∀ (lg : LogReg Req A.slots) (j : Fin A.slots) r q, lg j = some r → F.outer (A.reqCount lg j) r = some q →
      A.tabAt t (A.outerCount F lg j) q = b (A.reqCount lg j) q) (j : Fin A.slots) :
    A.afterPermTab F t j = A.afterPerm (F.atC b) j := by
  have h : A.answerPermTab F t j = A.answerPerm (F.atC b) j := by
    ext d : 1
    unfold answerPermTab answerPerm AlgShape.answerPerm
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    rcases hl : d.1.1.logs j with _ | r
    · rfl
    · dsimp only
      congr 4
      unfold tabAnswer
      simp only [TwoRelay.atC]
      rcases hq : F.outer (A.reqCount d.1.1.logs j) r with _ | q
      · rfl
      · simp only
        rw [hb _ j r q hl hq]
  unfold afterPermTab
  rw [AdaptiveIAlg.afterPerm_def]
  rw [h]
  rfl

/-- **Before step `k`, the table's handling of slot `k - 1`**, on the absorbed registers with the
table register (`ctrlPerm`); the identity at `k = 0` and after the last slot. -/
def afterAtTab (k : ℕ) :
    Equiv.Perm (DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :=
  if h : 0 < k ∧ k - 1 < A.slots then
    ((A.absorb F.base).constSplit (A.OuterTab Req₂ Resp₂)).symm.permCongr
      (ctrlPerm fun t => A.afterPermTab F t ⟨k - 1, h.2⟩)
  else Equiv.refl _

/-- A permutation of the absorbed registers, with the identity on the table register. -/
def tabLift (π : Equiv.Perm (DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁)) :
    Equiv.Perm (DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :=
  ((A.absorb F.base).constSplit (A.OuterTab Req₂ Resp₂)).symm.permCongr
    (π.prodCongr (Equiv.refl _))

/-- **The step `k` of the adversary absorbed with a table**: the absorbed step through `F.base`,
with the handling of slot `k - 1` read from the table register (`afterAtTab`). -/
@[irreducible, no_expose] def stepTab (k : StepIdx A.slots A.post) :
    KrausMap (A.absorb F.base).R
      (DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁)
      (DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :=
  (KrausMap.ofPerm (A.tabLift F (A.setAt F.base k))).comp
    ((((A.liftedStep (Resp' := Resp₁) k).tensorId (A.OuterTab Req₂ Resp₂)).reindex
      ((A.absorb F.base).constSplit (A.OuterTab Req₂ Resp₂)).symm).comp
      (KrausMap.ofPerm (A.afterAtTab F k)))

theorem stepTab_eq (k : StepIdx A.slots A.post) :
    A.stepTab F k = (KrausMap.ofPerm (A.tabLift F (A.setAt F.base k))).comp
      ((((A.liftedStep (Resp' := Resp₁) k).tensorId (A.OuterTab Req₂ Resp₂)).reindex
        ((A.absorb F.base).constSplit (A.OuterTab Req₂ Resp₂)).symm).comp
        (KrausMap.ofPerm (A.afterAtTab F k))) := by
  unfold stepTab
  rfl

omit [Inhabited Req₁] in
variable (Req₂ Resp₂) in
/-- **The shape of the adversary absorbed with a table** (`absorbTab`): the absorbed shape
(`AlgShape.absorbS`) with the table register (`AlgShape.withConstS`). -/
@[reducible] def _root_.GordieHowe.Quantum.AlgShape.absorbTabS (s : AlgShape X Y Req Resp) :
    AlgShape X Y Req₁ Resp₁ :=
  (s.absorbS (Req' := Req₁) (Resp' := Resp₁)).withConstS (Fin s.slots → Req₂ → Option Resp₂)

/-- **The adversary absorbed with a table of outer replies** `tab`: `A` absorbed through `F.base`
with a table register (`withConst`), a classical register written once, at initialization, and
read only by the controlled permutations of `stepTab`, which answer each logged outer request from
the table at the count of the earlier outer requests. The table enters only the initial state.

Running time: that of `A` absorbed through `F.base` (one relay program per request), the table
register written at initialization, and one controlled permutation of `stepTab` per logged outer
request. This running time is argued here, not proved in Lean. -/
abbrev absorbTab (tab : A.OuterTab Req₂ Resp₂) :
    AdaptiveIAlg (shA.absorbTabS Req₂ Resp₂ (Req₁ := Req₁) (Resp₁ := Resp₁)) O :=
  (A.absorb F.base).withConst (A.OuterTab Req₂ Resp₂) tab (A.stepTab F)

theorem absorbTab_toShape (tab : A.OuterTab Req₂ Resp₂) :
    (A.absorbTab F tab).toShape = A.toShape.absorbTabS Req₂ Resp₂ :=
  rfl

/-! #### The table register against the relay at the table's replies -/

section Real

variable {tab : A.OuterTab Req₂ Resp₂} {b : ℕ → Req₂ → Option Resp₂}

theorem tabLift_insD (π : Equiv.Perm (DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁))
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    A.tabLift F π ((A.absorb F.base).insD (A.OuterTab Req₂ Resp₂) tab d) =
      (A.absorb F.base).insD (A.OuterTab Req₂ Resp₂) tab (π d) :=
  rfl

theorem afterAtTab_insD
    (hb : ∀ (lg : LogReg Req A.slots) (j : Fin A.slots) r q, lg j = some r → F.outer (A.reqCount lg j) r = some q →
      A.tabAt tab (A.outerCount F lg j) q = b (A.reqCount lg j) q) (k : ℕ)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    A.afterAtTab F k ((A.absorb F.base).insD (A.OuterTab Req₂ Resp₂) tab d) =
      (A.absorb F.base).insD (A.OuterTab Req₂ Resp₂) tab (A.afterAt (F.atC b) k d) := by
  unfold afterAtTab
  rw [afterAt_def]
  split
  · rename_i h
    rw [← afterPermTab_eq A F hb]
    rfl
  · rfl

/-- **The steps of the adversary absorbed with a table are intertwined with those of the adversary
absorbed through the relay at `b`**, along the placement at the table, when the table at the count
of the earlier outer requests is `b` at the count of the earlier requests (`hb`). -/
theorem stepTab_intertwines
    (hb : ∀ (lg : LogReg Req A.slots) (j : Fin A.slots) r q, lg j = some r → F.outer (A.reqCount lg j) r = some q →
      A.tabAt tab (A.outerCount F lg j) q = b (A.reqCount lg j) q)
    (k : StepIdx A.slots A.post) (r : (A.absorb F.base).R) :
    Intertwines ((A.absorb F.base).insD (A.OuterTab Req₂ Resp₂) tab) ((A.stepTab F k).op r)
      (((A.absorb (F.atC b)).step k).op r) := by
  have hL : Intertwines ((A.absorb F.base).insD (A.OuterTab Req₂ Resp₂) tab)
      ((((A.liftedStep (Resp' := Resp₁) k).tensorId (A.OuterTab Req₂ Resp₂)).reindex
        ((A.absorb F.base).constSplit (A.OuterTab Req₂ Resp₂)).symm).op r.1.2)
      ((A.liftedStep (Resp' := Resp₁) (Req' := Req₁) k).op r.1.2) :=
    (Intertwines.kron_one_ket _ tab).submatrix (Equiv.refl _) (Equiv.refl _)
      ((A.absorb F.base).constSplit (A.OuterTab Req₂ Resp₂)).symm.symm
      ((A.absorb F.base).constSplit (A.OuterTab Req₂ Resp₂)).symm.symm (fun _ => rfl)
      (fun _ => rfl)
  rw [stepTab_eq, show (A.absorb (F.atC b)).step k = _ from A.absorbStep_eq (F.atC b) k]
  exact (Intertwines.ofPerm (fun d => tabLift_insD A F _ d) r.2).mul
    (hL.mul (Intertwines.ofPerm (fun d => afterAtTab_insD A F hb k d) r.1.1))

theorem withStep_absorb :
    (A.absorb F.base).withStep (A.absorb (F.atC b)).step = A.absorb (F.atC b) :=
  rfl

/-- **(c) The adversary absorbed with a table has the law of the adversary absorbed through the
relay at the table's replies**: against every challenger `C` and on every event `P` of the latter's
composed registers (read without the table register, `forgetCW`), when the table at the count of
the earlier outer requests is `b` at the count of the earlier requests (`hb`). -/
theorem toOuterMeasure_outLaw_absorbTab [Nonempty X] [AddGroup Y] [Nonempty Y]
    (hb : ∀ (lg : LogReg Req A.slots) (j : Fin A.slots) r q, lg j = some r → F.outer (A.reqCount lg j) r = some q →
      A.tabAt tab (A.outerCount F lg j) q = b (A.reqCount lg j) q)
    (C : Challenger X Y Req₁ Resp₁) (H : X → Y)
    (P : (A.absorb (F.atC b)).toKindAlg.CW C → Prop) :
    (((A.absorbTab F tab).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P ((A.absorb F.base).forgetCWTo tab (A.stepTab F) C
          (A.absorb (F.atC b)).step v)} =
      (((A.absorb (F.atC b)).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v} :=
  (A.absorb F.base).toOuterMeasure_outLaw_withConst_withStep tab (A.stepTab F) C
    (A.absorb (F.atC b)).step (stepTab_intertwines A F hb) H P

-- TODO(unbundle-M4): one-step instance at the adversary (instance search exceeds its size limit
-- on the game register of `toKindAlg`); goes with the toKindAlg unification
/-- Decidable equality of the game registers of the adversary absorbed with a table. -/
instance instDecidableEqGTab (t : A.OuterTab Req₂ Resp₂) :
    DecidableEq (A.absorbTab F t).toKindAlg.G :=
  @instDecidableEqGameReg _ _ _ _ _ _ _ inferInstance inferInstance inferInstance inferInstance
    inferInstance

-- TODO(unbundle-M4): one-step instance at the adversary (instance search exceeds its size limit
-- on the registers with the counter)
/-- Decidable equality of the registers with the counter of the adversary absorbed with a
table. -/
instance instDecidableEqCRegTab (t : A.OuterTab Req₂ Resp₂) :
    DecidableEq (A.absorbTab F t).CReg :=
  @DReg.instDecidableEq _ _ _ _ _ _ (@instDecidableEqProd _ _ inferInstance inferInstance) _ _ _ _

/-- **Absorbing with a table keeps the budget**, when the table matches the relay at `b` on the
logged outer requests (`hb`) and the inner requests are injective (`hinj`): the mixed game is that
of the adversary absorbed through the relay at `b`, placed at the table (`mgRun_withConst_withStep`),
which keeps the trace (`absorb_withinBudget`). -/
theorem absorbTab_withinBudget [Nonempty X] [AddGroup Y] [Nonempty Y]
    (hb : ∀ (lg : LogReg Req A.slots) (j : Fin A.slots) r q, lg j = some r → F.outer (A.reqCount lg j) r = some q →
      A.tabAt tab (A.outerCount F lg j) q = b (A.reqCount lg j) q)
    (hinj : ∀ c, Function.Injective (F.route₁ c)) (hA : A.WithinBudget) :
    (A.absorbTab F tab).WithinBudget := by
  refine ((withinBudget_iff (A.absorbTab F tab)).2 fun C' H => ?_)
  rw [AdaptiveIAlg.outLaw_compose_none_eq, ENNReal.ofReal_eq_zero, sub_nonpos]
  have h : ∀ c', ((A.absorbTab F tab).toKindAlg.mgRun C'.toPureEnv (H, c') true).trace.re = 1 := by
    intro c'
    change ((A.absorbTab F tab).toKindAlg.mgRun C'.toPureEnv (H, c') true).trace.re = 1
    rw [(A.absorb F.base).mgRun_withConst_withStep tab (A.stepTab F) C'.toPureEnv
      (H, c') (A.absorb (F.atC b)).step (stepTab_intertwines A F hb)]
    rw [re_trace_embed ((A.absorb F.base).insGTo_injective tab (A.stepTab F)
      (A.absorb (F.atC b)).step tab)]
    exact (congrArg Complex.re ((A.absorb_withinBudget (F.atC b) hinj hA).trace_mgRun_eq_one
      C'.toPureEnv (H, c'))).trans Complex.one_re
  simp only [h, mul_one]
  have hsum : ∑ c', C'.coins c' = 1 := by
    rw [← tsum_fintype (L := .unconditional _), PMF.tsum_coe]
  rw [← ENNReal.toReal_sum fun c _ => PMF.apply_ne_top _ c, hsum, ENNReal.toReal_one]

/-- The composed registers of an absorbed adversary, named without the relay: those of the
absorbed shape with its counter (`AlgShape.CntW`). -/
abbrev AbsCW (C : Challenger X Y Req₁ Resp₁) : Type :=
  CWork (shA.absorbS (Req' := Req₁) (Resp' := Resp₁)).CntW A.width X Y Req₁ Resp₁ A.slots C.q
    C.Coins

/-- **(c) on the composed registers named without the relay** (`AbsCW`). -/
theorem toOuterMeasure_outLaw_absorbTab' [Nonempty X] [AddGroup Y] [Nonempty Y]
    (hb : ∀ (lg : LogReg Req A.slots) (j : Fin A.slots) r q, lg j = some r → F.outer (A.reqCount lg j) r = some q →
      A.tabAt tab (A.outerCount F lg j) q = b (A.reqCount lg j) q)
    (C : Challenger X Y Req₁ Resp₁) (H : X → Y) (P : A.AbsCW C → Prop) :
    (((A.absorbTab F tab).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P ((A.absorb F.base).forgetCWTo tab (A.stepTab F) C
          (A.absorb (F.atC b)).step v)} =
      (((A.absorb (F.atC b)).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v} :=
  toOuterMeasure_outLaw_absorbTab A F hb C H P

theorem outerCount_lt (lg : LogReg Req A.slots) (j : Fin A.slots) : A.outerCount F lg j < A.slots :=
  lt_of_le_of_lt ((List.length_filter_le _ _).trans
    ((List.length_zipIdx (l := requestsBefore lg j)).trans_le (length_requestsBefore_le lg j))) j.2

/-- **Every request outer**: the count of the earlier outer requests is the count of the earlier
requests, so the table matches the relay at its own replies (`b := tabAt tab`). -/
theorem tabAt_outerCount_of_forall (hall : ∀ c r, (F.outer c r).isSome)
    (lg : LogReg Req A.slots) (j : Fin A.slots) (q : Req₂) :
    A.tabAt tab (A.outerCount F lg j) q = A.tabAt tab (A.reqCount lg j) q := by
  unfold outerCount
  rw [List.filter_eq_self.2 fun p _ => hall p.2 p.1, List.length_zipIdx]

/-- **A table that ignores the count** matches the relay at its replies (`b := fun _ => g`). -/
theorem tabAt_outerCount_const (g : Req₂ → Option Resp₂) (lg : LogReg Req A.slots)
    (j : Fin A.slots) (q : Req₂) :
    A.tabAt (fun _ => g) (A.outerCount F lg j) q = g q := by
  unfold tabAt
  rw [dite_cond_eq_true (eq_true (outerCount_lt A F lg j))]

/-- **(c) for a relay whose every request is outer**: the old relay answers request number `c`
from the table at `c` (`F.atC (tabAt tab)`). -/
theorem toOuterMeasure_outLaw_absorbTab_of_forall [Nonempty X] [AddGroup Y] [Nonempty Y]
    (hall : ∀ c r, (F.outer c r).isSome) (C : Challenger X Y Req₁ Resp₁) (H : X → Y)
    (P : (A.absorb (F.atC (A.tabAt tab))).toKindAlg.CW C → Prop) :
    (((A.absorbTab F tab).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P ((A.absorb F.base).forgetCWTo tab (A.stepTab F) C
          (A.absorb (F.atC (A.tabAt tab))).step v)} =
      (((A.absorb (F.atC (A.tabAt tab))).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v} :=
  toOuterMeasure_outLaw_absorbTab A F (fun lg j _ q _ _ => tabAt_outerCount_of_forall A F hall lg j q)
    C H P

/-- **(c) for a table that ignores the count**: the old relay answers every outer request `q`
from `g q` (`F.atC fun _ => g`). -/
theorem toOuterMeasure_outLaw_absorbTab_const [Nonempty X] [AddGroup Y] [Nonempty Y]
    (g : Req₂ → Option Resp₂) (C : Challenger X Y Req₁ Resp₁) (H : X → Y)
    (P : (A.absorb (F.atC fun _ => g)).toKindAlg.CW C → Prop) :
    (((A.absorbTab F fun _ => g).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P ((A.absorb F.base).forgetCWTo (fun _ => g) (A.stepTab F) C
          (A.absorb (F.atC fun _ => g)).step v)} =
      (((A.absorb (F.atC fun _ => g)).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v} :=
  toOuterMeasure_outLaw_absorbTab A F (fun lg j _ q _ _ => tabAt_outerCount_const A F g lg j q)
    C H P

end Real

end AdaptiveIAlg

/-! ### The bridge -/

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]

/-- **The composed registers of an extraction run** of the adversary `A` absorbed with a table
through a relay to `C₁`'s interface, named without the table and the relay: the run reads its
output with the table register dropped (`extOut`). -/
abbrev ExtReg {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
    (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁) (Req₂ Resp₂ : Type) : Type :=
  CWork (shA.absorbS (Req' := Req₁) (Resp' := Resp₁)).CntW
    A.width (Bits m) (BitStr I J) Req₁ Resp₁ A.slots C₁.q C₁.Coins

/-- The composed registers of the adversary absorbed with a table, the table register dropped. -/
def dropTabCW {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
    (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
    (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (tab : A.OuterTab Req₂ Resp₂)
    (v : (A.absorbTab F tab).toTPKindAlg.CW C₁) : ExtReg A C₁ Req₂ Resp₂ :=
  ⟨((AlgShape.CntW.mk v.adv.1.1.work.1 v.adv.1.1.cnt, v.adv.1.2), v.adv.2), v.chal⟩

/-- The composed registers of the adversary absorbed with a table, the table register set to
`tab`. -/
def insertTab {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
    (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
    (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (tab : A.OuterTab Req₂ Resp₂)
    (c : ExtReg A C₁ Req₂ Resp₂) : (A.absorbTab F tab).toTPKindAlg.CW C₁ :=
  ⟨((AlgShape.CntW.mk (c.adv.1.1.work, tab) c.adv.1.1.cnt, c.adv.1.2), c.adv.2), c.chal⟩

/-- **The output of an extraction run**: the composed registers with the table register dropped,
the default `d₀` on halted branches. -/
def extOut {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
    (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
    (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₀ : ExtReg A C₁ Req₂ Resp₂)
    (tab : A.OuterTab Req₂ Resp₂) :
    Option ((A.absorbTab F tab).toTPKindAlg.CW C₁) → ExtReg A C₁ Req₂ Resp₂
  | none => d₀
  | some v => dropTabCW A C₁ F tab v

/-- **The expanded purified extraction run at the table `tab`**: the adversary absorbed with the
table (`AdaptiveIAlg.absorbTab`), composed with `C₁`, purified (`Alg.toQueryAlgCoh`), its output
read without the table register and with the default `d₀` on halted branches (`extOut`), and
expanded by `E` with `kq` queries. The table enters only the initial state.

Running time: that of the adversary absorbed with the table (`AdaptiveIAlg.absorbTab`) composed
with `C₁`, its coherent purification, the output map `extOut`, and the expansion by `E` with `kq`
queries. This running time is argued here, not proved in Lean. -/
noncomputable abbrev extRun (e : BitStr I J ≃ B)
    {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
    (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
    (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂))
    (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂) (tab : A.OuterTab Req₂ Resp₂) :=
  expandAdv e E kq
    ((((A.absorbTab F tab).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh).mapOut
      (extOut A C₁ F d₀ tab))

/-- The slot whose reply the adversary's step at oracle step `k` of the run reads: `j` at
`k = (j + 1) · (q + width)`, `q` the inner challenger's queries per request. -/
def answerSlot {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
    (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁) (k : ℕ) : Option (Fin A.slots) :=
  if h : (C₁.q + A.width) ∣ k ∧ 0 < k / (C₁.q + A.width) ∧ k / (C₁.q + A.width) - 1 < A.slots then
    some ⟨k / (C₁.q + A.width) - 1, h.2.2⟩
  else none

/-- The empty table. -/
def tab₀ {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O) : A.OuterTab Req₂ Resp₂ :=
  fun _ _ => none

variable (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)
  (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)

/-- The registers of the adversary absorbed with a table. -/
abbrev AbsD {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O) (Req₁ Resp₁ Req₂ Resp₂ : Type)
    [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] : Type :=
  DReg (AbsorbedWork A.W Req Resp Resp₁ A.slots × A.OuterTab Req₂ Resp₂) A.width (Bits m)
    (BitStr I J) Req₁ Resp₁

/-- **The reply `x` to the outer request of slot `j`'s logged request**, on the absorbed registers
with the table, in place of the reply to `none` (`TwoRelay.replyFix`, at the count of the earlier
requests); the identity when slot `j` logged no outer request. -/
def absOuterSwap (j : Fin A.slots) (x : Option Resp₂) :
    Equiv.Perm (AbsD A Req₁ Resp₁ Req₂ Resp₂) where
  toFun d := match d.1.1.1.logs j with
    | none => d
    | some r => (match F.outer (A.reqCount d.1.1.1.logs j) r with
      | none => d
      | some _ => (((⟨d.1.1.1.work, d.1.1.1.request,
          F.replyFix (A.reqCount d.1.1.1.logs j) r x d.1.1.1.response, d.1.1.1.logs,
          d.1.1.1.store⟩, d.1.1.2), d.1.2), d.2))
  invFun d := match d.1.1.1.logs j with
    | none => d
    | some r => (match F.outer (A.reqCount d.1.1.1.logs j) r with
      | none => d
      | some _ => (((⟨d.1.1.1.work, d.1.1.1.request,
          (F.replyFix (A.reqCount d.1.1.1.logs j) r x).symm d.1.1.1.response, d.1.1.1.logs,
          d.1.1.1.store⟩, d.1.1.2), d.1.2), d.2))
  left_inv d := by
    obtain ⟨⟨⟨⟨w, r, rs, lg, st⟩, t⟩, mr⟩, qs⟩ := d
    rcases hl : lg j with _ | r'
    · simp [hl]
    · rcases h : F.outer (A.reqCount lg j) r' with _ | q
      · simp [hl, h]
      · simp [hl, h]
  right_inv d := by
    obtain ⟨⟨⟨⟨w, r, rs, lg, st⟩, t⟩, mr⟩, qs⟩ := d
    rcases hl : lg j with _ | r'
    · simp [hl]
    · rcases h : F.outer (A.reqCount lg j) r' with _ | q
      · simp [hl, h]
      · simp [hl, h]

/-- **The request point of slot `j`** on the absorbed registers with the table: undo the
handling of slot `j`'s reply from the table (`afterAtTab`), write the reply `x` to the outer
request in place of the reply to `none`, and redo it. -/
def answerDelta (j : Fin A.slots) (x : Option Resp₂) :
    Equiv.Perm (AbsD A Req₁ Resp₁ Req₂ Resp₂) :=
  (A.afterAtTab F (j + 1)).trans ((absOuterSwap A F j x).trans (A.afterAtTab F (j + 1)).symm)

/-- The registers of the adversary absorbed with a table, of a basis state of the run's work
register. -/
def absRegs (w : (extRun e A C₁ F E kq d₀ (tab₀ A)).W) : AbsD A Req₁ Resp₁ Req₂ Resp₂ :=
  ((w.1.1.1.1.adv.1.1.1, w.1.1.1.1.adv.1.2), w.1.1.1.1.adv.2)

/-- A permutation of the registers of the adversary absorbed with a table, on the run's work
register. -/
def liftAbs (π : Equiv.Perm (AbsD A Req₁ Resp₁ Req₂ Resp₂)) :
    Equiv.Perm (extRun e A C₁ F E kq d₀ (tab₀ A)).W where
  toFun w :=
    let d := π (absRegs e A C₁ F E kq d₀ w)
    ((((⟨(((d.1.1, w.1.1.1.1.adv.1.1.2), d.1.2), d.2), w.1.1.1.1.chal⟩, w.1.1.1.2), w.1.1.2), w.1.2),
      w.2)
  invFun w :=
    let d := π.symm (absRegs e A C₁ F E kq d₀ w)
    ((((⟨(((d.1.1, w.1.1.1.1.adv.1.1.2), d.1.2), d.2), w.1.1.1.1.chal⟩, w.1.1.1.2), w.1.1.2), w.1.2),
      w.2)
  left_inv w := by
    simp only [absRegs, Prod.mk.eta, Equiv.symm_apply_apply]
    rfl
  right_inv w := by
    simp only [absRegs, Prod.mk.eta, Equiv.apply_symm_apply]
    rfl

/-! ### A query algorithm with request points on the registers of a query algorithm -/

/-- **A query algorithm with request points on the registers of `Q`**: `Q`'s registers, initial
state, unitaries and output, with the requests `req` and the writes `write`. -/
noncomputable abbrev ReqQueryAlg.ofQueryAlg {X Y Req Resp O : Type} [Fintype X] [Fintype Y] {t : ℕ}
    (Q : QueryAlg X Y t O) (req : Fin (t + 1) → Q.W → Req)
    (write : Fin (t + 1) → Option Resp → Equiv.Perm Q.W)
    (req_write : ∀ k b w, req k (write k b w) = req k w) : ReqQueryAlg X Y Req Resp t O where
  W := Q.W
  instFintype := Q.instFintype
  instDecidableEq := Q.instDecidableEq
  init := Q.init
  norm_init := Q.norm_init
  step := Q.step
  req := req
  write := write
  req_write := req_write
  out := Q.out

/-! ### The bridge algorithm -/

theorem afterPermTab_logs (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁) :
    (A.afterPermTab F t j d).1.1.logs = d.1.1.logs := by
  have h1 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁,
      (A.storePerm j d').1.1.logs = d'.1.1.logs := fun d' => by
    unfold AdaptiveIAlg.storePerm AlgShape.storePerm
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    by_cases h : (d'.1.1.logs j).isSome = true
    · rw [if_pos h]
    · rw [if_neg h]
  have h2 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁,
      (A.answerPermTab F t j d').1.1.logs = d'.1.1.logs := fun d' => by
    unfold AdaptiveIAlg.answerPermTab
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    split <;> rfl
  have h3 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁,
      (A.clearPerm F.base j d').1.1.logs = d'.1.1.logs := fun d' => by
    unfold AdaptiveIAlg.clearPerm AlgShape.clearPerm
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    split <;> rfl
  unfold AdaptiveIAlg.afterPermTab
  simp only [Equiv.trans_apply, h1, h2, h3]

theorem afterAtTab_logs (k : ℕ) (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    (A.afterAtTab F k d).1.1.1.logs = d.1.1.1.logs := by
  unfold AdaptiveIAlg.afterAtTab
  split
  · exact afterPermTab_logs A F _ _ _
  · rfl

theorem absOuterSwap_logs (j : Fin A.slots) (x : Option Resp₂) (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    (absOuterSwap A F j x d).1.1.1.logs = d.1.1.1.logs := by
  unfold absOuterSwap
  dsimp only [Equiv.coe_fn_mk]
  split
  · rfl
  · split <;> rfl

theorem answerDelta_logs (j : Fin A.slots) (x : Option Resp₂) (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    (answerDelta A F j x d).1.1.1.logs = d.1.1.1.logs := by
  have hs : ∀ d' : AbsD A Req₁ Resp₁ Req₂ Resp₂,
      ((A.afterAtTab F (j + 1)).symm d').1.1.1.logs = d'.1.1.1.logs := fun d' => by
    rw [← afterAtTab_logs A F (j + 1) ((A.afterAtTab F (j + 1)).symm d'), Equiv.apply_symm_apply]
  simp only [answerDelta, Equiv.trans_apply]
  rw [hs, absOuterSwap_logs, afterAtTab_logs]

theorem absRegs_liftAbs (π : Equiv.Perm (AbsD A Req₁ Resp₁ Req₂ Resp₂))
    (w : (extRun e A C₁ F E kq d₀ (tab₀ A)).W) :
    absRegs e A C₁ F E kq d₀ (liftAbs e A C₁ F E kq d₀ π w) = π (absRegs e A C₁ F E kq d₀ w) :=
  rfl

/-- **The query algorithm with request points of the bridge**: the expanded purified run at the
empty table, with a request point at each step: at the step after slot `j` (`answerSlot`), the
outer request of the logged request of slot `j` (or `d₂` for a blank log or a request without
one), whose reply is written in place of the reply to `none` (`answerDelta`); `d₂` at the other
steps, whose reply is ignored. -/
@[irreducible] noncomputable def bridgeAlg :
    ReqQueryAlg (Bits m) (BitStr I J) Req₂ Resp₂
      ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth) + kq)
      (BaseGame.Tuple (Bits m) B (ExtReg A C₁ Req₂ Resp₂) kq) :=
  ReqQueryAlg.ofQueryAlg (extRun e A C₁ F E kq d₀ (tab₀ A))
    (fun k w => match answerSlot A C₁ k with
      | none => d₂
      | some j => match (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j with
        | none => d₂
        | some r => (F.outer (A.reqCount (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j) r).getD d₂)
    (fun k x => match answerSlot A C₁ k with
      | none => Equiv.refl _
      | some j => liftAbs e A C₁ F E kq d₀ (answerDelta A F j x))
    (fun k x w => by
      cases h : answerSlot A C₁ k with
      | none => rfl
      | some j =>
        simp only [h]
        change (match (absRegs e A C₁ F E kq d₀
            (liftAbs e A C₁ F E kq d₀ (answerDelta A F j x) w)).1.1.1.logs j with
          | none => d₂
          | some r => (F.outer (A.reqCount (absRegs e A C₁ F E kq d₀
            (liftAbs e A C₁ F E kq d₀ (answerDelta A F j x) w)).1.1.1.logs j) r).getD d₂) = _
        rw [absRegs_liftAbs, answerDelta_logs])

-- The bridge is irreducible outside the files that read its definition, which see it as reducible.
set_option allowUnsafeReducibility true in
attribute [local reducible] bridgeAlg

/-- **The bridge's requests are outer requests or the dummy.** -/
theorem bridgeAlg_req (k : Fin (((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth)
      + kq) + 1)) (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).req k w = d₂ ∨
      ∃ c r q, F.outer c r = some q ∧ (bridgeAlg e A C₁ F d₂ E kq d₀).req k w = q := by
  generalize hv : (bridgeAlg e A C₁ F d₂ E kq d₀).req k w = v
  change (match answerSlot A C₁ k with
    | none => d₂
    | some j => match (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j with
      | none => d₂
      | some r => (F.outer (A.reqCount (absRegs e A C₁ F E kq d₀ w).1.1.1.logs j) r).getD d₂) = v at hv
  subst hv
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · rename_i r _
      rcases hq : F.outer (A.reqCount (absRegs e A C₁ F E kq d₀ w).1.1.1.logs _) r with _ | q
      · exact Or.inl (by simp)
      · exact Or.inr ⟨_, r, q, hq, by simp⟩

/-- **The bridge statement**: for a trace-preserving adversary and a relay whose outer requests are
never the dummy `d₂`, every table of outer replies `tab` and every event `S`, `simLaw` of the
expanded purified extraction run of the adversary absorbed with the table (`extRun`) equals `simLaw`
of the bridge algorithm (`bridgeAlg`) with the replies of the table at the count of the earlier
outer requests (`countND`). -/
def ExtBridge : Prop :=
  A.TracePreserving →
  (∀ c r q, F.outer c r = some q → q ≠ d₂) →
  ∀ (tab : A.OuterTab Req₂ Resp₂)
    (S : Set (BaseGame.Tuple (Bits m) B (ExtReg A C₁ Req₂ Resp₂) kq × DB (Bits m) B)),
    simLaw e (extRun e A C₁ F E kq d₀ tab) S =
      simLaw e ((bridgeAlg e A C₁ F d₂ E kq d₀).instLog
        fun _ prev q => A.tabAt tab (ReqQueryAlg.countND d₂ prev) q) S

end GordieHowe.Quantum
