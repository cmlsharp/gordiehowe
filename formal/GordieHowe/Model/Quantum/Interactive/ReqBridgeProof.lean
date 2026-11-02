-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ReqBridgeCore
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeLogs
public import GordieHowe.Model.QROM.ExpandCohRelabel

@[expose] public section

-- The proofs below read the definition of the bridge (irreducible elsewhere).
set_option allowUnsafeReducibility true in
attribute [local reducible] GordieHowe.Quantum.bridgeAlg

/-!
# Toward the bridge statement: the request points as Kraus maps of the composition

The objects of the proof of `ExtBridge` (`GordieHowe/Model/Quantum/Interactive/ReqBridge.lean`)
at the level of the composition `bridgeCompose` (the trace-preserving composition of the adversary
absorbed with the empty table, a core algorithm):

- `reqV k c`: the request of the bridge's request point `k` read from the composition's work
  register `c` (`bridgeAlg_req_eq`); `histV k c`: the requests before `k`; `repV tab k c`: the reply of
  the table `tab` at the count of the earlier outer requests.
- `writeV tab k`: the request point `k` with the reply `repV tab k`, a permutation of the
  composition's registers (`answerDelta` on the absorbed registers).
- `BridgeSteps`, `bridgeComposeAt st`: the composition with the base's steps replaced by `st`;
  `bridgeCompose` its instance at the base's steps (`bridgeComposeAt_base`).
- `BridgeHopAt`, `BridgeKeepsAt`: the statements at the steps `st`; `BridgeHop`, `BridgeKeeps` at
  the base's steps.
- `bridgeCompose' tab`: the composition with step `k` read after the request point `k`
  (`KrausMap.permConj`), same registers, initial state and output.
-/

open Finset Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)
  (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)

/-- **The steps of the bridge's base**: the type of the Kraus maps of the trace-preserving form of
the adversary absorbed with the empty table. -/
abbrev BridgeSteps : Type :=
  StepIdx (A.absorbTab F (tab₀ A)).toTPKindAlg.slots (A.absorbTab F (tab₀ A)).toTPKindAlg.post →
    KrausMap (A.absorbTab F (tab₀ A)).toTPKindAlg.R
      (DReg (A.absorbTab F (tab₀ A)).toTPKindAlg.W (A.absorbTab F (tab₀ A)).toTPKindAlg.width
        (Bits m) (BitStr I J) Req₁ Resp₁)
      (DReg (A.absorbTab F (tab₀ A)).toTPKindAlg.W (A.absorbTab F (tab₀ A)).toTPKindAlg.width
        (Bits m) (BitStr I J) Req₁ Resp₁)

/-- **The composition of the bridge at the steps `st`**: the composition of the trace-preserving
form of the adversary absorbed with the empty table, its steps replaced by `st`, with `C₁`. -/
noncomputable abbrev bridgeComposeAt (st : BridgeSteps A F) :
    Alg (Bits m) (BitStr I J) ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) :=
  ({ (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st } :
    KindAlg _ O).composeBothOut C₁ id

/-- **The composition of the bridge**: the trace-preserving composition of the adversary absorbed
with the empty table with `C₁`, a core algorithm (`bridgeComposeAt` at the base's steps, `bridgeComposeAt_base`). -/
noncomputable abbrev bridgeCompose : Alg (Bits m) (BitStr I J) ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) :=
  (A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id

/-- `bridgeComposeAt` at the base's steps is `bridgeCompose`. -/
theorem bridgeComposeAt_base :
    bridgeComposeAt A C₁ F (A.absorbTab F (tab₀ A)).toTPKindAlg.step = bridgeCompose A C₁ F :=
  rfl

/-- **The request of the request point `k`** read from the composition's work register: the outer
request of slot `j`'s logged request at the step after slot `j` (`answerSlot`), the dummy `d₂`
otherwise. -/
def reqV (k : ℕ) (c : (bridgeCompose A C₁ F).V) : Req₂ :=
  match answerSlot A C₁ k with
  | none => d₂
  | some j => match c.1.adv.1.1.1.1.logs j with
    | none => d₂
    | some r => (F.outer (A.reqCount c.1.adv.1.1.1.1.logs j) r).getD d₂

/-- **The requests before the request point `k`**, read from the work register, as logs indexed by
the request points `0, …, T`. -/
def histV (T k : ℕ) (c : (bridgeCompose A C₁ F).V) : LogReg Req₂ (T + 1) :=
  fun j => if (j : ℕ) < k then some (reqV A C₁ F d₂ j c) else none

/-- **The reply of the table `tab` at the request point `k`**: the table at the count of the
earlier requests other than the dummy (`countND`), read at the request. -/
def repV (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) (c : (bridgeCompose A C₁ F).V) : Option Resp₂ :=
  A.tabAt tab (ReqQueryAlg.countND d₂ (requestsBefore (histV A C₁ F d₂ T k c) k)) (reqV A C₁ F d₂ k c)

/-- The registers of the adversary absorbed with a table, of the composition's work register. -/
def absV (c : (bridgeCompose A C₁ F).V) : AbsD A Req₁ Resp₁ Req₂ Resp₂ :=
  ((c.1.adv.1.1.1, c.1.adv.1.2), c.1.adv.2)

/-- A permutation of the registers of the adversary absorbed with a table, on the composition's
work register. -/
def liftV (π : Equiv.Perm (AbsD A Req₁ Resp₁ Req₂ Resp₂)) :
    Equiv.Perm (bridgeCompose A C₁ F).V where
  toFun c :=
    let d := π (absV A C₁ F c)
    (⟨(((d.1.1, c.1.adv.1.1.2), d.1.2), d.2), c.1.chal⟩, c.2)
  invFun c :=
    let d := π.symm (absV A C₁ F c)
    (⟨(((d.1.1, c.1.adv.1.1.2), d.1.2), d.2), c.1.chal⟩, c.2)
  left_inv c := by
    simp only [absV, Prod.mk.eta, Equiv.symm_apply_apply]
    rfl
  right_inv c := by
    simp only [absV, Prod.mk.eta, Equiv.apply_symm_apply]
    rfl

theorem absV_liftV (π : Equiv.Perm (AbsD A Req₁ Resp₁ Req₂ Resp₂)) (c : (bridgeCompose A C₁ F).V) :
    absV A C₁ F (liftV A C₁ F π c) = π (absV A C₁ F c) :=
  rfl

theorem reqV_eq (k : ℕ) (c : (bridgeCompose A C₁ F).V) :
    reqV A C₁ F d₂ k c = match answerSlot A C₁ k with
      | none => d₂
      | some j => match (absV A C₁ F c).1.1.1.logs j with
        | none => d₂
        | some r => (F.outer (A.reqCount (absV A C₁ F c).1.1.1.logs j) r).getD d₂ :=
  rfl

/-- **The request point of slot `j` keeps every request.** -/
theorem reqV_liftV_answerDelta (j : Fin A.slots) (x : Option Resp₂) (k : ℕ)
    (c : (bridgeCompose A C₁ F).V) :
    reqV A C₁ F d₂ k (liftV A C₁ F (answerDelta A F j x) c) = reqV A C₁ F d₂ k c := by
  rw [reqV_eq, reqV_eq, absV_liftV, answerDelta_logs]

theorem histV_liftV_answerDelta (j : Fin A.slots) (x : Option Resp₂) (T k : ℕ)
    (c : (bridgeCompose A C₁ F).V) :
    histV A C₁ F d₂ T k (liftV A C₁ F (answerDelta A F j x) c) = histV A C₁ F d₂ T k c := by
  funext i
  unfold histV
  rw [reqV_liftV_answerDelta]

theorem repV_liftV_answerDelta (tab : A.OuterTab Req₂ Resp₂) (j : Fin A.slots) (x : Option Resp₂)
    (T k : ℕ) (c : (bridgeCompose A C₁ F).V) :
    repV A C₁ F d₂ tab T k (liftV A C₁ F (answerDelta A F j x) c) = repV A C₁ F d₂ tab T k c := by
  unfold repV
  rw [histV_liftV_answerDelta, reqV_liftV_answerDelta]

/-- **The request point `k` with the reply of the table `tab`**, a permutation of the composition's
work register: at the step after slot `j` (`answerSlot`), the reply `repV tab T k` written in place
of the reply to `none` (`answerDelta`); the identity at the other steps. -/
def writeV (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) : Equiv.Perm (bridgeCompose A C₁ F).V :=
  match answerSlot A C₁ k with
  | none => Equiv.refl _
  | some j =>
    { toFun := fun c => liftV A C₁ F (answerDelta A F j (repV A C₁ F d₂ tab T k c)) c
      invFun := fun c => (liftV A C₁ F (answerDelta A F j (repV A C₁ F d₂ tab T k c))).symm c
      left_inv := fun c => by
        dsimp only
        rw [repV_liftV_answerDelta]
        exact Equiv.symm_apply_apply _ _
      right_inv := fun c => by
        have h : repV A C₁ F d₂ tab T k
            ((liftV A C₁ F (answerDelta A F j (repV A C₁ F d₂ tab T k c))).symm c) =
            repV A C₁ F d₂ tab T k c := by
          conv_rhs => rw [← (liftV A C₁ F (answerDelta A F j
            (repV A C₁ F d₂ tab T k c))).apply_symm_apply c]
          rw [repV_liftV_answerDelta]
        dsimp only
        rw [h]
        exact Equiv.apply_symm_apply _ _ }

/-- `writeV` on the composition's registers with the query register. -/
def writeQ (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) :
    Equiv.Perm (QueryReg (bridgeCompose A C₁ F).V 1 (Bits m) (BitStr I J)) :=
  (writeV A C₁ F d₂ tab T k).prodCongr (Equiv.refl _)

/-- **The composition with the request points of the table `tab`**: the composition at the empty
table with Kraus map `k` read after the request point `k` (`writeQ`), same registers, Kraus index,
depth, initial state and output. -/
noncomputable def bridgeCompose' (tab : A.OuterTab Req₂ Resp₂) (T : ℕ) :
    Alg (Bits m) (BitStr I J) ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) where
  V := (bridgeCompose A C₁ F).V
  depth := (bridgeCompose A C₁ F).depth
  R := (bridgeCompose A C₁ F).R
  init := (bridgeCompose A C₁ F).init
  step k := ((bridgeCompose A C₁ F).step k).permConj (writeQ A C₁ F d₂ tab T k) (Equiv.refl _)
  out := (bridgeCompose A C₁ F).out

/-! ### The objects of `simLaw_withSteps_eq_instLog` at the bridge -/

/-- The request bound of the bridge. -/
noncomputable abbrev bT : ℕ := (bridgeCompose A C₁ F).depth + kq

/-- **The request bound of the bridge from the adversary's numbers**: the challenger's `q` queries
and the adversary's `width` queries at every slot, `width` per post batch, and `kq`. -/
theorem bT_eq : bT A C₁ F kq = A.slots * (C₁.q + A.width) + A.width * A.post + kq := by
  unfold bT bridgeCompose
  rw [Circuit.toAlg_depth, ReprogrammedCircuit.queries_toCircuit, KindAlg.queries_fullCircBoth]

theorem bridgeAlg_req_eq (k) (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).req k w = reqV A C₁ F d₂ k w.1.1.1 :=
  rfl

/-- **The bridge's reply at the request point `k`**, read from the work register. -/
noncomputable def bridgeRep (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1))
    (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) : Option Resp₂ :=
  repV A C₁ F d₂ tab (bT A C₁ F kq) k w.1.1.1

/-- **Writing keeps every request of the bridge.** -/
theorem bridgeAlg_req_write (k : Fin (bT A C₁ F kq + 1)) (x : Option Resp₂)
    (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) (i : Fin (bT A C₁ F kq + 1)) :
    (bridgeAlg e A C₁ F d₂ E kq d₀).req i ((bridgeAlg e A C₁ F d₂ E kq d₀).write k x w) =
      (bridgeAlg e A C₁ F d₂ E kq d₀).req i w := by
  rw [bridgeAlg_req_eq, bridgeAlg_req_eq, reqV_eq, reqV_eq]
  have hl := (bridgeAlg_write_spec e A C₁ F d₂ E kq d₀ k x w).1
  change (absV A C₁ F _).1.1.1.logs = (absV A C₁ F _).1.1.1.logs at hl
  rw [hl]

theorem bridgeRep_write (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1)) (x : Option Resp₂)
    (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) :
    bridgeRep e A C₁ F d₂ E kq d₀ tab k ((bridgeAlg e A C₁ F d₂ E kq d₀).write k x w) =
      bridgeRep e A C₁ F d₂ E kq d₀ tab k w := by
  have hr : ∀ i, reqV A C₁ F d₂ i ((bridgeAlg e A C₁ F d₂ E kq d₀).write k x w).1.1.1 =
      reqV A C₁ F d₂ i w.1.1.1 := fun i => by
    rw [reqV_eq, reqV_eq]
    have hl := (bridgeAlg_write_spec e A C₁ F d₂ E kq d₀ k x w).1
    change (absV A C₁ F _).1.1.1.logs = (absV A C₁ F _).1.1.1.logs at hl
    rw [hl]
  have hh : histV A C₁ F d₂ (bT A C₁ F kq) k ((bridgeAlg e A C₁ F d₂ E kq d₀).write k x w).1.1.1 =
      histV A C₁ F d₂ (bT A C₁ F kq) k w.1.1.1 := by
    funext i
    simp only [histV, hr]
  simp only [bridgeRep, repV, hh, hr]

/-- **The bridge's write at the request point `k` with the reply of the table `tab`**, on the work
register with the query register. -/
noncomputable def bridgeWrite (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1)) :
    Equiv.Perm (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :=
  ((bridgeAlg e A C₁ F d₂ E kq d₀).ctrlWrite k (bridgeRep e A C₁ F d₂ E kq d₀ tab k)
    (bridgeRep_write e A C₁ F d₂ E kq d₀ tab k)).prodCongr (Equiv.refl _)

/-- **The steps of the bridge with the request points of the table `tab`**: step `k` of the bridge
after its write at the request point `k` (`bridgeWrite`). -/
noncomputable def bridgeSteps (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1)) :
    QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) ≃ₗᵢ[ℂ]
      QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)) :=
  (permOp (bridgeWrite e A C₁ F d₂ E kq d₀ tab k)).trans ((bridgeAlg e A C₁ F d₂ E kq d₀).step k)

/-- **The supports of the bridge's work register before step `k`** (proof-internal): `initW` before
step `0`, `wSet ∅ k` before step `k + 1`. -/
def goodW : ℕ → Set (bridgeAlg e A C₁ F d₂ E kq d₀).W
  | 0 => initW e A C₁ F d₂ E kq d₀
  | k + 1 => wSet e A C₁ F d₂ E kq d₀ ∅ k

/-- `goodW` on the simulation register. -/
def goodS (k : ℕ) : Set (SimRegister (bridgeAlg e A C₁ F d₂ E kq d₀).W I J m (bT A C₁ F kq)) :=
  {s | s.1.1 ∈ goodW e A C₁ F d₂ E kq d₀ k}

/-! ### The hypotheses `hS` and `hA` of `simLaw_withSteps_eq_instLog` at the bridge -/

/-- **`hS` at the bridge**: step `k` of the bridge with the table's request points is the bridge's
step after its write, on every vector of the simulation register. -/
theorem bridge_hS (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1))
    (q : QState (SimRegister (bridgeAlg e A C₁ F d₂ E kq d₀).W I J m (bT A C₁ F kq))) :
    controlled (fun _ => bridgeSteps e A C₁ F d₂ E kq d₀ tab k) q =
      ReqQueryAlg.stepSim (bridgeAlg e A C₁ F d₂ E kq d₀) k
        (permOp ((bridgeAlg e A C₁ F d₂ E kq d₀).simPerm
          ((bridgeAlg e A C₁ F d₂ E kq d₀).ctrlWrite k (bridgeRep e A C₁ F d₂ E kq d₀ tab k)
            (bridgeRep_write e A C₁ F d₂ E kq d₀ tab k))) q) := by
  rw [bridgeSteps, ReqQueryAlg.controlled_trans]
  rfl

/-- **`hA` at the bridge**: the bridge's reply at the request point `k` is the table's reply at the
count of the earlier requests other than the dummy, read at the request. -/
theorem bridge_hA (tab : A.OuterTab Req₂ Resp₂) (k : Fin (bT A C₁ F kq + 1))
    (s : SimRegister (bridgeAlg e A C₁ F d₂ E kq d₀).W I J m (bT A C₁ F kq)) :
    bridgeRep e A C₁ F d₂ E kq d₀ tab k s.1.1 =
      A.tabAt tab (ReqQueryAlg.countND d₂
        (requestsBefore ((bridgeAlg e A C₁ F d₂ E kq d₀).hist k s) k))
        ((bridgeAlg e A C₁ F d₂ E kq d₀).req k s.1.1) :=
  rfl

/-! ### The table swap and the Kraus maps of the composition along it -/

/-- **The swap of the table register between `tab` and the empty table**, on the composition's
work register. -/
def tabSwap (tab : A.OuterTab Req₂ Resp₂) : Equiv.Perm (bridgeCompose A C₁ F).V where
  toFun c := (⟨((((c.1.adv.1.1.1.1, Equiv.swap tab (tab₀ A) c.1.adv.1.1.1.2), c.1.adv.1.1.2),
    c.1.adv.1.2), c.1.adv.2), c.1.chal⟩, c.2)
  invFun c := (⟨((((c.1.adv.1.1.1.1, Equiv.swap tab (tab₀ A) c.1.adv.1.1.1.2), c.1.adv.1.1.2),
    c.1.adv.1.2), c.1.adv.2), c.1.chal⟩, c.2)
  left_inv c := by
    simp only [Equiv.swap_apply_self]
    rfl
  right_inv c := by
    simp only [Equiv.swap_apply_self]
    rfl

/-- **The composition's work registers whose table register holds `tab`.** -/
def tabBlock (tab : A.OuterTab Req₂ Resp₂) : Set (bridgeCompose A C₁ F).V :=
  {c | c.1.adv.1.1.1.2 = tab}

open KrausRel in
/-- **The request points relate the Kraus maps across the table swap, at the steps `st`**
(statement): on every column whose table register holds `tab`, Kraus map `i` of the composition at
the steps `st` read after the request point `i` (`writeV`) and along the table swap is Kraus map
`i`. -/
def BridgeHopAt (st : BridgeSteps A F) (tab : A.OuterTab Req₂ Resp₂) (T : ℕ) : Prop :=
  ∀ i : Fin ((bridgeComposeAt A C₁ F st).depth + 1),
    OpRel (queryWorkPerm (tabSwap A C₁ F tab)) {p | p.1 ∈ tabBlock A C₁ F tab}
      ((bridgeComposeAt A C₁ F st).step i)
      (((bridgeComposeAt A C₁ F st).step i).permConj (queryWorkPerm (writeV A C₁ F d₂ tab T i))
        (Equiv.refl _))

open KrausRel in
/-- **The request points relate the Kraus maps across the table swap** (statement): `BridgeHopAt`
at the base's steps. -/
def BridgeHop (tab : A.OuterTab Req₂ Resp₂) (T : ℕ) : Prop :=
  ∀ i : Fin ((bridgeCompose A C₁ F).depth + 1),
    OpRel (queryWorkPerm (tabSwap A C₁ F tab)) {p | p.1 ∈ tabBlock A C₁ F tab}
      ((bridgeCompose A C₁ F).step i)
      (((bridgeCompose A C₁ F).step i).permConj (queryWorkPerm (writeV A C₁ F d₂ tab T i))
        (Equiv.refl _))

open KrausRel in
/-- **The Kraus maps of the composition at the steps `st` keep the table register** (statement). -/
def BridgeKeepsAt (st : BridgeSteps A F) (tab : A.OuterTab Req₂ Resp₂) : Prop :=
  ∀ i : Fin ((bridgeComposeAt A C₁ F st).depth + 1),
    Keeps {p | p.1 ∈ tabBlock A C₁ F tab} ((bridgeComposeAt A C₁ F st).step i)

open KrausRel in
/-- **The Kraus maps of the composition keep the table register** (statement): `BridgeKeepsAt` at
the base's steps. -/
def BridgeKeeps (tab : A.OuterTab Req₂ Resp₂) : Prop :=
  ∀ i : Fin ((bridgeCompose A C₁ F).depth + 1),
    Keeps {p | p.1 ∈ tabBlock A C₁ F tab} ((bridgeCompose A C₁ F).step i)

end GordieHowe.Quantum
