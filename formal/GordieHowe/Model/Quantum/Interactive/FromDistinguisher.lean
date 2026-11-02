-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AbsorbBudget
public import GordieHowe.Model.Quantum.Interactive.TPRunAt
public import GordieHowe.Model.Quantum.Interactive.ProgAlg
public import GordieHowe.Model.Quantum.Interactive.PureTest
public import GordieHowe.Model.Quantum.Pure.MultiRelayRun
public import GordieHowe.Model.Quantum.Interactive.PureGameRun

@[expose] public section

/-!
# A distinguisher of the pure game as an adversary with run-time kinds

A distinguisher `D` of the pure game (`Distinguisher`, unitary steps, no post phase) is an
adversary with run-time kinds. When the pure game's runs keep a query budget `q`, the events of
its composed game against a challenger have the probabilities of the corresponding events of its
pure runs.

- `KindAlg.vecRun`, `KindAlg.mgRun_false_eq_proj`: a kind algorithm whose Kraus maps have one
  operator each, from the projector onto a vector, has a pure mixed game (without the request
  measurement): the projector onto its vector run.
- `Distinguisher.toAdaptive D hn q out`: `D` as an adversary with run-time kinds (`AdaptiveIAlg`):
  `D`'s workspace, width, slots and kinds, its steps as one-operator channels, its initial vector,
  no post batches, the budget `q`, the output `out` of the workspace. It is trace preserving
  (`toAdaptive_tracePreserving`); its shape is `AlgShape.toAdaptiveS` (`toAdaptive_toShape`).
  `KC`: its kind algorithm with the query counter, stated on concrete registers
  (`toKindAlg_eq_KC`).
- `Distinguisher.BudgetAt q j`: the basis states with at most `q` query slots before slot `j`, and
  fewer if slot `j` queries. `Distinguisher.mgRun_KC`: when the pure game's state after each step
  `j` lies in `BudgetAt q j`, the mixed game without the request measurement is the projector
  onto the pure run with the counter set to the number of query slots (`fMid`).
- `Distinguisher.toOuterMeasure_outLaw_toAdaptive`, `Distinguisher.withinBudgetAt_toAdaptive`,
  `Distinguisher.toOuterMeasure_outLaw_abortAlg_toAdaptive`: under that condition at every coins
  of a challenger at the oracle `H`, every event of the composed registers of the adversary, and of
  its aborting completion (`AdaptiveIAlg.abortAlg`), is the coin average of the probability of the
  placed event in the pure run, and the adversary stays within its budget against the challenger
  at `H` (`AdaptiveIAlg.WithinBudgetAt`).
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder

namespace GordieHowe.Quantum

/-! ### Kraus maps with one operator -/

namespace KrausMap

variable {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]

/-- Restricting a Kraus map with one operator `U` to the branches `p` gives one operator, the
projection onto `p` after `U`. -/
theorem PureAt.restrict {K : KrausMap R ι ι} {r₀ : R} {U : Matrix ι ι ℂ} (h : K.PureAt r₀ U)
    (p : ι → Bool) :
    (K.restrict p).PureAt r₀ (Matrix.diagonal (fun i => if p i then 1 else 0) * U) where
  op_eq := by simp [KrausMap.restrict, h.op_eq]
  op_ne r hr := by simp [KrausMap.restrict, h.op_ne r hr]

end KrausMap

/-! ### The mixed game of a kind algorithm with one operator per step -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {ksK : KindShape X Y Req Resp} (K : KindAlg ksK O)

/-- An operator on the adversary's registers, with the identity on the logs. -/
noncomputable def liftOp (M : Matrix (DReg K.W K.width X Y Req Resp) (DReg K.W K.width X Y Req Resp) ℂ) :
    Matrix K.G K.G ℂ :=
  (M ⊗ₖ (1 : Matrix (LogReg Req K.slots) (LogReg Req K.slots) ℂ)).submatrix splitLogs splitLogs

/-- A step with one operator `U` has, lifted to the logs, the one operator `liftOp U`. -/
theorem liftG_pureAt {k : StepIdx K.slots K.post} {r₀ : K.R}
    {U : Matrix (DReg K.W K.width X Y Req Resp) (DReg K.W K.width X Y Req Resp) ℂ}
    (h : (K.step k).PureAt r₀ U) : (K.liftG k).PureAt r₀ (K.liftOp U) := by
  exact (h.tensorId (LogReg Req K.slots)).reindex splitLogs.symm

variable [AddGroup Y] {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St)
  (U : StepIdx K.slots K.post → Matrix (DReg K.W K.width X Y Req Resp)
    (DReg K.W K.width X Y Req Resp) ℂ)

/-- A slot of the vector run: the operator, the copy of the request, the reply and the query. -/
noncomputable def vecSlot (ω : Ω) (v : QState K.G) (k : Fin K.slots) : QState K.G :=
  permOp (E.oraclePerm K.kind ω) (permOp (K.respG E ω k) (permOp (K.copyG k)
    (matApply (K.liftOp (U (slotStep k))) v)))

/-- A post batch of the vector run: the operator and the query to the oracle in force. -/
noncomputable def vecPost (ω : Ω) (v : QState K.G) (b : Fin K.post) : QState K.G :=
  permOp (K.postG E ω) (matApply (K.liftOp (U (postStep b))) v)

/-- **The vector run** of the operators `U` from the vector `ψ`: the mixed game without the request
measurement, for Kraus maps with one operator. -/
noncomputable def vecRun (ψ : QState (DReg K.W K.width X Y Req Resp)) (ω : Ω) : QState K.G :=
  matApply (K.liftOp (U lastStep)) ((List.finRange K.post).foldl (K.vecPost E U ω)
    ((List.finRange K.slots).foldl (K.vecSlot E U ω) (K.liftLogs ψ)))

/-- **The mixed game of a kind algorithm whose Kraus maps have one operator is pure**: without the
request measurement it ends in the projector onto the vector run. -/
theorem mgRun_false_eq_proj (hU : ∀ k, ∃ r₀, (K.step k).PureAt r₀ (U k))
    (ψ : QState (DReg K.W K.width X Y Req Resp)) (hinit : K.init.mat = proj ψ) (ω : Ω) :
    K.mgRun E ω false = proj (K.vecRun E U ψ ω) := by
  have hstep : ∀ k v, (K.liftG k) (proj v) = proj (matApply (K.liftOp (U k)) v) :=
    fun k v => by
      obtain ⟨r₀, h⟩ := hU k
      exact (K.liftG_pureAt h).apply_proj v
  have hslots : ∀ (l : List (Fin K.slots)) v,
      (Circuit.concat (l.map fun k : Fin K.slots =>
        Circuit.kraus (K.liftG (slotStep k)) (K.eventCirc E ω k false))).run (Equiv.refl _)
          (proj v) = proj (l.foldl (K.vecSlot E U ω) v) := by
    intro l
    induction l with
    | nil => intro v; rfl
    | cons k l ih =>
      intro v
      rw [List.map_cons, Circuit.run_concat, List.foldl_cons, ← ih]
      congr 1
      simp only [eventCirc, Circuit.run, Bool.false_eq_true, ↓reduceIte, id, KrausMap.ofPerm_apply,
        hstep, submatrix_proj]
      rfl
  have hposts : ∀ (l : List (Fin K.post)) v,
      (Circuit.concat (l.map fun b : Fin K.post =>
        Circuit.kraus (K.liftG (postStep b)) (.kraus (KrausMap.ofPerm (K.postG E ω)) .nil))).run
          (Equiv.refl _) (proj v) = proj (l.foldl (K.vecPost E U ω) v) := by
    intro l
    induction l with
    | nil => intro v; rfl
    | cons b l ih =>
      intro v
      rw [List.map_cons, Circuit.run_concat, List.foldl_cons, ← ih]
      congr 1
      simp only [Circuit.run, KrausMap.ofPerm_apply, hstep, submatrix_proj]
      rfl
  have hinit' : K.mgInit = proj (K.liftLogs ψ) := by
    ext r s
    simp only [mgInit, MState.reindex, MState.tensorKet_mat, submatrix_apply, Equiv.symm_symm,
      kroneckerMap_apply, hinit, proj, vecMulVec_apply, liftLogs_apply, Matrix.single_apply]
    by_cases hr : (splitLogs r).2 = fun _ => none <;> by_cases hs : (splitLogs s).2 = fun _ => none
    · simp [hr, hs]
    · have hs' : ¬ (fun _ => none) = (splitLogs s).2 := fun h => hs h.symm
      simp [hr, hs, hs']
    · have hr' : ¬ (fun _ => none) = (splitLogs r).2 := fun h => hr h.symm
      simp [hr, hs, hr']
    · have hr' : ¬ (fun _ => none) = (splitLogs r).2 := fun h => hr h.symm
      simp [hr, hs, hr']
  rw [mgRun, mgCirc, Circuit.run_append, Circuit.run_append, hinit', hslots, hposts]
  simp only [Circuit.run, hstep]
  rfl

end KindAlg

/-! ### A distinguisher as an adversary with run-time kinds -/

/-- A count as a value of a counter with values below `q + 2`. -/
def toCnt (q x : ℕ) : Fin (q + 2) := ⟨min x (q + 1), by omega⟩

namespace Distinguisher

variable {W X Y Req A O : Type} [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype A] [DecidableEq A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m)

/-- **The initial state of the adversary of a distinguisher** with initial vector `φ`: the
projector onto `φ`. Sealed; it unfolds through `toAdaptiveInit_eq`. -/
@[irreducible, no_expose] noncomputable def toAdaptiveInit (φ : QState (DReg W n X Y Req A))
    (hφ : ‖φ‖ = 1) : MState (DReg W n X Y Req A) :=
  MState.ofVec φ hφ

theorem toAdaptiveInit_eq (φ : QState (DReg W n X Y Req A)) (hφ : ‖φ‖ = 1) :
    toAdaptiveInit φ hφ = MState.ofVec φ hφ := by
  unfold toAdaptiveInit; rfl

/-- **Step `k` of the adversary of a distinguisher with steps `st`**: the unitary `st k` (the
identity after the last step) as a channel with one operator. Sealed; it reads only the steps,
and unfolds through `toAdaptiveStep_eq`. -/
@[irreducible, no_expose] noncomputable def toAdaptiveStep
    (st : Fin (m + 1) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (k : StepIdx m 0) : KrausMap Unit (DReg W n X Y Req A) (DReg W n X Y Req A) :=
  (KrausChannel.ofUnitary (unitaryMat (if h : (k : ℕ) < m + 1 then st ⟨k, h⟩
    else LinearIsometryEquiv.refl ℂ _)) (unitaryMat_conjTranspose_mul _)).toKrausMap

/-- The step of the adversary of `D` is `D`'s unitary `stepAt k` as a channel with one
operator. -/
theorem toAdaptiveStep_eq (k : StepIdx m 0) :
    toAdaptiveStep D.step k = (KrausChannel.ofUnitary (unitaryMat (D.stepAt k))
      (unitaryMat_conjTranspose_mul _)).toKrausMap := by
  unfold toAdaptiveStep; rfl

/-- **A distinguisher of the pure game as an adversary with run-time kinds** (module docstring):
the workspace, the kind register, the slots and the width of `D`; its steps are the unitaries of
`D` as channels with one operator; its initial state is the projector onto `D`'s initial vector;
no post batches; the query budget `q`; the output read from the workspace by `out`. -/
noncomputable def toAdaptive (hn : 0 < n) (q : ℕ) (out : W → O) :
    AdaptiveIAlg (AlgShape.toAdaptiveS (X := X) (Y := Y) (Req := Req) (Resp := A) W n m hn q) O where
  kind := D.kind
  init := toAdaptiveInit D.init D.norm_init
  step := toAdaptiveStep D.step
  out := out

variable (hn : 0 < n) (q : ℕ) (out : W → O)

/-- The kind of the adversary of a distinguisher: `D`'s. -/
theorem toAdaptive_kind : (D.toAdaptive hn q out).kind = D.kind := rfl

/-- The initial state of the adversary of a distinguisher: the projector onto `D`'s initial
vector. -/
theorem toAdaptive_init : (D.toAdaptive hn q out).init = MState.ofVec D.init D.norm_init :=
  toAdaptiveInit_eq D.init D.norm_init

/-- The initial state of the adversary of a distinguisher is the projector onto `D`'s initial
vector. -/
theorem toAdaptive_init_mat : (D.toAdaptive hn q out).init.mat = proj D.init := by
  rw [toAdaptive_init]
  rfl

/-- Step `k` of the adversary of a distinguisher: `D`'s unitary `stepAt k` as a channel with one
operator. -/
theorem toAdaptive_step (k : StepIdx m 0) :
    (D.toAdaptive hn q out).step k = (KrausChannel.ofUnitary (unitaryMat (D.stepAt k))
      (unitaryMat_conjTranspose_mul _)).toKrausMap :=
  D.toAdaptiveStep_eq k

/-- The operator of each step of the adversary of a distinguisher is `D`'s unitary. -/
theorem toAdaptive_op (k : StepIdx m 0) (i : Unit) :
    ((D.toAdaptive hn q out).step k).op i = unitaryMat (D.stepAt k) := by
  rw [toAdaptive_step]
  rfl

/-- The output of the adversary of a distinguisher: `out` of the workspace. -/
theorem toAdaptive_out : (D.toAdaptive hn q out).out = out := rfl

/-- **The shape of the adversary of a distinguisher** (`AlgShape.toAdaptiveS`). -/
theorem toAdaptive_toShape :
    (D.toAdaptive hn q out).toShape = AlgShape.toAdaptiveS (X := X) (Y := Y) W n m hn q :=
  rfl

/-- **The adversary of a distinguisher is trace preserving.** -/
theorem toAdaptive_tracePreserving : (D.toAdaptive hn q out).TracePreserving := fun k => by
  rw [toAdaptive_step]
  change ∑ r : Unit, (unitaryMat (D.stepAt k))ᴴ * unitaryMat (D.stepAt k) = 1
  rw [Fintype.sum_unique]
  exact unitaryMat_conjTranspose_mul _

/-- Each step of the adversary of a distinguisher has the one operator `D.stepAt k`. -/
theorem toAdaptive_step_pureAt (k : StepIdx m 0) :
    ((D.toAdaptive hn q out).step k).PureAt () (unitaryMat (D.stepAt k)) := by
  rw [toAdaptive_step]
  exact KrausChannel.ofUnitary_pureAt _ _

/-- The registers with a counter as the registers and the counter. -/
def cntSplitC : DReg (W × Fin (q + 2)) n X Y Req A ≃ DReg W n X Y Req A × Fin (q + 2) where
  toFun p := (((p.1.1.1, p.1.2.1, p.1.2.2), p.2), p.1.1.2)
  invFun q := ((((q.1.1.1, q.2), q.1.1.2.1, q.1.1.2.2)), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Within the budget (`AdaptiveIAlg.inBudget` of `toAdaptive`). -/
def inBudgetC (d : DReg (W × Fin (q + 2)) n X Y Req A) : Bool :=
  D.kind d.1.1.1 || decide (d.1.1.2 ≠ Fin.castSucc (Fin.last q))

/-- The counter advanced on the query branches (`AdaptiveIAlg.cntShift` of `toAdaptive`). -/
def cntShiftC : Equiv.Perm (DReg (W × Fin (q + 2)) n X Y Req A) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.prodShear (Equiv.refl W)
    fun w => if D.kind w then Equiv.refl _ else finRotate _) (Equiv.refl _)) (Equiv.refl _)

/-- The operator of the step of the adversary with its counter, before the projection. -/
noncomputable def cntOp (k : StepIdx m 0) :
    Matrix (DReg (W × Fin (q + 2)) n X Y Req A) (DReg (W × Fin (q + 2)) n X Y Req A) ℂ :=
  (unitaryMat (D.stepAt k) ⊗ₖ (1 : Matrix (Fin (q + 2)) (Fin (q + 2)) ℂ)).submatrix
    (cntSplitC q) (cntSplitC q)

/-- **The operator of each step of the adversary with its counter**: before a slot, the step, the
projection onto the branches within the budget and the counter advanced; after the slots, the
step. -/
noncomputable def kindOp (k : StepIdx m 0) :
    Matrix (DReg (W × Fin (q + 2)) n X Y Req A) (DReg (W × Fin (q + 2)) n X Y Req A) ℂ :=
  if (k : ℕ) < m then
    (Matrix.diagonal (fun i : DReg (W × Fin (q + 2)) n X Y Req A =>
      if D.inBudgetC q i then (1 : ℂ) else 0) *
      D.cntOp q k).submatrix (D.cntShiftC q).symm (Equiv.refl _)
  else D.cntOp q k

/-- Each step of the kind algorithm of the adversary with its counter has the one operator
`kindOp q k`. -/
theorem toKindAlg_step_pureAt (k : StepIdx m 0) :
    ((D.toAdaptive hn q out).toKindAlg.step k).PureAt () (D.kindOp q k) := by
  have h0 := ((D.toAdaptive_step_pureAt hn q out k).tensorId (Fin (q + 2))).reindex
    (D.toAdaptive hn q out).cntSplit.symm
  by_cases hk : (k : ℕ) < m
  · have hs : (D.toAdaptive hn q out).toKindAlg.step k = KrausMap.permConj
        (((((D.toAdaptive hn q out).step k).tensorId (Fin (q + 2))).reindex
          (D.toAdaptive hn q out).cntSplit.symm).restrict (D.toAdaptive hn q out).inBudget)
        (Equiv.refl _) (D.toAdaptive hn q out).cntShift :=
      AdaptiveIAlg.toKindAlg_step_of_lt _ hk
    rw [hs]
    unfold kindOp
    rw [if_pos hk]
    exact (h0.restrict _).permConj _ _
  · have hs : (D.toAdaptive hn q out).toKindAlg.step k = (((D.toAdaptive hn q out).step k).tensorId
        (Fin (q + 2))).reindex (D.toAdaptive hn q out).cntSplit.symm :=
      AdaptiveIAlg.toKindAlg_step_of_not_lt _ hk
    rw [hs]
    unfold kindOp
    rw [if_neg hk]
    exact h0

/-! ### The run of the adversary with its counter -/

/-- A game basis state of `D` with the counter at `c`. -/
def addCnt (c : Fin (q + 2)) (g : GameReg W n X Y Req A m) : GameReg (W × Fin (q + 2)) n X Y Req A m :=
  (((g.1.1, c), g.1.2), g.2)


omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] in
/-- **A sum over the image of a pushed vector.** -/
theorem sum_mul_pushV {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (a : κ → ℂ) (f : ι → κ)
    (v : QState ι) : ∑ k, a k * pushV f v k = ∑ i, a (f i) * v i := by
  classical
  simp only [pushV_apply, Finset.mul_sum]
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := f) (f := fun i => a (f i) * v i)]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.1 hi).2]

/-- **The shape of `KC`**: the workspace with the query counter, width `n`, `m` slots, no post batches, one Kraus operator. -/
@[reducible] def KCS (W : Type) [Fintype W] [DecidableEq W] (m : ℕ) (hn : 0 < n) (q : ℕ) :
    KindShape X Y Req A where
  W := W × Fin (q + 2)
  width := n
  width_pos := hn
  slots := m
  post := 0
  R := Unit

/-- **The kind algorithm of the adversary with its counter**, with its registers stated
concretely; it is `(D.toAdaptive hn q out).toKindAlg` (`toKindAlg_eq_KC`). -/
noncomputable abbrev KC : KindAlg (KCS (X := X) (Y := Y) (Req := Req) (A := A) W m hn q) O where
  kind w := D.kind w.1
  init := (D.toAdaptive hn q out).toKindAlg.init
  step := (D.toAdaptive hn q out).toKindAlg.step
  out w := out w.1

/-- The kind algorithm of the adversary is `KC`. -/
theorem toKindAlg_eq_KC : (D.toAdaptive hn q out).toKindAlg = D.KC hn q out :=
  rfl

/-- An operator on the registers with the counter, with the identity on the logs. -/
noncomputable def liftOpC (M : Matrix (DReg (W × Fin (q + 2)) n X Y Req A)
    (DReg (W × Fin (q + 2)) n X Y Req A) ℂ) :
    Matrix (GameReg (W × Fin (q + 2)) n X Y Req A m) (GameReg (W × Fin (q + 2)) n X Y Req A m) ℂ :=
  (M ⊗ₖ (1 : Matrix (LogReg Req m) (LogReg Req m) ℂ)).submatrix splitLogs splitLogs

/-- The lift to the logs of `KC` is `liftOpC`. -/
theorem liftOp_toKindAlg (M : Matrix (DReg (W × Fin (q + 2)) n X Y Req A)
    (DReg (W × Fin (q + 2)) n X Y Req A) ℂ) :
    (D.KC hn q out).liftOp M = liftOpC (m := m) q M :=
  rfl

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] in
/-- The game basis states that `addCnt` with the counter read from the logs by `c` sends to a
given state: that state without its counter if the counter is `c` of its logs, no state
otherwise. -/
theorem filter_addCnt_eq (c : LogReg Req m → Fin (q + 2)) (w : W) (cr : Fin (q + 2)) (rq : Req)
    (rs : Option A) (lg : LogReg Req m) (ps : Fin n → X × Y) [Fintype W] [Fintype X] [Fintype Y]
    [Fintype Req] [Fintype A] :
    Finset.univ.filter (fun g : GameReg W n X Y Req A m => addCnt q (c g.1.2.2.2) g =
      (((w, cr), rq, rs, lg), ps)) = if cr = c lg then {((w, rq, rs, lg), ps)} else ∅ := by
  ext ⟨⟨w', rq', rs', lg'⟩, ps'⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, addCnt, Prod.mk.injEq]
  split_ifs with h
  · simp only [Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4, h5⟩, h6⟩
      exact ⟨⟨h1, h3, h4, h5⟩, h6⟩
    · rintro ⟨⟨h1, h3, h4, h5⟩, h6⟩
      subst h1 h3 h4 h5 h6
      exact ⟨⟨⟨rfl, h.symm⟩, rfl, rfl, rfl⟩, rfl⟩
  · simp only [Finset.notMem_empty, iff_false]
    rintro ⟨⟨⟨-, h2⟩, -, -, h5⟩, -⟩
    exact h (by rw [← h5]; exact h2.symm)

/-- The entries of the lifted step with the counter: the entry of the distinguisher's step times
the identity on the counter and on the logs. -/
theorem liftOpC_cntOp_apply (k : StepIdx m 0) (r r' : GameReg (W × Fin (q + 2)) n X Y Req A m) :
    liftOpC q (D.cntOp q k) r r' =
      unitaryMat (D.stepAt k) ((r.1.1.1, r.1.2.1, r.1.2.2.1), r.2)
        ((r'.1.1.1, r'.1.2.1, r'.1.2.2.1), r'.2) *
        ((if r.1.1.2 = r'.1.1.2 then 1 else 0) * (if r.1.2.2.2 = r'.1.2.2.2 then 1 else 0)) := by
  obtain ⟨⟨⟨w, c⟩, rq, rs, lg⟩, ps⟩ := r
  obtain ⟨⟨⟨w', c'⟩, rq', rs', lg'⟩, ps'⟩ := r'
  simp only [liftOpC, cntOp, submatrix_apply, kroneckerMap_apply, Matrix.one_apply, cntSplitC,
    splitLogs, Equiv.coe_fn_mk, Prod.mk.injEq]
  rw [mul_assoc]

/-- **The step of the adversary with its counter**, before the projection, acts on the
distinguisher's registers placed with a counter read from the logs as the distinguisher's step. -/
theorem matApply_cntOp_pushV (k : StepIdx m 0) (c : LogReg Req m → Fin (q + 2))
    (v : QState (GameReg W n X Y Req A m)) :
    matApply (liftOpC q (D.cntOp q k)) (pushV (fun g => addCnt q (c g.1.2.2.2) g) v) =
      pushV (fun g => addCnt q (c g.1.2.2.2) g) (D.liftedStep k v) := by
  classical
  ext r
  obtain ⟨⟨⟨w, cr⟩, rq, rs, lg⟩, ps⟩ := r
  rw [matApply_apply, sum_mul_pushV, pushV_apply, filter_addCnt_eq]
  simp only [D.liftOpC_cntOp_apply q k]
  rw [← splitLogs.symm.sum_comp, Fintype.sum_prod_type]
  split_ifs with hc
  · rw [Finset.sum_singleton]
    simp only [Distinguisher.liftedStep, logControlled_apply]
    rw [← matApply_unitaryMat, matApply_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_eq_single lg (fun lg' _ hne => by
      simp [splitLogs, addCnt, Ne.symm hne]) (by simp)]
    simp [splitLogs, addCnt, hc]
  · rw [Finset.sum_empty]
    refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun lg' _ => ?_
    by_cases hl : lg = lg'
    · subst hl
      simp [splitLogs, addCnt, hc]
    · simp [splitLogs, addCnt, hl]

omit [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype
    Req]
  [DecidableEq Req] [Fintype A] [DecidableEq A] in
/-- Applying a diagonal matrix after `M` scales each entry of the image. -/
theorem matApply_diagonal_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) (M : Matrix ι ι ℂ)
    (v : QState ι) (i : ι) : matApply (Matrix.diagonal d * M) v i = d i * matApply M v i := by
  simp only [matApply_apply, Matrix.diagonal_mul, Finset.mul_sum, mul_assoc]

/-- Applying the lift of `M` with its rows permuted by `τ` is applying the lift of `M`, then
`τ` on the registers. -/
theorem liftOpC_submatrix (M : Matrix (DReg (W × Fin (q + 2)) n X Y Req A)
    (DReg (W × Fin (q + 2)) n X Y Req A) ℂ) (τ : Equiv.Perm (DReg (W × Fin (q + 2)) n X Y Req A))
    (v : QState (GameReg (W × Fin (q + 2)) n X Y Req A m)) :
    matApply (liftOpC q (M.submatrix τ.symm (Equiv.refl _))) v =
      permOp (liftL τ) (matApply (liftOpC q M) v) := by
  ext r
  simp only [matApply_apply, permOp_apply, liftOpC, submatrix_apply, kroneckerMap_apply]
  rfl

/-- Applying the lift of a diagonal matrix after `M` scales each entry of the image by the
diagonal entry of its registers. -/
theorem liftOpC_diag_mul (d : DReg (W × Fin (q + 2)) n X Y Req A → ℂ)
    (M : Matrix (DReg (W × Fin (q + 2)) n X Y Req A) (DReg (W × Fin (q + 2)) n X Y Req A) ℂ)
    (v : QState (GameReg (W × Fin (q + 2)) n X Y Req A m)) (r : GameReg (W × Fin (q + 2)) n X Y Req A m) :
    matApply (liftOpC q (Matrix.diagonal d * M)) v r = d (splitLogs r).1 * matApply (liftOpC q M) v r := by
  simp only [matApply_apply, liftOpC, submatrix_apply, kroneckerMap_apply, Matrix.diagonal_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun r' _ => ?_
  ring

/-- The counter placed at the query slots below `k`. -/
def fMid (k : ℕ) (g : GameReg W n X Y Req A m) : GameReg (W × Fin (q + 2)) n X Y Req A m :=
  addCnt q (toCnt q (queriesBefore g.1.2.2.2 k)) g

/-- The counter placed after the step before slot `k`: the query slots below `k`, and one more if
slot `k` queries. -/
def fAfter (k : ℕ) (g : GameReg W n X Y Req A m) : GameReg (W × Fin (q + 2)) n X Y Req A m :=
  addCnt q (toCnt q (queriesBefore g.1.2.2.2 k + if D.kind g.1.1 then 0 else 1)) g

/-- The basis states within the budget before slot `k`. -/
def BudgetAt (k : ℕ) : Set (GameReg W n X Y Req A m) :=
  {g | queriesBefore g.1.2.2.2 k ≤ q ∧ (D.kind g.1.1 = false → queriesBefore g.1.2.2.2 k < q)}

/-- **The step before a slot of the adversary with its counter**: on a vector whose image under
the distinguisher's step lies within the budget, the distinguisher's step with the counter
advanced on the query branches. -/
theorem matApply_kindOp_pushV {k : StepIdx m 0} (hk : (k : ℕ) < m)
    (v : QState (GameReg W n X Y Req A m)) (hv : Supported (D.BudgetAt q k) (D.liftedStep k v)) :
    matApply (liftOpC q (D.kindOp q k)) (pushV (fMid q k) v) =
      pushV (D.fAfter q k) (D.liftedStep k v) := by
  classical
  have hmid : matApply (liftOpC q (Matrix.diagonal (fun i : DReg (W × Fin (q + 2)) n X Y Req A =>
      if D.inBudgetC q i then (1 : ℂ) else 0) * D.cntOp q k)) (pushV (fMid q k) v) =
      pushV (fMid q k) (D.liftedStep k v) := by
    ext r
    have hf : (fMid (W := W) (n := n) (X := X) (Y := Y) (Req := Req) (A := A) (m := m) q k) =
        fun g => addCnt q ((fun lg => toCnt q (queriesBefore lg k)) g.1.2.2.2) g := rfl
    rw [liftOpC_diag_mul, hf, D.matApply_cntOp_pushV q k (fun lg => toCnt q (queriesBefore lg k)) v]
    split_ifs with hb
    · rw [one_mul]
    · rw [zero_mul, pushV_apply]
      refine (Finset.sum_eq_zero fun g hg => hv g fun hgB => hb ?_).symm
      have hr := (Finset.mem_filter.1 hg).2
      subst hr
      obtain ⟨hc1, hc2⟩ := hgB
      simp only [inBudgetC, splitLogs, Equiv.coe_fn_mk, fMid, addCnt, toCnt]
      cases hkd : D.kind g.1.1
      · have := hc2 hkd
        simp only [Bool.false_or]
        exact decide_eq_true fun h => by
          have := congrArg Fin.val h
          simp at this
          omega
      · rfl
  unfold kindOp
  rw [if_pos hk, liftOpC_submatrix, hmid]
  refine permOp_pushV hv (π := Equiv.refl _) fun g hg => ?_
  obtain ⟨hc1, hc2⟩ := hg
  obtain ⟨⟨w, rq, rs, lg⟩, ps⟩ := g
  simp only at hc1 hc2
  simp only [liftL_apply, fMid, fAfter, addCnt, Equiv.refl_apply, cntShiftC, splitLogs,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Equiv.prodCongr_apply, Prod.map, Equiv.prodShear_apply,
    Equiv.coe_refl, id]
  by_cases hkd : D.kind w = true
  · simp [hkd]
  · have hkd' : D.kind w = false := by simpa using hkd
    have := hc2 hkd'
    simp only [hkd', Bool.false_eq_true, ↓reduceIte, toCnt, Prod.mk.injEq, and_true, true_and]
    ext
    rw [coe_finRotate_of_ne_last (by simp [Fin.ext_iff]; omega)]
    simp only
    omega

variable [AddGroup Y] {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req A X Y Q St)

/-- **The events of a slot on the registers with the counter**: the copy of the request, the reply
and the query leave the counter, which then counts the slot. -/
theorem events_fAfter (ω : Ω) {k : ℕ} (hk : k < m) (g : GameReg W n X Y Req A m)
    (hg : g.1.2.2.2 ⟨k, hk⟩ = none) :
    E.oraclePerm (fun w : W × Fin (q + 2) => D.kind w.1) ω
      (((respondPerm (fun w : W × Fin (q + 2) => D.kind w.1)
          (fun lg => E.answer ω lg ⟨k, hk⟩)).prodCongr (Equiv.refl _))
        (((copyPerm (fun w : W × Fin (q + 2) => D.kind w.1) ⟨k, hk⟩).prodCongr (Equiv.refl _))
          (D.fAfter q k g))) =
      fMid q (k + 1) (D.eventPerm E ω k g) := by
  obtain ⟨⟨w, rq, rs, lg⟩, ps⟩ := g
  change lg ⟨k, hk⟩ = none at hg
  have hqb : ∀ lg' : LogReg Req m, (∀ i : Fin m, (i : ℕ) < k → lg' i = lg i) →
      queriesBefore lg' (k + 1) = queriesBefore lg k + if lg' ⟨k, hk⟩ = none then 1 else 0 := by
    intro lg' h
    rw [queriesBefore_succ, queriesBefore_congr h]
    simp only [queriedAt, hk, ↓reduceDIte]
    cases lg' ⟨k, hk⟩ <;> simp
  simp only [eventPerm, hk, ↓reduceDIte, Equiv.trans_apply, Env.requestPerm, fAfter, fMid,
    addCnt, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
  by_cases hkd : D.kind w = true
  · simp only [copyPerm_apply, respondPerm_apply, hkd, ↓reduceIte, hg, Equiv.swap_apply_left]
    rw [Env.oraclePerm, Env.oraclePerm, queryPermOf_apply, queryPermOf_apply]
    simp only [hkd, ↓reduceIte, Prod.mk.injEq, and_true, true_and]
    rw [hqb _ fun i hi => Function.update_of_ne (fun e => by subst e; simp at hi) _ _]
    simp
  · have hkd' : D.kind w = false := by simpa using hkd
    simp only [copyPerm_apply, respondPerm_apply, hkd', Bool.false_eq_true, ↓reduceIte]
    rw [Env.oraclePerm, Env.oraclePerm, queryPermOf_apply, queryPermOf_apply]
    simp only [hkd', Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, and_true, true_and]
    rw [hqb _ fun i hi => rfl, hg]
    simp

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] in
/-- The entries of a vector pushed by `addCnt` with the counter read from the logs by `c`: the
entry without the counter if the counter is `c` of the logs, `0` otherwise. -/
theorem pushV_addCnt_apply [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
    (c : LogReg Req m → Fin (q + 2)) (v : QState (GameReg W n X Y Req A m)) (w : W)
    (cr : Fin (q + 2)) (rq : Req) (rs : Option A) (lg : LogReg Req m) (ps : Fin n → X × Y) :
    pushV (fun g => addCnt q (c g.1.2.2.2) g) v (((w, cr), rq, rs, lg), ps) =
      if cr = c lg then v ((w, rq, rs, lg), ps) else 0 := by
  rw [pushV_apply, filter_addCnt_eq]
  split_ifs <;> simp

/-- The initial vector of the adversary with its counter: `D`'s initial vector, counter `0`. -/
noncomputable def initC : QState (DReg (W × Fin (q + 2)) n X Y Req A) :=
  WithLp.toLp 2 fun d => if d.1.1.2 = 0 then D.init (cntSplitC q d).1 else 0

/-- The initial state of `KC` is the projector onto `initC`. -/
theorem toKindAlg_init_mat :
    (D.KC hn q out).init.mat = proj (D.initC q) := by
  refine ((D.toAdaptive hn q out).toKindAlg_init_mat_of_proj (φ := D.init)
      (D.toAdaptive_init_mat hn q out)).trans
    (congrArg proj ?_)
  ext ⟨⟨⟨w, c⟩, rq, rs⟩, ps⟩
  simp only [AdaptiveIAlg.cntVec, relabel_apply, Equiv.symm_symm]
  erw [tensorKet_apply]
  -- TODO(unbundle-M4): `KC` keeps the product `W × Fin (q + 2)` where `toKindAlg` has the named
  -- `CntW`; `erw` matches `CntW.mk w c` against the pair `(w, c)`.
  erw [AdaptiveIAlg.cntSplit_apply]
  by_cases hc : c = 0
  · simp only [initC, hc, cntSplitC, Equiv.coe_fn_mk, ↓reduceIte, mul_one]
  · simp [initC, hc, cntSplitC]

/-- `initC` with empty logs is the pure game's initial vector with the counter at `0`. -/
theorem liftLogs_initC :
    (D.KC hn q out).liftLogs (D.initC q) =
      pushV (fMid (m := m) q 0) D.gameInit := by
  ext r
  obtain ⟨⟨⟨w, cr⟩, rq, rs, lg⟩, ps⟩ := r
  have hf : (fMid (W := W) (n := n) (X := X) (Y := Y) (Req := Req) (A := A) (m := m) q 0) =
      fun g => addCnt q ((fun lg => toCnt q (queriesBefore lg 0)) g.1.2.2.2) g := rfl
  have hp := pushV_addCnt_apply q (fun lg => toCnt q (queriesBefore lg 0)) D.gameInit w cr rq rs lg ps
  rw [← hf] at hp
  rw [hp, KindAlg.liftLogs_apply]
  simp only [initC, gameInit, splitLogs, Equiv.coe_fn_mk, cntSplitC, PiLp.toLp_apply,
    queriesBefore_zero, toCnt]
  have h0 : (⟨min 0 (q + 1), by omega⟩ : Fin (q + 2)) = 0 := by ext; simp
  rw [h0]
  by_cases h1 : cr = 0 <;> by_cases h2 : lg = (fun _ => none) <;> simp [h1, h2]

/-- The input of `step k` in the pure game: the initial state, then the state after slot `k - 1`. -/
noncomputable def preStage (ω : Ω) : ℕ → QState (GameReg W n X Y Req A m)
  | 0 => D.gameInit
  | k + 1 => permOp (D.eventPerm E ω k) (D.stage E ω k)

/-- The state after `step k` of the pure game is `step k` applied to its input. -/
theorem stage_eq_preStage (ω : Ω) (k : ℕ) : D.stage E ω k = D.liftedStep k (D.preStage E ω k) := by
  cases k <;> rfl

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq W] [DecidableEq X]
  [DecidableEq Y] [DecidableEq Req] [DecidableEq A] in
/-- The first `j + 1` slots are the first `j` slots and slot `j`. -/
theorem take_finRange_succ {j : ℕ} (hj : j < m) :
    (List.finRange m).take (j + 1) = (List.finRange m).take j ++ [⟨j, hj⟩] := by
  rw [List.take_succ, List.getElem?_eq_getElem (by simpa using hj), List.getElem_finRange]
  rfl

/-- **The vector run of the adversary with its counter**, slot by slot: the pure game's input of
`step j`, with the counter at the query slots below `j`, when the run stays within the budget. -/
theorem foldl_vecSlot (ω : Ω) (hB : ∀ j < m, Supported (D.BudgetAt q j) (D.stage E ω j)) :
    ∀ j ≤ m, ((List.finRange m).take j).foldl ((D.KC hn q out).vecSlot E
        (D.kindOp q) ω) ((D.KC hn q out).liftLogs (D.initC q)) =
      pushV (fMid q j) (D.preStage E ω j) := by
  intro j
  induction j with
  | zero => intro _; rw [List.take_zero, List.foldl_nil, D.liftLogs_initC hn q out]; rfl
  | succ j ih =>
    intro hj
    rw [take_finRange_succ (by omega), List.foldl_append, ih (by omega), List.foldl_cons,
      List.foldl_nil]
    simp only [KindAlg.vecSlot]
    rw [liftOp_toKindAlg]
    have hstep := D.matApply_kindOp_pushV q (k := slotStep (post := 0) ⟨j, by omega⟩)
      (show j < m by omega) (D.preStage E ω j) (by
        rw [← stage_eq_preStage]
        exact hB j (by omega))
    change matApply _ (pushV (fMid q j) _) = pushV (D.fAfter q j) (D.liftedStep j _) at hstep
    refine (congrArg _ (congrArg _ (congrArg _ hstep))).trans ?_
    rw [← permOp_trans, ← permOp_trans, ← stage_eq_preStage]
    have hR : Supported (logsIn (reachableLogs j)) (D.stage E ω j) :=
      D.hybrid_supported_reachable _ (fun k r hr => D.eventPerm_mem_reachableSet E ω hr) j
    refine permOp_pushV hR fun g hg => ?_
    have hgj : g.1.2.2.2 ⟨j, by omega⟩ = none := hg ⟨j, by omega⟩ le_rfl
    exact D.events_fAfter q E ω (by omega) g hgj

/-- **The vector run of the adversary with its counter** is the run of the pure game with the
counter at the number of query slots, when the run stays within the budget. -/
theorem vecRun_KC (ω : Ω) (hB : ∀ j < m, Supported (D.BudgetAt q j) (D.stage E ω j)) :
    (D.KC hn q out).vecRun E (D.kindOp q) (D.initC q) ω = pushV (fMid q m) (D.run E ω) := by
  have hf := D.foldl_vecSlot hn q out E ω hB m le_rfl
  rw [List.take_of_length_le (by simp)] at hf
  simp only [KindAlg.vecRun]
  have hpost : (List.finRange (D.KC hn q out).post) = [] := List.finRange_zero
  rw [hpost, List.foldl_nil]
  refine (congrArg _ hf).trans ?_
  rw [liftOp_toKindAlg]
  have hk : D.kindOp q (lastStep : StepIdx m 0) = D.cntOp q lastStep := by
    unfold kindOp
    exact if_neg (by simp)
  refine (congrArg (fun M => matApply (liftOpC q M) _) hk).trans ?_
  have hc := D.matApply_cntOp_pushV q lastStep (fun lg => toCnt q (queriesBefore lg m))
    (D.preStage E ω m)
  refine hc.trans ?_
  rw [run, stage_eq_preStage]
  rfl

/-- **The mixed game of the adversary with its counter**, without the request measurement, is the
projector onto the pure game's run with the counter, when the run stays within the budget. -/
theorem mgRun_KC (ω : Ω) (hB : ∀ j < m, Supported (D.BudgetAt q j) (D.stage E ω j)) :
    (D.KC hn q out).mgRun E ω false = proj (pushV (fMid q m) (D.run E ω)) := by
  have hU : ∀ k : StepIdx m 0, ∃ r₀, ((D.KC hn q out).step k).PureAt r₀ (D.kindOp q k) :=
    fun k => ⟨(), D.toKindAlg_step_pureAt hn q out k⟩
  have h := KindAlg.mgRun_false_eq_proj (D.KC hn q out) E (D.kindOp q) hU (D.initC q)
    (D.toKindAlg_init_mat hn q out) ω
  exact h.trans (congrArg proj (D.vecRun_KC hn q out E ω hB))

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq W] [DecidableEq X]
  [DecidableEq Y] [DecidableEq Req] [DecidableEq A] in
/-- Placing the counter is injective. -/
theorem fMid_injective (k : ℕ) :
    Function.Injective (fMid (W := W) (n := n) (X := X) (Y := Y) (Req := Req) (A := A) (m := m) q k) := by
  rintro ⟨⟨w, rq, rs, lg⟩, ps⟩ ⟨⟨w', rq', rs', lg'⟩, ps'⟩ h
  simp only [fMid, addCnt, Prod.mk.injEq] at h
  obtain ⟨⟨⟨h1, -⟩, h2, h3, h4⟩, h5⟩ := h
  subst h1 h2 h3 h4 h5
  rfl

omit [DecidableEq W] [DecidableEq X] [DecidableEq Y] in
/-- The run of the pure game is a unit vector. -/
theorem norm_run (ω : Ω) : ‖D.run E ω‖ = 1 := by
  rw [run, stage, norm_hybrid, D.norm_gameInit]

/-- The diagonal of the mixed game of the distinguisher's adversary with the request measurement:
the squared amplitudes of the pure game's run with the counter, within the budget. -/
theorem re_mgRun_KC (ω : Ω) (hB : ∀ j < m, Supported (D.BudgetAt q j) (D.stage E ω j))
    (r : (D.KC hn q out).G) :
    ((D.KC hn q out).mgRun E ω true r r).re = ‖pushV (fMid q m) (D.run E ω) r‖ ^ 2 := by
  rw [KindAlg.mgRun_deph, dephase_apply_self, D.mgRun_KC hn q out E ω hB, proj_apply]

variable [Nonempty X] [Nonempty Y]

/-- **The events of the composed registers of the distinguisher's adversary** against a
challenger `C` at the oracle `H`: when the pure game's runs stay within the budget at every coins,
the probability of an event is the coin average of the probability, in the pure game's run, of
the placed event. -/
theorem toOuterMeasure_outLaw_toAdaptive (C : Challenger X Y Req A) (H : X → Y)
    (hB : ∀ c, ∀ j < m, Supported (D.BudgetAt q j) (D.stage C.toPureEnv (H, c) j))
    (P : (D.toAdaptive hn q out).toKindAlg.CW C → Prop) :
    (((D.toAdaptive hn q out).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v} =
      ENNReal.ofReal (∑ c, (C.coins c).toReal *
        prob {g | P ((D.toAdaptive hn q out).toKindAlg.emb C H c m (fMid q m g)).1}
          (D.run C.toPureEnv (H, c))) := by
  classical
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut_id]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have hp := prob_pushV (S := Set.univ) (fun _ h => absurd trivial h)
    (fun g _ g' _ h => fMid_injective q m h)
    {r : GameReg (W × Fin (q + 2)) n X Y Req A m | P ((D.toAdaptive hn q out).toKindAlg.emb C H c m r).1}
    (v := D.run C.toPureEnv (H, c))
  refine Eq.trans ?_ hp
  rw [prob, norm_mask_sq, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr := D.re_mgRun_KC hn q out C.toPureEnv (H, c) (hB c) r
  split_ifs with h1 h2 h2
  · exact hr
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

/-- **The distinguisher's adversary stays within its budget** against `C` at `H` when the pure
game's runs stay within the budget at every coins. -/
theorem withinBudgetAt_toAdaptive (C : Challenger X Y Req A) (H : X → Y)
    (hB : ∀ c, ∀ j < m, Supported (D.BudgetAt q j) (D.stage C.toPureEnv (H, c) j)) :
    (D.toAdaptive hn q out).WithinBudgetAt C H := by
  classical
  refine AdaptiveIAlg.withinBudgetAt_of_outLaw_none _ C H ?_
  rw [AdaptiveIAlg.outLaw_compose_none_eq, ENNReal.ofReal_eq_zero, sub_nonpos]
  have h1 : ∀ c, ((D.toAdaptive hn q out).toKindAlg.mgRun C.toPureEnv (H, c) true).trace.re = 1 := by
    intro c
    rw [Matrix.trace, Complex.re_sum]
    have hd : ∀ r : (D.KC hn q out).G, (((D.toAdaptive hn q out).toKindAlg.mgRun C.toPureEnv (H, c)
        true).diag r).re = ‖pushV (fMid q m) (D.run C.toPureEnv (H, c)) r‖ ^ 2 :=
      fun r => D.re_mgRun_KC hn q out C.toPureEnv (H, c) (hB c) r
    refine (Finset.sum_congr rfl fun r _ => hd r).trans ?_
    have h := prob_pushV (S := Set.univ) (fun _ h => absurd trivial h)
      (fun g _ g' _ h => fMid_injective q m h) (Set.univ : Set (GameReg (W × Fin (q + 2)) n X Y Req A m))
      (v := D.run C.toPureEnv (H, c))
    rw [Set.preimage_univ, prob_univ, prob_univ, D.norm_run, EuclideanSpace.norm_sq_eq] at h
    simp only [one_pow] at h
    refine Eq.trans ?_ h
    first
    | rfl
    | (congr 1; exact Subsingleton.elim _ _)
  simp only [h1, mul_one]
  have hsum : ∑ c, C.coins c = 1 := by
    rw [← tsum_fintype (L := .unconditional _), PMF.tsum_coe]
  rw [← ENNReal.toReal_sum fun c _ => PMF.apply_ne_top _ c, hsum, ENNReal.toReal_one]

/-- **The events of the composed registers of the aborting completion of the distinguisher's
adversary**: when the pure game's runs stay within the budget at every coins, the probability of
an event is the coin average of the probability, in the pure game's run, of the event placed and
lifted. -/
theorem toOuterMeasure_outLaw_abortAlg_toAdaptive (C : Challenger X Y Req A) (H : X → Y)
    (hB : ∀ c, ∀ j < m, Supported (D.BudgetAt q j) (D.stage C.toPureEnv (H, c) j))
    (P : (D.toAdaptive hn q out).abortAlg.toKindAlg.CW C → Prop) :
    (((D.toAdaptive hn q out).abortAlg.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v} =
      ENNReal.ofReal (∑ c, (C.coins c).toReal *
        prob {g | P ((D.toAdaptive hn q out).liftCW C
          ((D.toAdaptive hn q out).toKindAlg.emb C H c m (fMid q m g)).1)}
          (D.run C.toPureEnv (H, c))) := by
  classical
  rw [(D.withinBudgetAt_toAdaptive hn q out C H hB).toOuterMeasure_outLaw_abortAlg,
    D.toOuterMeasure_outLaw_toAdaptive hn q out C H hB]

end Distinguisher

end GordieHowe.Quantum
