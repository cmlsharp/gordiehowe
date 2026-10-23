-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Output
public import GordieHowe.Model.Quantum.Interactive.Test

@[expose] public section

/-!
# Interactive adversaries without requests whose Kraus maps are unitary

The semantics of an interactive adversary (`IAlg.compose`, `GordieHowe/Model/Quantum/Interactive/Basic.lean`) is
a mixed run. For an adversary that makes no request (every slot of its schedule is a query slot)
and whose Kraus maps have one operator each (`KrausMap.PureAt`), the run from a pure initial state
stays pure: on every oracle `H` the final state is the projector onto the vector of the
alternating run of the operators and the queries to `H` (`IAlg.pureRun`). This file proves it for
the kind algorithm of the adversary (`KindAlg.mgRun_false_of_pure`, `IAlg.pureRun_toKindAlg`).

- `KrausMap.PureAt K r₀ U`: `K` has the operator `U` at the index `r₀` and zero operators at the
  others, so `K ρ = U ρ U*` (`PureAt.apply`); preserved by `tensorId`, `reindex`, `permConj`,
  `comp`, `embedIdx`, and satisfied by `ofPerm`.
- `KindAlg.mgRun_false_of_pure`: the mixed game without the request measurement is the projector
  onto the lifted pure run (blank logs).
- `IAlg.outLaw_composeOut_some`: the output law of `composeOut f` at `o` is the coin-average of
  the diagonal of the mixed game with measured requests on the registers whose composed register
  `f` reads as `o`.
- `IAlg.pureRun_toKindAlg`, `IAlg.toKindAlg_step_pureAt`, `IAlg.toKindAlg_init_of_proj`: for an
  adversary without requests, the pure run, the Kraus maps with one operator and the pure initial
  state carry over to its kind algorithm `toKindAlg`, whose slot counter reads `cntFinal` after
  the slots.
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder

namespace GordieHowe.Quantum

/-! ### Projectors -/

section Proj

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The projector `|ψ⟩⟨ψ|` onto a vector, as a matrix. -/
noncomputable def proj (ψ : QState ι) : Matrix ι ι ℂ :=
  vecMulVec (fun i => ψ i) (fun i => star (ψ i))

/-- A matrix applied to a vector. -/
noncomputable def matApply (U : Matrix κ ι ℂ) (ψ : QState ι) : QState κ :=
  WithLp.toLp 2 (U *ᵥ fun i => ψ i)

theorem matApply_apply (U : Matrix κ ι ℂ) (ψ : QState ι) (k : κ) :
    matApply U ψ k = ∑ i, U k i * ψ i := rfl

theorem mul_proj_mul (U : Matrix κ ι ℂ) (ψ : QState ι) :
    U * proj ψ * Uᴴ = proj (matApply U ψ) := by
  ext a b
  simp only [proj, matApply, mul_apply, vecMulVec_apply, conjTranspose_apply, mulVec, dotProduct,
    PiLp.toLp_apply, Finset.sum_mul, star_sum, star_mul', Finset.mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

theorem proj_apply (ψ : QState ι) (i : ι) : (proj ψ i i).re = ‖ψ i‖ ^ 2 := by
  simp only [proj, vecMulVec_apply, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re,
    RCLike.star_def]

theorem submatrix_proj (π : Equiv.Perm ι) (ψ : QState ι) :
    (proj ψ).submatrix π.symm π.symm = proj (permOp π ψ) := by
  ext a b
  simp [proj, permOp_apply, vecMulVec_apply]

end Proj

/-! ### Kraus maps with one operator -/

namespace KrausMap

variable {R R' ι κ : Type*} [Fintype R] [Fintype R'] [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- **A Kraus map with one operator**: the operator `U` at the index `r₀`, the zero operator at
every other index. Such a map is `ρ ↦ U ρ U*` (`PureAt.apply`). -/
structure PureAt (K : KrausMap R ι κ) (r₀ : R) (U : Matrix κ ι ℂ) : Prop where
  op_eq : K.op r₀ = U
  op_ne : ∀ r ≠ r₀, K.op r = 0

theorem PureAt.apply {K : KrausMap R ι κ} {r₀ : R} {U : Matrix κ ι ℂ} (h : K.PureAt r₀ U)
    (ρ : Matrix ι ι ℂ) : K ρ = U * ρ * Uᴴ := by
  rw [KrausMap.apply, Finset.sum_eq_single r₀ (fun r _ hr => by simp [h.op_ne r hr]) (by simp),
    h.op_eq]

theorem PureAt.apply_proj {K : KrausMap R ι κ} {r₀ : R} {U : Matrix κ ι ℂ} (h : K.PureAt r₀ U)
    (ψ : QState ι) : K (proj ψ) = proj (matApply U ψ) := by
  rw [h.apply, mul_proj_mul]

theorem PureAt.tensorId {K : KrausMap R ι ι} {r₀ : R} {U : Matrix ι ι ℂ} (h : K.PureAt r₀ U)
    (A : Type*) [Fintype A] [DecidableEq A] :
    (K.tensorId A).PureAt r₀ (U ⊗ₖ (1 : Matrix A A ℂ)) where
  op_eq := by simp [KrausMap.tensorId, h.op_eq]
  op_ne r hr := by simp [KrausMap.tensorId, h.op_ne r hr]

theorem PureAt.reindex {K : KrausMap R ι ι} {r₀ : R} {U : Matrix ι ι ℂ} (h : K.PureAt r₀ U)
    {κ' : Type*} [Fintype κ'] [DecidableEq κ'] (e : ι ≃ κ') :
    (K.reindex e).PureAt r₀ (U.submatrix e.symm e.symm) where
  op_eq := by simp [KrausMap.reindex, h.op_eq]
  op_ne r hr := by simp [KrausMap.reindex, h.op_ne r hr]

theorem PureAt.permConj {K : KrausMap R ι ι} {r₀ : R} {U : Matrix ι ι ℂ} (h : K.PureAt r₀ U)
    (σ τ : Equiv.Perm ι) : (K.permConj σ τ).PureAt r₀ (U.submatrix τ.symm σ) where
  op_eq := by simp [KrausMap.permConj, h.op_eq]
  op_ne r hr := by simp [KrausMap.permConj, h.op_ne r hr]

theorem PureAt.comp {K₂ : KrausMap R' ι ι} {K₁ : KrausMap R ι ι} {r₁ : R} {r₂ : R'}
    {U₁ U₂ : Matrix ι ι ℂ} (h₂ : K₂.PureAt r₂ U₂) (h₁ : K₁.PureAt r₁ U₁) :
    (K₂.comp K₁).PureAt (r₁, r₂) (U₂ * U₁) where
  op_eq := by simp [KrausMap.comp, h₁.op_eq, h₂.op_eq]
  op_ne p hp := by
    simp only [KrausMap.comp]
    by_cases h1 : p.1 = r₁
    · have h2 : p.2 ≠ r₂ := fun h2 => hp (Prod.ext h1 h2)
      rw [h₂.op_ne _ h2, Matrix.zero_mul]
    · rw [h₁.op_ne _ h1, Matrix.mul_zero]

theorem PureAt.embedIdx {K : KrausMap R ι ι} {r₀ : R} {U : Matrix ι ι ℂ} (h : K.PureAt r₀ U)
    (f : R ↪ R') : (K.embedIdx f).PureAt (f r₀) U where
  op_eq := by
    classical
    change (if h' : ∃ r, f r = f r₀ then K.op h'.choose else 0) = U
    have hex : ∃ r, f r = f r₀ := ⟨r₀, rfl⟩
    simp only [hex, ↓reduceDIte]
    rw [← h.op_eq]
    congr 1
    exact f.injective (Exists.choose_spec (⟨r₀, rfl⟩ : ∃ r, f r = f r₀))
  op_ne r' hr' := by
    classical
    change (if h' : ∃ r, f r = r' then K.op h'.choose else 0) = 0
    split_ifs with h'
    · refine h.op_ne _ fun e => hr' ?_
      rw [← e, h'.choose_spec]
    · rfl

theorem pureAt_ofPerm (π : Equiv.Perm ι) :
    (KrausMap.ofPerm π).PureAt () ((1 : Matrix ι ι ℂ).submatrix π.symm (Equiv.refl ι)) where
  op_eq := rfl
  op_ne _ hr := absurd rfl hr

end KrausMap

/-- A trace-preserving Kraus family with one operator. -/
theorem KrausChannel.pureAt_toKrausMap {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]
    {K : KrausChannel R ι ι} {r₀ : R} {U : Matrix ι ι ℂ} (h0 : K.op r₀ = U)
    (h1 : ∀ r ≠ r₀, K.op r = 0) : K.toKrausMap.PureAt r₀ U :=
  ⟨h0, h1⟩

/-! ### The mixed game of an adversary with a kind register -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : KindAlg X Y Req Resp O)

/-- A vector of the adversary's registers with blank logs, as a vector of the game registers. -/
noncomputable def liftLogs (v : QState (DReg A.W A.width X Y Req Resp)) : QState A.G :=
  WithLp.toLp 2 fun r => if (splitLogs r).2 = (fun _ => none) then v (splitLogs r).1 else 0

theorem liftLogs_apply (v : QState (DReg A.W A.width X Y Req Resp)) (r : A.G) :
    A.liftLogs v r = if (splitLogs r).2 = (fun _ => none) then v (splitLogs r).1 else 0 := rfl

/-- **The adversary's Kraus map with one operator, on blank logs.** -/
theorem liftG_proj {k : StepIdx A.slots A.post} {r₀ : A.R}
    {U : Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ}
    (h : (A.step k).PureAt r₀ U) (v : QState (DReg A.W A.width X Y Req Resp)) :
    (A.liftG k) (proj (A.liftLogs v)) = proj (A.liftLogs (matApply U v)) := by
  unfold liftG
  rw [((h.tensorId (LogReg Req A.slots)).reindex splitLogs.symm).apply_proj]
  congr 1
  ext r
  rw [matApply_apply, liftLogs_apply, ← splitLogs.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.symm_symm, submatrix_apply, Equiv.apply_symm_apply, kroneckerMap_apply,
    liftLogs_apply]
  by_cases hr : (splitLogs r).2 = fun _ => none
  · simp only [hr, ↓reduceIte, matApply_apply]
    refine sum_congr rfl fun d _ => ?_
    rw [Finset.sum_eq_single (fun _ => none) (fun lg _ hlg => by simp [hlg]) (by simp)]
    simp [hr, one_apply]
  · simp only [hr, ↓reduceIte]
    refine sum_eq_zero fun d _ => sum_eq_zero fun lg _ => ?_
    by_cases hlg : lg = fun _ => none
    · subst hlg
      simp [one_apply, hr]
    · simp [hlg]

variable [AddGroup Y] {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St)

omit [AddGroup Y] in
theorem copyG_eq_refl (hkind : ∀ w, A.kind w = false) (k : Fin A.slots) :
    A.copyG k = Equiv.refl _ :=
  Equiv.ext fun r => by
    obtain ⟨s, q⟩ := r
    simp [copyG, Equiv.prodCongr_apply, copyPerm_apply, hkind]

omit [AddGroup Y] [OracleState St X Y] in
theorem respG_eq_refl (hkind : ∀ w, A.kind w = false) (ω : Ω) (k : Fin A.slots) :
    A.respG E ω k = Equiv.refl _ :=
  Equiv.ext fun r => by
    obtain ⟨s, q⟩ := r
    simp [respG, Equiv.prodCongr_apply, respondPerm_apply, hkind]

/-- The oracle in force on blank logs. -/
def blankOracle (ω : Ω) : X → Y :=
  E.oracle ω (fun _ => none : LogReg Req A.slots)

theorem permOp_oraclePerm_liftLogs (hkind : ∀ w, A.kind w = false) (ω : Ω)
    (v : QState (DReg A.W A.width X Y Req Resp)) :
    permOp (E.oraclePerm A.kind ω) (A.liftLogs v) =
      A.liftLogs (permOp (queryPerm (A.blankOracle E ω)) v) := by
  ext r
  obtain ⟨⟨w, req, resp, lg⟩, qs⟩ := r
  by_cases hlg : lg = fun _ => none
  · subst hlg
    simp [permOp_apply, liftLogs_apply, Env.oraclePerm, queryPermOf, queryPerm, hkind, splitLogs,
      blankOracle]
  · simp [permOp_apply, liftLogs_apply, Env.oraclePerm, queryPermOf, splitLogs, hlg]

theorem permOp_postG_liftLogs (ω : Ω) (v : QState (DReg A.W A.width X Y Req Resp)) :
    permOp (A.postG E ω) (A.liftLogs v) =
      A.liftLogs (permOp (queryPerm (A.blankOracle E ω)) v) := by
  ext r
  obtain ⟨⟨w, req, resp, lg⟩, qs⟩ := r
  by_cases hlg : lg = fun _ => none
  · subst hlg
    simp [permOp_apply, liftLogs_apply, postG, queryPermOf, queryPerm, splitLogs, blankOracle]
  · simp [permOp_apply, liftLogs_apply, postG, queryPermOf, splitLogs, hlg]

variable (U : StepIdx A.slots A.post → Matrix (DReg A.W A.width X Y Req Resp)
  (DReg A.W A.width X Y Req Resp) ℂ) (H : X → Y)

/-- A query slot of the pure run: the operator, then the query to `H`. -/
noncomputable def pureSlot (v : QState (DReg A.W A.width X Y Req Resp)) (k : Fin A.slots) :
    QState (DReg A.W A.width X Y Req Resp) :=
  permOp (queryPerm H) (matApply (U (slotStep k)) v)

/-- A post batch of the pure run: the operator, then the query to `H`. -/
noncomputable def purePost (v : QState (DReg A.W A.width X Y Req Resp)) (b : Fin A.post) :
    QState (DReg A.W A.width X Y Req Resp) :=
  permOp (queryPerm H) (matApply (U (postStep b)) v)

/-- **The pure run** of operators `U` with the oracle `H`: each slot is the operator and a query,
each post batch the same, then the last operator. -/
noncomputable def pureRun (ψ : QState (DReg A.W A.width X Y Req Resp)) :
    QState (DReg A.W A.width X Y Req Resp) :=
  matApply (U lastStep) ((List.finRange A.post).foldl (A.purePost U H)
    ((List.finRange A.slots).foldl (A.pureSlot U H) ψ))

/-- **The mixed game of an adversary without requests whose Kraus maps have one operator is
pure**: from the projector onto `ψ`, the mixed game without the request measurement ends in the
projector onto the lifted pure run with the oracle in force on blank logs. -/
theorem mgRun_false_of_pure (hkind : ∀ w, A.kind w = false)
    (hU : ∀ k, ∃ r₀, (A.step k).PureAt r₀ (U k)) (ψ : QState (DReg A.W A.width X Y Req Resp))
    (hinit : A.init.mat = proj ψ) (ω : Ω) :
    A.mgRun E ω false = proj (A.liftLogs (A.pureRun U (A.blankOracle E ω) ψ)) := by
  set H := A.blankOracle E ω
  have hstep : ∀ k v, (A.liftG k) (proj (A.liftLogs v)) = proj (A.liftLogs (matApply (U k) v)) :=
    fun k v => by
      obtain ⟨r₀, h⟩ := hU k
      exact A.liftG_proj h v
  have hslots : ∀ (l : List (Fin A.slots)) v,
      (Circuit.concat (l.map fun k : Fin A.slots =>
        Circuit.kraus (A.liftG (slotStep k)) (A.eventCirc E ω k false))).run (Equiv.refl _)
          (proj (A.liftLogs v)) = proj (A.liftLogs (l.foldl (A.pureSlot U H) v)) := by
    intro l
    induction l with
    | nil => intro v; rfl
    | cons k l ih =>
      intro v
      rw [List.map_cons, Circuit.run_concat, List.foldl_cons, ← ih]
      congr 1
      simp only [eventCirc, Circuit.run, Bool.false_eq_true, ↓reduceIte, id, KrausMap.ofPerm_apply,
        A.copyG_eq_refl hkind, A.respG_eq_refl E hkind, hstep]
      simp only [Equiv.refl_symm, Equiv.coe_refl, submatrix_id_id, submatrix_proj,
        A.permOp_oraclePerm_liftLogs E hkind]
      rfl
  have hposts : ∀ (l : List (Fin A.post)) v,
      (Circuit.concat (l.map fun b : Fin A.post =>
        Circuit.kraus (A.liftG (postStep b)) (.kraus (KrausMap.ofPerm (A.postG E ω)) .nil))).run
          (Equiv.refl _) (proj (A.liftLogs v)) = proj (A.liftLogs (l.foldl (A.purePost U H) v)) := by
    intro l
    induction l with
    | nil => intro v; rfl
    | cons b l ih =>
      intro v
      rw [List.map_cons, Circuit.run_concat, List.foldl_cons, ← ih]
      congr 1
      simp only [Circuit.run, KrausMap.ofPerm_apply, hstep, submatrix_proj,
        A.permOp_postG_liftLogs E]
      rfl
  have hinit' : A.mgInit = proj (A.liftLogs ψ) := by
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

/-! ### The output law of a composition with a function of its registers -/

namespace IAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] (A : IAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- **The output law of `composeOut f`** is the coin-average of the diagonal of the mixed game
with measured requests on the registers whose composed register `f` reads as `o` (as
`IAlg.outLaw_compose_some`, for any output). -/
theorem outLaw_composeOut_some {O' : Type} [DecidableEq O'] (f : A.toKindAlg.CW C → O')
    (H : X → Y) (o : O') :
    (A.composeOut C f).outLaw H (some o) =
      ENNReal.ofReal (∑ c, (C.coins c).toReal * ∑ r : A.toKindAlg.G,
        if f (A.toKindAlg.emb C H c A.slots r).1 = o then
          (A.toKindAlg.mgRun C.toPureEnv (H, c) true r r).re else 0) := by
  have hpsd := (A.composeOut C f).posSemidef_stage H (A.composeOut C f).depth
  rw [Alg.outLaw]
  refine (map_basisLaw_apply_some (o := o) ..).trans ?_
  have hdiag : ∀ p, 0 ≤ ((A.composeOut C f).final H p p).re := fun p =>
    (Complex.nonneg_iff.1 (hpsd.diag_nonneg (i := p))).1
  have hite : ∀ p, (if some o = some ((A.composeOut C f).out p.1) then
      ENNReal.ofReal ((A.composeOut C f).final H p p).re else 0) =
      ENNReal.ofReal (if o = (A.composeOut C f).out p.1 then
        ((A.composeOut C f).final H p p).re else 0) :=
    fun p => by split_ifs with h1 h2 h2 <;> simp_all
  refine (Finset.sum_congr rfl fun p _ => hite p).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => by split_ifs; exact hdiag p; exact le_rfl]
  congr 1
  rw [composeOut_final, compose_final]
  have hanc : ∀ a : X × Y × Bool, (reprogAnc (Y := Y) (KindAlg.x₀ : X) a a).im = 0 := fun a => by
    simp only [reprogAnc, ancWeight]
    split_ifs <;> simp
  have hstep : ∀ σ : Matrix (QueryReg (A.toKindAlg.CW C) 1 X Y) (QueryReg (A.toKindAlg.CW C) 1 X Y) ℂ,
      (∑ p : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y,
        if o = f p.1.1 then (withAnc KindAlg.x₀ σ p p).re else 0) =
        ∑ q : QueryReg (A.toKindAlg.CW C) 1 X Y, if o = f q.1 then (σ q q).re else 0 := by
    intro σ
    rw [← (ancSplit (A.toKindAlg.CW C) X Y).symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [ancSplit, Equiv.coe_fn_symm_mk, withAnc, Complex.mul_re, hanc, mul_zero, sub_zero]
    split_ifs
    · rw [← Finset.mul_sum, sum_re_reprogAnc, mul_one]
    · simp
  refine (hstep _).trans ?_
  simp only [re_sum_smul_apply]
  have hg : ∀ q : QueryReg (A.toKindAlg.CW C) 1 X Y, ∀ x : ℝ,
      (if o = f q.1 then x else 0) = (if o = f q.1 then 1 else 0) * x :=
    fun q x => by split_ifs <;> simp
  rw [Finset.sum_congr rfl fun q _ => hg q _]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mul_left_comm _ (C.coins c).toReal, ← Finset.mul_sum]
  congr 1
  rw [embed_diag_of_injective (A.toKindAlg.emb_injective C H c A.slots)]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : f (A.toKindAlg.emb C H c A.slots r).1 = o
  · simp [h]
  · simp [h, Ne.symm h]

/-! ### Adversaries without requests whose Kraus maps have one operator -/

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem toKindAlg_kind_eq_false (hsched : ∀ j, A.sched j = false) (w : A.toKindAlg.W) :
    A.toKindAlg.kind w = false := by
  change A.cntKind w = false
  unfold cntKind
  split_ifs <;> simp [hsched]

/-- A vector of the adversary's registers with the slot counter at `c`. -/
noncomputable def liftCnt (v : QState (DReg A.W A.width X Y Req Resp)) (c : Fin (A.slots + 1)) :
    QState (DReg (A.W × Fin (A.slots + 1)) A.width X Y Req Resp) :=
  WithLp.toLp 2 fun r => if (A.cntSplit r).2 = c then v (A.cntSplit r).1 else 0

/-- The operator of a Kraus map of `toKindAlg`, from the operator `U` of `A`'s Kraus map. -/
noncomputable def cntMat
    (U : Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ)
    (k : StepIdx A.slots A.post) :
    Matrix (DReg (A.W × Fin (A.slots + 1)) A.width X Y Req Resp)
      (DReg (A.W × Fin (A.slots + 1)) A.width X Y Req Resp) ℂ :=
  ((U ⊗ₖ (1 : Matrix (Fin (A.slots + 1)) (Fin (A.slots + 1)) ℂ)).submatrix A.cntSplit
    A.cntSplit).submatrix (A.cntPerm k).symm (Equiv.refl _)

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem toKindAlg_step_pureAt {k : StepIdx A.slots A.post} {r₀ : A.R}
    {U : Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ}
    (h : (A.step k).PureAt r₀ U) : (A.toKindAlg.step k).PureAt r₀ (A.cntMat U k) := by
  exact ((h.tensorId (Fin (A.slots + 1))).reindex A.cntSplit.symm).permConj (Equiv.refl _)
    (A.cntPerm k)

/-- The counter after the Kraus map `k`. -/
def cntNext (k : StepIdx A.slots A.post) (c : Fin (A.slots + 1)) : Fin (A.slots + 1) :=
  if (k : ℕ) < A.slots then finRotate _ c else c

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem cntSplit_cntPerm_symm (k : StepIdx A.slots A.post)
    (r : DReg (A.W × Fin (A.slots + 1)) A.width X Y Req Resp) {c : Fin (A.slots + 1)} :
    (A.cntSplit ((A.cntPerm k).symm r)).1 = (A.cntSplit r).1 ∧
      ((A.cntSplit ((A.cntPerm k).symm r)).2 = c ↔ (A.cntSplit r).2 = A.cntNext k c) := by
  obtain ⟨⟨⟨w, cr⟩, req, resp⟩, qs⟩ := r
  unfold cntPerm cntNext
  split_ifs with hk
  · refine ⟨rfl, ?_⟩
    simp only [cntSplit, Equiv.coe_fn_mk, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map,
      Equiv.refl_symm, Equiv.refl_apply]
    constructor
    · intro h
      rw [← h, Equiv.apply_symm_apply]
    · intro h
      rw [h, Equiv.symm_apply_apply]
  · exact ⟨rfl, Iff.rfl⟩

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem matApply_cntMat
    (U : Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ)
    (k : StepIdx A.slots A.post) (v : QState (DReg A.W A.width X Y Req Resp))
    (c : Fin (A.slots + 1)) :
    matApply (A.cntMat U k) (A.liftCnt v c) = A.liftCnt (matApply U v) (A.cntNext k c) := by
  ext r
  obtain ⟨h1, h2⟩ := A.cntSplit_cntPerm_symm k r (c := c)
  rw [matApply_apply]
  refine (Fintype.sum_equiv A.cntSplit _ (fun p => A.cntMat U k r (A.cntSplit.symm p) *
    A.liftCnt v c (A.cntSplit.symm p)) fun i => by simp).trans ?_
  rw [Fintype.sum_prod_type]
  simp only [cntMat, submatrix_apply, Equiv.refl_apply, Equiv.apply_symm_apply, kroneckerMap_apply,
    liftCnt, PiLp.toLp_apply]
  rw [h1]
  by_cases hc : (A.cntSplit r).2 = A.cntNext k c
  · have hc' := h2.2 hc
    simp only [hc, ↓reduceIte, matApply_apply]
    refine sum_congr rfl fun d _ => ?_
    rw [Finset.sum_eq_single c (fun c' _ hc'' => by simp [hc'']) (by simp)]
    simp [hc', one_apply]
  · have hc' : ¬ (A.cntSplit ((A.cntPerm k).symm r)).2 = c := fun h => hc (h2.1 h)
    simp only [hc, ↓reduceIte]
    refine sum_eq_zero fun d _ => sum_eq_zero fun c' _ => ?_
    by_cases hcc : c' = c
    · subst hcc
      simp [one_apply, hc']
    · simp [hcc]

omit [Nonempty X] [Nonempty Y] in
theorem permOp_queryPerm_liftCnt (H : X → Y) (v : QState (DReg A.W A.width X Y Req Resp))
    (c : Fin (A.slots + 1)) :
    permOp (queryPerm H) (A.liftCnt v c) = A.liftCnt (permOp (queryPerm H) v) c := by
  ext r
  rfl

variable (U : StepIdx A.slots A.post → Matrix (DReg A.W A.width X Y Req Resp)
  (DReg A.W A.width X Y Req Resp) ℂ) (H : X → Y)

/-- A query slot of the pure run of `A`. -/
noncomputable def pureSlot (v : QState (DReg A.W A.width X Y Req Resp)) (k : Fin A.slots) :
    QState (DReg A.W A.width X Y Req Resp) :=
  permOp (queryPerm H) (matApply (U (slotStep k)) v)

/-- A post batch of the pure run of `A`. -/
noncomputable def purePost (v : QState (DReg A.W A.width X Y Req Resp)) (b : Fin A.post) :
    QState (DReg A.W A.width X Y Req Resp) :=
  permOp (queryPerm H) (matApply (U (postStep b)) v)

/-- **The pure run of `A`** with operators `U` and oracle `H`: each slot is the operator and a
query to `H` on all query pairs, each post batch the same, then the last operator. -/
noncomputable def pureRun (ψ : QState (DReg A.W A.width X Y Req Resp)) :
    QState (DReg A.W A.width X Y Req Resp) :=
  matApply (U lastStep) ((List.finRange A.post).foldl (A.purePost U H)
    ((List.finRange A.slots).foldl (A.pureSlot U H) ψ))

/-- The counter after the slots. -/
def cntFinal : Fin (A.slots + 1) := (finRotate (A.slots + 1))^[A.slots] 0

omit [Nonempty X] [Nonempty Y] in
theorem pureRun_toKindAlg (ψ : QState (DReg A.W A.width X Y Req Resp)) :
    A.toKindAlg.pureRun (fun k => A.cntMat (U k) k) H (A.liftCnt ψ 0) =
      A.liftCnt (A.pureRun U H ψ) A.cntFinal := by
  set F := A.toKindAlg.pureSlot (fun k => A.cntMat (U k) k) H
  set F' := A.toKindAlg.purePost (fun k => A.cntMat (U k) k) H
  have hslots : ∀ (l : List (Fin A.slots)) v c, l.foldl F (A.liftCnt v c) =
      A.liftCnt (l.foldl (A.pureSlot U H) v) ((finRotate (A.slots + 1))^[l.length] c) := by
    intro l
    induction l with
    | nil => intro v c; rfl
    | cons k l ih =>
      intro v c
      have e1 := A.matApply_cntMat (U (slotStep k)) (slotStep k) v c
      have e2 : A.cntNext (slotStep k) c = finRotate _ c := by simp [cntNext]
      rw [e2] at e1
      have hk : F (A.liftCnt v c) k = A.liftCnt (A.pureSlot U H v k) (finRotate _ c) :=
        (congrArg (permOp (queryPerm H)) e1).trans (A.permOp_queryPerm_liftCnt H _ _)
      show List.foldl F (F (A.liftCnt v c) k) l = _
      rw [hk, ih, List.length_cons, Function.iterate_succ_apply]
      rfl
  have hposts : ∀ (l : List (Fin A.post)) v c, l.foldl F' (A.liftCnt v c) =
      A.liftCnt (l.foldl (A.purePost U H) v) c := by
    intro l
    induction l with
    | nil => intro v c; rfl
    | cons b l ih =>
      intro v c
      have e1 := A.matApply_cntMat (U (postStep b)) (postStep b) v c
      have e2 : A.cntNext (postStep b) c = c := by simp [cntNext]
      rw [e2] at e1
      have hb : F' (A.liftCnt v c) b = A.liftCnt (A.purePost U H v b) c :=
        (congrArg (permOp (queryPerm H)) e1).trans (A.permOp_queryPerm_liftCnt H _ _)
      show List.foldl F' (F' (A.liftCnt v c) b) l = _
      rw [hb, ih]
      rfl
  have h1 := hslots (List.finRange A.slots) ψ 0
  rw [List.length_finRange] at h1
  have h2 := hposts (List.finRange A.post) ((List.finRange A.slots).foldl (A.pureSlot U H) ψ)
    ((finRotate (A.slots + 1))^[A.slots] 0)
  have h3 := A.matApply_cntMat (U lastStep) lastStep ((List.finRange A.post).foldl
    (A.purePost U H) ((List.finRange A.slots).foldl (A.pureSlot U H) ψ))
    ((finRotate (A.slots + 1))^[A.slots] 0)
  have e3 : A.cntNext lastStep ((finRotate (A.slots + 1))^[A.slots] 0) =
      (finRotate (A.slots + 1))^[A.slots] 0 := by simp [cntNext]
  rw [e3] at h3
  show matApply (A.cntMat (U lastStep) lastStep) (List.foldl F' (List.foldl F (A.liftCnt ψ 0)
    (List.finRange A.slots)) (List.finRange A.post)) = _
  exact (congrArg (fun z => matApply (A.cntMat (U lastStep) lastStep)
    (List.foldl F' z (List.finRange A.post))) h1).trans
    ((congrArg (matApply (A.cntMat (U lastStep) lastStep)) h2).trans h3)

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem toKindAlg_init_of_proj {ψ : QState (DReg A.W A.width X Y Req Resp)}
    (hinit : A.init.mat = proj ψ) :
    (MState.reindex A.cntSplit.symm (A.init.tensorKet (0 : Fin (A.slots + 1)))).mat =
      proj (A.liftCnt ψ 0) := by
  ext r s
  obtain ⟨⟨⟨w, cr⟩, req, resp⟩, qs⟩ := r
  obtain ⟨⟨⟨w', cs⟩, req', resp'⟩, qs'⟩ := s
  simp only [MState.reindex, MState.tensorKet_mat, Equiv.symm_symm, submatrix_apply, hinit,
    kroneckerMap_apply, proj, vecMulVec_apply, liftCnt, cntSplit, Equiv.coe_fn_mk, PiLp.toLp_apply,
    Matrix.single_apply]
  by_cases h1 : cr = 0 <;> by_cases h2 : cs = 0 <;> simp [h1, h2, eq_comm]

end IAlg

end GordieHowe.Quantum
