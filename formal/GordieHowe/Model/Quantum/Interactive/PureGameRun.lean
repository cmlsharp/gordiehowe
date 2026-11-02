-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.PureGame
public import GordieHowe.Model.Quantum.Interactive.PureRun
public import GordieHowe.Model.Quantum.Interactive.Adaptive

@[expose] public section

/-!
# The mixed game of an adversary with one-operator Kraus maps is pure

For a kind algorithm (`Quantum.KindAlg`) whose Kraus maps have one operator each
(`KrausMap.PureAt`) and whose initial state is the projector onto a vector, the mixed game without
the request measurement (`KindAlg.mgRun … false`, `GordieHowe/Model/Quantum/Interactive/Pure.lean`)
is the projector onto the vector of the alternating run of the operators (with the identity on the
logs) and the slot permutations (`KindAlg.evPerm`), requests included.

- `KindAlg.liftMat U k`: the operator `U k` with the identity on the logs; `KindAlg.pureVec`: the
  vectors of the run; `KindAlg.mgU_eq_proj`, `KindAlg.mgRun_false_eq_proj_pureVec`: the mixed game is
  their projector; `KindAlg.mgAccept_eq_pureVec`: the acceptance probability of the mixed game is
  the Born weight of the final vector on the accepting outcomes.
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder

namespace GordieHowe.Quantum

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O)
  (U : StepIdx A.slots A.post → Matrix (DReg A.W A.width X Y Req Resp)
    (DReg A.W A.width X Y Req Resp) ℂ)

/-- **The operator `U k` with the identity on the logs**, on the game registers. -/
def liftMat (k : StepIdx A.slots A.post) : Matrix A.G A.G ℂ :=
  (U k ⊗ₖ (1 : Matrix (LogReg Req A.slots) (LogReg Req A.slots) ℂ)).submatrix splitLogs splitLogs

/-- The operator number `k` with the identity on the logs, indexed by `ℕ` (the identity from
`slots + post + 1` on). -/
def liftMatAt (k : ℕ) : Matrix A.G A.G ℂ :=
  if h : k < A.slots + A.post + 1 then A.liftMat U ⟨k, h⟩ else 1

theorem liftMatAt_of_lt {k : ℕ} (h : k < A.slots + A.post + 1) :
    A.liftMatAt U k = A.liftMat U ⟨k, h⟩ :=
  dif_pos h

theorem liftG_proj_of_pureAt {k : StepIdx A.slots A.post} {r₀ : A.R} (h : (A.step k).PureAt r₀ (U k))
    (v : QState A.G) : (A.liftG k) (proj v) = proj (matApply (A.liftMat U k) v) := by
  unfold liftG liftMat
  rw [((h.tensorId (LogReg Req A.slots)).reindex splitLogs.symm).apply_proj]
  rfl

/-- **A pure initial state with blank logs**: an initial state `|φ⟩⟨φ|` gives the mixed game the
initial state `|φ⟩⟨φ|` with blank logs (`liftLogs`). -/
theorem mgInitM_mat_of_proj {φ : QState (DReg A.W A.width X Y Req Resp)} (h : A.init.mat = proj φ) :
    A.mgInitM.mat = proj (A.liftLogs φ) := by
  ext r s
  simp only [mgInitM, MState.reindex, MState.tensorKet_mat, submatrix_apply, Equiv.symm_symm,
    kroneckerMap_apply, h, proj, vecMulVec_apply, liftLogs_apply, Matrix.single_apply]
  by_cases hr : (splitLogs r).2 = fun _ => none <;> by_cases hs : (splitLogs s).2 = fun _ => none
  · simp [hr, hs]
  · have hs' : ¬ (fun _ => none) = (splitLogs s).2 := fun h => hs h.symm
    simp [hr, hs, hs']
  · have hr' : ¬ (fun _ => none) = (splitLogs r).2 := fun h => hr h.symm
    simp [hr, hs, hr']
  · have hr' : ¬ (fun _ => none) = (splitLogs r).2 := fun h => hr h.symm
    simp [hr, hs, hr']

variable [AddGroup Y] {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St)

/-- **The vectors of the run** from the vector `ψ₀` of the game registers: the operator number `k`
(`liftMatAt`), then the slot permutation number `k` (`evPerm`). -/
noncomputable def pureVec (ψ₀ : QState A.G) (ω : Ω) : ℕ → QState A.G
  | 0 => ψ₀
  | k + 1 => permOp (A.evPerm E ω k) (matApply (A.liftMatAt U k) (pureVec ψ₀ ω k))

variable {A U}

theorem gK_proj {r₀ : StepIdx A.slots A.post → A.R} (hU : ∀ k, (A.step k).PureAt (r₀ k) (U k))
    (k : ℕ) (v : QState A.G) : A.gK k (proj v) = proj (matApply (A.liftMatAt U k) v) := by
  unfold gK liftMatAt
  split_ifs with h
  · exact liftG_proj_of_pureAt A U (hU _) v
  · congr 1
    ext i
    simp [matApply_apply, Matrix.one_apply]

/-- **The mixed game without the request measurement, before the operator number `k`**, is the
projector onto `pureVec k` from the initial vector `ψ₀`. -/
theorem mgU_eq_proj {r₀ : StepIdx A.slots A.post → A.R} (hU : ∀ k, (A.step k).PureAt (r₀ k) (U k))
    {ψ₀ : QState A.G} (hinit : A.mgInitM.mat = proj ψ₀) (ω : Ω) :
    ∀ k, A.mgU E ω k = proj (A.pureVec U E ψ₀ ω k) := by
  intro k
  induction k with
  | zero => exact hinit
  | succ k ih =>
    rw [mgU, ih, gK_proj hU, submatrix_proj]
    rfl

/-- **The mixed game without the request measurement is the projector onto the final vector**:
`liftMatAt (slots + post)` applied to `pureVec (slots + post)`. -/
theorem mgRun_false_eq_proj_pureVec {r₀ : StepIdx A.slots A.post → A.R}
    (hU : ∀ k, (A.step k).PureAt (r₀ k) (U k)) {ψ₀ : QState A.G}
    (hinit : A.mgInitM.mat = proj ψ₀) (ω : Ω) :
    A.mgRun E ω false = proj (matApply (A.liftMatAt U (A.slots + A.post))
      (A.pureVec U E ψ₀ ω (A.slots + A.post))) := by
  rw [mgRun_false_eq, mgU_eq_proj E hU hinit, gK_proj hU]

/-- **The acceptance probability of the mixed game is the Born weight of the final vector** on the
outcomes with output `o`. -/
theorem mgAccept_eq_pureVec [DecidableEq O] {r₀ : StepIdx A.slots A.post → A.R}
    (hU : ∀ k, (A.step k).PureAt (r₀ k) (U k)) {ψ₀ : QState A.G}
    (hinit : A.mgInitM.mat = proj ψ₀) (o : O) (ω : Ω) :
    A.mgAccept E o ω true = ∑ r : A.G, if A.out r.1.1 = o then
      ‖matApply (A.liftMatAt U (A.slots + A.post)) (A.pureVec U E ψ₀ ω (A.slots + A.post)) r‖ ^ 2
      else 0 := by
  rw [mgAccept_deph, mgAccept, mgRun_false_eq_proj_pureVec E hU hinit]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs
  · exact proj_apply _ r
  · rfl

end KindAlg

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

/-- A vector of the adversary's registers with the query counter at `0`. -/
noncomputable def cntVec (φ : QState (DReg A.W A.width X Y Req Resp)) :
    QState (DReg A.CntW A.width X Y Req Resp) :=
  relabel A.cntSplit.symm (tensorKet φ 0)

/-- **A pure initial state with the counter at `0`**: the initial state `|φ⟩⟨φ|` gives the
adversary with its counter the initial state `|φ, 0⟩⟨φ, 0|`. -/
theorem toKindAlg_init_mat_of_proj {φ : QState (DReg A.W A.width X Y Req Resp)}
    (h : A.init.mat = proj φ) : A.toKindAlg.init.mat = proj (A.cntVec φ) := by
  ext r s
  change (A.init.mat ⊗ₖ Matrix.single (0 : Fin (A.budget + 2)) 0 1) (A.cntSplit r) (A.cntSplit s) =
    proj (A.cntVec φ) r s
  simp only [h, kroneckerMap_apply, proj, vecMulVec_apply, cntVec, relabel_apply, tensorKet_apply,
    Matrix.single_apply, Equiv.symm_symm]
  by_cases hr : (A.cntSplit r).2 = 0 <;> by_cases hs : (A.cntSplit s).2 = 0
  · simp [hr, hs]
  · have hs' : ¬ (0 : Fin (A.budget + 2)) = (A.cntSplit s).2 := fun h => hs h.symm
    simp [hr, hs, hs']
  · have hr' : ¬ (0 : Fin (A.budget + 2)) = (A.cntSplit r).2 := fun h => hr h.symm
    simp [hr, hs, hr']
  · have hr' : ¬ (0 : Fin (A.budget + 2)) = (A.cntSplit r).2 := fun h => hr h.symm
    simp [hr, hs, hr']

/-- **An adversary whose every slot is a request keeps its Kraus maps with one operator under the
counter**: `toKindAlg`'s map is `U` with the identity on the counter. -/
theorem toKindAlg_step_pureAt_of_kind (hk : ∀ w, A.kind w = true) {k : StepIdx A.slots A.post}
    {r₀ : A.R} {U : Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ}
    (h : (A.step k).PureAt r₀ U) :
    (A.toKindAlg.step k).PureAt r₀
      ((U ⊗ₖ (1 : Matrix (Fin (A.budget + 2)) (Fin (A.budget + 2)) ℂ)).submatrix A.cntSplit
        A.cntSplit) := by
  have hshift : A.cntShift = Equiv.refl _ := by
    ext d <;> simp [cntShift, AlgShape.cntShift, hk]
  have hb : ∀ d, A.inBudget d = true := fun d => by simp [inBudget, AlgShape.inBudget, hk]
  have hdiag : (Matrix.diagonal fun d => if A.inBudget d then (1 : ℂ) else 0) = 1 := by
    simp [hb, Matrix.diagonal_one]
  have hU := (h.tensorId (Fin (A.budget + 2))).reindex A.cntSplit.symm
  simp only [Equiv.symm_symm] at hU
  refine ⟨?_, fun r hr => ?_⟩
  · by_cases hks : (k : ℕ) < A.slots
    · rw [A.toKindAlg_step_of_lt hks]
      simp [KrausMap.permConj, KrausMap.restrict, hU.op_eq, hshift, hdiag]
    · rw [A.toKindAlg_step_of_not_lt hks]
      exact hU.op_eq
  · by_cases hks : (k : ℕ) < A.slots
    · rw [A.toKindAlg_step_of_lt hks]
      simp only [KrausMap.permConj, KrausMap.restrict]
      rw [hU.op_ne r hr]
      ext i j
      simp only [Matrix.zero_apply, mul_zero, submatrix_apply]
    · rw [A.toKindAlg_step_of_not_lt hks]
      exact hU.op_ne r hr

end AdaptiveIAlg

end GordieHowe.Quantum
