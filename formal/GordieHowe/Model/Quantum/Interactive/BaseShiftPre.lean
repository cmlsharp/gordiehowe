-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftBridge
public import GordieHowe.Model.Quantum.Interactive.CircuitSegPerm

@[expose] public section

/-!
# Kraus maps read after a permutation at their input

`KrausMap.RightPerm π K' K`: `K'` is `K` read after the basis permutation `π`, operator by operator.
It passes through reindexings, the identity on a second factor, compositions on the left and with a
basis permutation on the right (conjugating `π`), and the adversary's absorption with a table and
its trace-preserving form.

- `KrausMap.RightPerm`, `RightPerm.apply`, `RightPerm.reindex`, `RightPerm.tensorId`,
  `RightPerm.comp_left`, `RightPerm.comp_ofPerm`, `RightPerm.restrict`, `RightPerm.permConj_left`.
- `AdaptiveIAlg.preTabPerm`, `AdaptiveIAlg.rightPerm_stepTab`, `AdaptiveIAlg.cntKraus_rightPerm`,
  `AdaptiveIAlg.rightPerm_stepTab`, `AdaptiveIAlg.rightPerm_toTPKindAlg`,
  `AdaptiveIAlg.rightPerm_absorbTab_toTP`, `AdaptiveIAlg.rightPerm_absorbTab_toTP_withStep`:
  through the absorption and the trace-preserving form.
-/

open Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

namespace KrausMap

variable {R R' ι κ : Type*} [Fintype R] [Fintype R'] [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- **`K'` is `K` read after the basis permutation `π` at its input**, operator by operator. -/
def RightPerm (π : Equiv.Perm ι) (K' K : KrausMap R ι ι) : Prop :=
  ∀ r a b, K'.op r a b = K.op r a (π b)

namespace RightPerm

variable {π : Equiv.Perm ι} {K' K : KrausMap R ι ι}

/-- **`K'` applied to a matrix is `K` applied to it relabelled by `π`.** -/
theorem apply (h : RightPerm π K' K) (ρ : Matrix ι ι ℂ) :
    K' ρ = K (ρ.submatrix π.symm π.symm) := by
  have hop : ∀ r, K'.op r = (K.permConj π (Equiv.refl ι)).op r := fun r => by
    ext a b
    exact h r a b
  have e : K' ρ = (K.permConj π (Equiv.refl ι)) ρ := by
    simp only [KrausMap.apply, hop]
  rw [e, KrausMap.permConj_apply]
  rfl

/-- **Along a reindexing**, the permutation is conjugated. -/
theorem reindex (h : RightPerm π K' K) (e : ι ≃ κ) :
    RightPerm (e.permCongr π) (K'.reindex e) (K.reindex e) := fun r a b => by
  change K'.op r (e.symm a) (e.symm b) = K.op r (e.symm a) (e.symm (e (π (e.symm b))))
  rw [Equiv.symm_apply_apply]
  exact h r _ _

/-- **With the identity on a second factor.** -/
theorem tensorId (h : RightPerm π K' K) (A : Type*) [Fintype A] [DecidableEq A] :
    RightPerm (π.prodCongr (Equiv.refl A)) (K'.tensorId A) (K.tensorId A) := fun r a b => by
  change (K'.op r ⊗ₖ (1 : Matrix A A ℂ)) a b = (K.op r ⊗ₖ (1 : Matrix A A ℂ)) a (π b.1, b.2)
  simp only [Matrix.kroneckerMap_apply, h r]

/-- **A composition with a Kraus map on the left.** -/
theorem comp_left (h : RightPerm π K' K) (L : KrausMap R' ι ι) :
    RightPerm π (L.comp K') (L.comp K) := fun r a b => by
  change (L.op r.2 * K'.op r.1) a b = (L.op r.2 * K.op r.1) a (π b)
  simp only [Matrix.mul_apply, h r.1]

/-- **A composition with a basis permutation `σ` on the right** conjugates the permutation. -/
theorem comp_ofPerm (h : RightPerm π K' K) (σ : Equiv.Perm ι) :
    RightPerm (σ.trans (π.trans σ.symm)) (K'.comp (KrausMap.ofPerm σ))
      (K.comp (KrausMap.ofPerm σ)) := fun r a b => by
  change (K'.op r.2 * (KrausMap.ofPerm σ).op r.1) a b =
    (K.op r.2 * (KrausMap.ofPerm σ).op r.1) a (σ.symm (π (σ b)))
  have hm : ∀ (M : Matrix ι ι ℂ) (c : ι), (M * (KrausMap.ofPerm σ).op r.1) a c = M a (σ c) :=
    fun M c => by
      rw [Matrix.mul_apply, Finset.sum_eq_single (σ c)]
      · simp [LeftPerm.ofPerm_op_apply]
      · intro d _ hd
        simp [LeftPerm.ofPerm_op_apply, hd]
      · simp
  rw [hm, hm, h r.2, Equiv.apply_symm_apply]

/-- **A projection onto the basis states of `p` after the map.** -/
theorem restrict (h : RightPerm π K' K) (p : ι → Bool) :
    RightPerm π (K'.restrict p) (K.restrict p) := fun r a b => by
  change (Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) * K'.op r) a b =
    (Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) * K.op r) a (π b)
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul, h r]

/-- **A basis permutation `τ` after the map.** -/
theorem permConj_left (h : RightPerm π K' K) (τ : Equiv.Perm ι) :
    RightPerm π (K'.permConj (Equiv.refl ι) τ) (K.permConj (Equiv.refl ι) τ) := fun r a b => by
  change (K'.op r).submatrix τ.symm (Equiv.refl ι) a b =
    (K.op r).submatrix τ.symm (Equiv.refl ι) a (π b)
  simp only [Matrix.submatrix_apply, Equiv.refl_apply, h r]

end RightPerm

end KrausMap

/-! ### Through the absorption with a table and the trace-preserving form -/

namespace AdaptiveIAlg

variable {X Y Req Resp O Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  {shB : AlgShape X Y Req Resp} {B : AdaptiveIAlg shB O} {F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂}

/-- **The permutation at the input of the step of the adversary absorbed with a table**: the
permutation of the adversary's registers, read after the answer of the previous slot
(`afterAtTab`). -/
def preTabPerm (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (tab : B.OuterTab Req₂ Resp₂)
    (k : StepIdx B.slots B.post) (π : Equiv.Perm (DReg B.W B.width X Y Req Resp)) :
    Equiv.Perm (DReg (B.absorbTab F tab).W B.width X Y Req₁ Resp₁) :=
  (B.afterAtTab F k).trans ((tabPerm F tab π).trans (B.afterAtTab F k).symm)

/-- **The steps of the adversary absorbed with a table are read after the permutation** when the
adversary's are (`h`). -/
theorem rightPerm_stepTab
    (st' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp))
    (k : StepIdx B.slots B.post) {π : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (h : KrausMap.RightPerm π (st' k) (B.step k)) (tab : B.OuterTab Req₂ Resp₂) :
    KrausMap.RightPerm (preTabPerm F tab k π) ((B.withStep st').stepTab F k) (B.stepTab F k) := by
  rw [stepTab_eq (B.withStep st') F k, stepTab_eq B F k]
  exact ((((h.tensorId (B.AbsRest (Req' := Req₁) (Resp' := Resp₁))).reindex
    B.absSplit.symm).tensorId
    (B.OuterTab Req₂ Resp₂)).reindex
        ((B.absorb F.base).constSplit (B.OuterTab Req₂ Resp₂)).symm).comp_ofPerm
          (B.afterAtTab F k) |>.comp_left (KrausMap.ofPerm (B.tabLift F (B.setAt F.base k)))

variable {shC : AlgShape X Y Req Resp} {C : AdaptiveIAlg shC O}

theorem cntKraus_rightPerm
    {st' : StepIdx C.slots C.post → KrausMap C.R (DReg C.W C.width X Y Req Resp)
      (DReg C.W C.width X Y Req Resp)} {π : Equiv.Perm (DReg C.W C.width X Y Req Resp)}
    (k : StepIdx C.slots C.post) (h : KrausMap.RightPerm π (st' k) (C.step k)) :
    KrausMap.RightPerm (C.cntPerm π) ((C.withStep st').cntKraus k) (C.cntKraus k) :=
  (h.tensorId (Fin (C.budget + 2))).reindex C.cntSplit.symm

/-- **The trace-preserving form's steps are read after the permutation** when the adversary's are
(`h`), for trace-preserving steps (`hTP'`, `hTP`). -/
theorem rightPerm_toTPKindAlg
    {st' : StepIdx C.slots C.post → KrausMap C.R (DReg C.W C.width X Y Req Resp)
      (DReg C.W C.width X Y Req Resp)} {π : Equiv.Perm (DReg C.W C.width X Y Req Resp)}
    (k : StepIdx C.slots C.post) (h : KrausMap.RightPerm π (st' k) (C.step k))
    (hTP' : (C.withStep st').TracePreserving) (hTP : C.TracePreserving) :
    KrausMap.RightPerm (C.cntPerm π) ((C.withStep st').toTPKindAlg.step k)
      (C.toTPKindAlg.step k) := by
  intro z a b
  simp only [AdaptiveIAlg.toTPKindAlg_step_op, AlgShape.tpStep_op]
  change (C.withStep st').tpOp false k z a b = C.tpOp false k z a (C.cntPerm π b)
  rcases z with r | r | c
  · by_cases hk : (k : ℕ) < C.slots
    · simp only [tpOp_eq, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, Bool.false_eq_true, ↓reduceIte]
      have hk' : (k : ℕ) < (C.withStep st').slots := hk
      simp only [hk', hk, ↓reduceIte]
      exact (((cntKraus_rightPerm k h).restrict C.inBudget).permConj_left C.tpShift) r a b
    · simp only [tpOp_eq, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, Bool.false_eq_true, ↓reduceIte]
      have hk' : ¬ (k : ℕ) < (C.withStep st').slots := hk
      simp only [hk', hk, ↓reduceIte]
      exact cntKraus_rightPerm k h r a b
  · by_cases hk : (k : ℕ) < C.slots
    · simp only [tpOp_eq, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, Bool.false_eq_true, ↓reduceIte]
      have hk' : (k : ℕ) < (C.withStep st').slots := hk
      simp only [hk', hk, ↓reduceIte]
      exact (((cntKraus_rightPerm k h).restrict fun d => !C.inBudget d).permConj_left
        C.endSwap) r a b
    · simp only [tpOp_eq, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, Bool.false_eq_true, ↓reduceIte]
      have hk' : ¬ (k : ℕ) < (C.withStep st').slots := hk
      simp only [hk', hk, ↓reduceIte]
      rfl
  · simp only [tpOp_eq, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, Bool.false_eq_true, ↓reduceIte,
      TracePreserving.haltOp_eq_zero hTP' k,
      TracePreserving.haltOp_eq_zero hTP k,
      Matrix.zero_kronecker]
    rfl

/-- **The trace-preserving form of the adversary absorbed with a table is read after the
permutation** when the adversary's step is (`h`), for trace-preserving adversaries. -/
theorem rightPerm_absorbTab_toTP
    (st' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp))
    (k : StepIdx B.slots B.post) {π : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (h : KrausMap.RightPerm π (st' k) (B.step k)) (hTP' : (B.withStep st').TracePreserving)
    (hTP : B.TracePreserving) (tab : B.OuterTab Req₂ Resp₂) :
    KrausMap.RightPerm ((B.absorbTab F tab).cntPerm (preTabPerm F tab k π))
      (((B.withStep st').absorbTab F tab).toTPKindAlg.step k)
      ((B.absorbTab F tab).toTPKindAlg.step k) :=
  rightPerm_toTPKindAlg (C := B.absorbTab F tab) (st' := (B.withStep st').stepTab F) k
    (rightPerm_stepTab st' k h tab)
    (absorbTab_tracePreserving (B.withStep st') F hTP' tab)
    (absorbTab_tracePreserving B F hTP tab)

/-- **`rightPerm_absorbTab_toTP` with the Kraus maps read through the trace-preserving form of `B`
absorbed with the table**, with `withStep`. -/
theorem rightPerm_absorbTab_toTP_withStep
    (st' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp))
    (k : StepIdx B.slots B.post) {π : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (h : KrausMap.RightPerm π (st' k) (B.step k)) (hTP' : (B.withStep st').TracePreserving)
    (hTP : B.TracePreserving) (tab : B.OuterTab Req₂ Resp₂) :
    KrausMap.RightPerm ((B.absorbTab F tab).cntPerm (preTabPerm F tab k π))
      ((((B.absorbTab F tab).toTPKindAlg).withStep
        ((B.withStep st').absorbTab F tab).toTPKindAlg.step).step k)
      ((B.absorbTab F tab).toTPKindAlg.step k) :=
  rightPerm_absorbTab_toTP st' k h hTP' hTP tab

end AdaptiveIAlg

end GordieHowe.Quantum
