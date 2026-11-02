-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.DensityRun
public import GordieHowe.Model.Quantum.Interactive.CompressedSimReq

@[expose] public section

/-!
# The simulated run of a query algorithm with a passive scratch register

A query algorithm `Q'` whose work register is that of `Q` with a scratch register `Sc`, started at
`Q`'s initial state tensored with a unit vector `u` of the scratch, whose steps act on the vectors
`v ⊗ u` as `Q`'s on `v` (keeping `u`) and whose output does not read the scratch, has the
compressed-oracle simulation `Sim*` of `Q` tensored with `u`, and the same `simLaw`
(`simLaw_eq_of_scratch`).

- `simWork σ`: an equivalence of work registers on the simulation register;
  `simQuery_simWork`: the simulated query commutes with it.
- `tensorVec v u`: the product vector; `controlled_tensorVec`.
-/

open Matrix
open scoped BigOperators ENNReal

namespace GordieHowe.QROM

open GordieHowe.Quantum

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : BitStr I J ≃ B)

/-! ### Product vectors -/

section Tensor

variable {ι L : Type*} [Fintype ι] [Fintype L]

/-- **The product vector** `v ⊗ u`. -/
def tensorVec (v : QState ι) (u : QState L) : QState (ι × L) :=
  WithLp.toLp 2 fun p => v p.1 * u p.2

theorem tensorVec_apply (v : QState ι) (u : QState L) (p : ι × L) :
    tensorVec v u p = v p.1 * u p.2 :=
  rfl

/-- **A unitary controlled by a passive factor acts on product vectors on the first factor.** -/
theorem controlled_tensorVec (U : QState ι ≃ₗᵢ[ℂ] QState ι) (v : QState ι) (u : QState L) :
    controlled (fun _ => U) (tensorVec v u) = tensorVec (U v) u := by
  ext ⟨i, l⟩
  rw [controlled_apply]
  have h : (WithLp.toLp 2 fun i' => tensorVec v u (i', l) : QState ι) = u l • v := by
    ext i'
    simp only [tensorVec_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [h, LinearIsometryEquiv.map_smul, tensorVec_apply, PiLp.smul_apply, smul_eq_mul, mul_comm]

end Tensor

/-! ### Equivalences of the work register -/

section Work

variable {W W' : Type} [Fintype W] [DecidableEq W] [Fintype W'] [DecidableEq W'] {t : ℕ}

/-- An equivalence of the work registers, on the simulation register. -/
def simWork (σ : W ≃ W') : SimRegister W I J m t ≃ SimRegister W' I J m t :=
  (σ.prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _)

theorem simWork_apply (σ : W ≃ W') (b : SimRegister W I J m t) :
    simWork (I := I) (J := J) (m := m) (t := t) σ b = ((σ b.1.1, b.1.2), b.2) :=
  rfl

theorem simWork_symm (σ : W ≃ W') :
    (simWork (I := I) (J := J) (m := m) (t := t) σ).symm = simWork σ.symm :=
  Equiv.ext fun _ => rfl

/-- **A kernel operator along an equivalence whose kernel it carries.** -/
theorem kernelOp_relabel {κ κ' : Type} [Fintype κ] [Fintype κ'] (π : κ ≃ κ') {K : κ → κ → ℂ}
    {K' : κ' → κ' → ℂ} (hK : ∀ a b, K' (π a) (π b) = K a b) (v : QState κ) :
    kernelOp K' (relabel π v) = relabel π (kernelOp K v) := by
  ext i
  rw [kernelOp_apply, relabel_apply, kernelOp_apply, ← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [relabel_apply, Equiv.symm_apply_apply, ← hK, Equiv.apply_symm_apply]

theorem hadamardKernel_simWork (σ : W ≃ W') (b' b : SimRegister W I J m t) :
    hadamardKernel W' t (simWork σ b') (simWork σ b) = hadamardKernel W t b' b := by
  simp only [hadamardKernel, simWork_apply, σ.injective.eq_iff, qIn, qAns]

theorem decKernel_simWork (σ : W ≃ W') (b' b : SimRegister W I J m t) :
    decKernel e W' t (simWork σ b') (simWork σ b) = decKernel e W t b' b := by
  simp only [decKernel, simWork_apply, Prod.mk.injEq, σ.injective.eq_iff, qIn]
  exact if_congr Prod.ext_iff.symm rfl rfl

theorem phaseKernel_simWork (σ : W ≃ W') (b' b : SimRegister W I J m t) :
    phaseKernel e W' t (simWork σ b') (simWork σ b) = phaseKernel e W t b' b := by
  simp only [phaseKernel, Equiv.apply_eq_iff_eq]
  rfl

/-- **The simulated query commutes with an equivalence of the work registers.** -/
theorem simQuery_simWork (σ : W ≃ W') (v : QState (SimRegister W I J m t)) :
    simQuery e W' t (relabel (simWork σ) v) = relabel (simWork σ) (simQuery e W t v) := by
  simp only [simQuery, compressedOracle, ContinuousLinearMap.comp_apply]
  rw [hadamard_eq_kernelOp, hadamard_eq_kernelOp, decOp_eq_kernelOp, decOp_eq_kernelOp,
    phaseOp_eq_kernelOp, phaseOp_eq_kernelOp,
    kernelOp_relabel _ (hadamardKernel_simWork σ), kernelOp_relabel _ (decKernel_simWork e σ),
    kernelOp_relabel _ (phaseKernel_simWork e σ), kernelOp_relabel _ (decKernel_simWork e σ),
    kernelOp_relabel _ (hadamardKernel_simWork σ)]

end Work

/-! ### A passive scratch register -/

section Scratch

variable {O : Type} {t : ℕ} (Q Q' : QueryAlg (Bits m) (BitStr I J) t O) {Sc : Type} [Fintype Sc]
  [DecidableEq Sc] (σ : Q'.W ≃ Q.W × Sc) (u : QState Sc)

/-- The query registers of `Q'` as those of `Q` and the scratch. -/
def qSplit : QueryReg Q'.W 1 (Bits m) (BitStr I J) ≃ QueryReg Q.W 1 (Bits m) (BitStr I J) × Sc where
  toFun p := (((σ p.1).1, p.2), (σ p.1).2)
  invFun p := (σ.symm (p.1.1, p.2), p.1.2)
  left_inv p := by simp
  right_inv p := by simp

/-- **A vector of `Q`'s query registers tensored with `u`**, on `Q'`'s. -/
noncomputable def qEmb (w : QState (QueryReg Q.W 1 (Bits m) (BitStr I J))) :
    QState (QueryReg Q'.W 1 (Bits m) (BitStr I J)) :=
  relabel (qSplit Q Q' σ).symm (tensorVec w u)

/-- The simulation registers of `Q'` as those of `Q` and the scratch. -/
def sSplit : SimRegister Q'.W I J m t ≃ SimRegister Q.W I J m t × Sc :=
  (simWork σ).trans (wsSplit Q.W Sc)

/-- **A vector of `Q`'s simulation registers tensored with `u`**, on `Q'`'s. -/
noncomputable def sEmb (v : QState (SimRegister Q.W I J m t)) : QState (SimRegister Q'.W I J m t) :=
  relabel (sSplit Q Q' σ).symm (tensorVec v u)

theorem sEmb_apply (v : QState (SimRegister Q.W I J m t)) (b : SimRegister Q'.W I J m t) :
    sEmb Q Q' σ u v b = v (((σ b.1.1).1, b.1.2), b.2) * u (σ b.1.1).2 :=
  rfl

theorem qEmb_apply (w : QState (QueryReg Q.W 1 (Bits m) (BitStr I J)))
    (p : QueryReg Q'.W 1 (Bits m) (BitStr I J)) :
    qEmb Q Q' σ u w p = w ((σ p.1).1, p.2) * u (σ p.1).2 :=
  rfl

variable (hinit : Q'.init = qEmb Q Q' σ u Q.init)
  (hstep : ∀ k w, Q'.step k (qEmb Q Q' σ u w) = qEmb Q Q' σ u (Q.step k w))

include hinit in
theorem simInit_scratch : simInit e Q' = sEmb Q Q' σ u (simInit e Q) := by
  ext b
  rw [sEmb_apply]
  simp only [simInit, hinit, qEmb_apply]
  ring

include hstep in
theorem simStep_scratch (k : ℕ) (v : QState (SimRegister Q.W I J m t)) :
    simStep Q' k (sEmb Q Q' σ u v) = sEmb Q Q' σ u (simStep Q k v) := by
  ext b
  rw [sEmb_apply]
  simp only [simStep]
  rw [controlled_apply, controlled_apply]
  by_cases hk : k < t + 1
  · simp only [OracleAlg.stepAt, hk, dif_pos, QueryAlg.toOracleAlg]
    have h : (WithLp.toLp 2 fun i' => sEmb Q Q' σ u v (i', b.2) :
        QState (QueryReg Q'.W 1 (Bits m) (BitStr I J))) =
        qEmb Q Q' σ u (WithLp.toLp 2 fun i' => v (i', b.2)) := by
      ext p
      rfl
    rw [h, hstep, qEmb_apply]
  · simp only [OracleAlg.stepAt, hk, dif_neg, not_false_eq_true]
    rfl

theorem simQuery_scratch (v : QState (SimRegister Q.W I J m t)) :
    simQuery e Q'.W t (sEmb Q Q' σ u v) = sEmb Q Q' σ u (simQuery e Q.W t v) := by
  have h1 : sEmb Q Q' σ u v = relabel (simWork σ.symm)
      (relabel (wsSplit Q.W Sc).symm (tensorVec v u)) := by
    ext b
    rfl
  have h2 : sEmb Q Q' σ u (simQuery e Q.W t v) = relabel (simWork σ.symm)
      (relabel (wsSplit Q.W Sc).symm (tensorVec (simQuery e Q.W t v) u)) := by
    ext b
    rfl
  rw [h1, h2, simQuery_simWork, simQuery_prod]
  congr 2
  rw [show relabel (wsSplit Q.W Sc) (relabel (wsSplit Q.W Sc).symm (tensorVec v u)) =
    tensorVec v u by ext; simp, controlled_tensorVec]
  rfl

include hinit hstep in
theorem simStage_scratch (k : ℕ) : simStage e Q' k = sEmb Q Q' σ u (simStage e Q k) := by
  induction k with
  | zero =>
    show simStep Q' 0 (simInit e Q') = _
    rw [simInit_scratch e Q Q' σ u hinit, simStep_scratch Q Q' σ u hstep]
    rfl
  | succ k ih =>
    show simStep Q' (k + 1) (simQuery e Q'.W t (simStage e Q' k)) = _
    rw [ih, simQuery_scratch, simStep_scratch Q Q' σ u hstep]
    rfl

include hinit hstep in
/-- **The simulated run of `Q'` is that of `Q` with the scratch at `u`**, and `simLaw` is that
of `Q`, for a unit vector `u` and an output that does not read the scratch. -/
theorem simLaw_eq_of_scratch (hu : ‖u‖ = 1) (hout : ∀ w, Q'.out w = Q.out (σ w).1) :
    simLaw e Q' = simLaw e Q := by
  ext S
  rw [simLaw, simLaw, MeasureTheory.OuterMeasure.map_apply, MeasureTheory.OuterMeasure.map_apply,
    bornWeight_apply_eq_sum, bornWeight_apply_eq_sum]
  change ∑ b, _ = _
  rw [simState, simState, simStage_scratch e Q Q' σ u hinit hstep,
    ← Equiv.sum_comp (sSplit Q Q' σ).symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hsum : ∑ s, ‖u s‖ₑ ^ 2 = 1 := by
    rw [sum_enorm_sq, hu, one_pow, ENNReal.ofReal_one]
  by_cases hb : b ∈ (fun b : SimRegister Q.W I J m t => (Q.out b.1.1, slotsDB e b.2)) ⁻¹' S
  · rw [Set.indicator_of_mem hb, ← mul_one (‖_‖ₑ ^ 2), ← hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hm : (sSplit Q Q' σ).symm (b, s) ∈
        (fun b : SimRegister Q'.W I J m t => (Q'.out b.1.1, slotsDB e b.2)) ⁻¹' S := by
      simp only [Set.mem_preimage, hout] at hb ⊢
      simpa [sSplit, simWork, wsSplit] using hb
    rw [Set.indicator_of_mem hm]
    change ‖tensorVec _ u ((sSplit Q Q' σ) ((sSplit Q Q' σ).symm (b, s)))‖ₑ ^ 2 = _
    rw [Equiv.apply_symm_apply, tensorVec_apply, enorm_mul, mul_pow]
  · rw [Set.indicator_of_notMem hb]
    refine Finset.sum_eq_zero fun s _ => ?_
    have hm : (sSplit Q Q' σ).symm (b, s) ∉
        (fun b : SimRegister Q'.W I J m t => (Q'.out b.1.1, slotsDB e b.2)) ⁻¹' S := by
      simp only [Set.mem_preimage, hout] at hb ⊢
      simpa [sSplit, simWork, wsSplit] using hb
    rw [Set.indicator_of_notMem hm]

end Scratch

end GordieHowe.QROM
