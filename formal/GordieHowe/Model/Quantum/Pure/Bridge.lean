-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.Model
public import GordieHowe.Model.Quantum.Pure.QueryAlg
public import GordieHowe.Model.Quantum.O2H.Mixed
public import GordieHowe.Foundations.ToMathlib.PMFOption
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

@[expose] public section

/-!
# The halting completion of a core algorithm

The Kraus maps of a core algorithm (`Alg`, `GordieHowe/Model/Quantum/Core/Model.lean`) may lose trace
(non-termination, HU25 p. 245). Each `K : KrausMap R ι ι` is completed to a trace-preserving Kraus
family on `ι × Bool` (`KrausMap.complete`): on flag `false` it applies `K` and, with the operator
`B = √(1 - ∑ r, (op r)ᴴ * op r)` (`KrausMap.haltOp`), sets the flag to `true`; on flag `true` it
does nothing. The queries act on `ι` and leave the flag alone. The block of the state at flag
`false` is the state of the core at every step (`Alg.ffBlock_halting_stage`), so the outcome law
of the completed algorithm, with flag `true` read as `none`, is the output law of the core
(`Alg.outLaw_halting`). Its coherent purification is `Alg.toQueryAlgCoh`
(`GordieHowe/Model/QROM/CoherentBridgeCore.lean`).
-/

open Finset Matrix
open scoped BigOperators ENNReal MatrixOrder Kronecker ComplexOrder

namespace GordieHowe.Quantum

/-! ### Completing a Kraus map with a halting flag -/

namespace KrausMap

variable {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι] (K : KrausMap R ι ι)

open scoped Matrix.Norms.L2Operator in
/-- **The halting operator** of a Kraus map: the positive square root of the halting effect
`1 - ∑ r, (op r)ᴴ * op r`; `Bᴴ * B` is the halting effect (`haltOp_spec`). -/
noncomputable def haltOp : Matrix ι ι ℂ :=
  CFC.sqrt (1 - ∑ r, (K.op r)ᴴ * K.op r)

open scoped Matrix.Norms.L2Operator in
theorem haltOp_spec : 1 - ∑ r, (K.op r)ᴴ * K.op r = K.haltOpᴴ * K.haltOp := by
  have hP : (0 : Matrix ι ι ℂ) ≤ 1 - ∑ r, (K.op r)ᴴ * K.op r := sub_nonneg.2 K.sum_le
  have hs : K.haltOpᴴ = K.haltOp :=
    ((CFC.sqrt_nonneg (1 - ∑ r, (K.op r)ᴴ * K.op r)).isSelfAdjoint).star_eq
  rw [hs]
  exact (CFC.sqrt_mul_sqrt_self _ hP).symm

variable {K} in
/-- **The halting operator of a trace-preserving Kraus map is `0`.** -/
theorem haltOp_eq_zero (htp : ∑ r, (K.op r)ᴴ * K.op r = 1) : K.haltOp = 0 := by
  have h := K.haltOp_spec
  rw [htp, sub_self] at h
  exact Matrix.conjTranspose_mul_self_eq_zero.1 h.symm

open scoped Matrix.Norms.L2Operator in
/-- **The halting operator commutes with every matrix commuting with every `(op r)ᴴ * op r`.** -/
theorem haltOp_commute {M : Matrix ι ι ℂ} (hM : ∀ r, Commute M ((K.op r)ᴴ * K.op r)) :
    Commute M K.haltOp := by
  have hP : Commute (1 - ∑ r, (K.op r)ᴴ * K.op r) M :=
    ((Commute.one_left M).sub_left (Commute.sum_left _ _ _ fun r _ => (hM r).symm))
  unfold haltOp
  rw [CFC.sqrt_eq_cfc]
  exact (Commute.cfc_nnreal hP _).symm

/-- **`(op r)ᴴ * op r` keeps every basis permutation that the operators keep.** -/
theorem conjTranspose_mul_perm {σ : Equiv.Perm ι} (h : ∀ r a b, K.op r (σ a) (σ b) = K.op r a b)
    (r : R) (a b : ι) : ((K.op r)ᴴ * K.op r) (σ a) (σ b) = ((K.op r)ᴴ * K.op r) a b := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← Equiv.sum_comp σ]
  simp only [h]

/-- **The halting operator keeps every basis permutation that the operators keep.** -/
theorem haltOp_perm {σ : Equiv.Perm ι} (h : ∀ r a b, K.op r (σ a) (σ b) = K.op r a b)
    (a b : ι) : K.haltOp (σ a) (σ b) = K.haltOp a b := by
  set Pσ : Matrix ι ι ℂ := Matrix.of fun a b => if a = σ b then 1 else 0
  have hl : ∀ (N : Matrix ι ι ℂ) a b, (Pσ * N) a b = N (σ.symm a) b := fun N a b => by
    simp only [Pσ, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single (σ.symm a)]
    · simp
    · intro c _ hc
      rw [if_neg (fun h' => hc (by rw [h']; simp)), zero_mul]
    · simp
  have hr : ∀ (N : Matrix ι ι ℂ) a b, (N * Pσ) a b = N a (σ b) := fun N a b => by
    simp only [Pσ, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single (σ b)]
    · simp
    · intro c _ hc
      rw [if_neg hc, mul_zero]
    · simp
  have hc : Commute Pσ K.haltOp := K.haltOp_commute fun r => by
    ext a b
    rw [hl, hr]
    have := conjTranspose_mul_perm K h r (σ.symm a) b
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have := congrFun (congrFun hc.eq (σ a)) b
  rw [hl, hr, Equiv.symm_apply_apply] at this
  exact this.symm

/-- **The halting operator keeps every register that the operators read**: if the nonzero entries
of every operator have rows `a` and columns `b` with `f a = g b`, the nonzero entries of the halting
operator have rows and columns with equal `g`. -/
theorem haltOp_keeps {V : Type*} [DecidableEq V] {f g : ι → V}
    (h : ∀ r a b, K.op r a b ≠ 0 → f a = g b) {a b : ι} (hab : K.haltOp a b ≠ 0) : g a = g b := by
  set Dv : Matrix ι ι ℂ := Matrix.diagonal fun c => if g c = g b then 1 else 0
  have hc : Commute Dv K.haltOp := K.haltOp_commute fun r => by
    ext c d
    simp only [Dv, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hz : ((K.op r)ᴴ * K.op r) c d = 0
    · rw [hz, mul_zero, zero_mul]
    · have hcd : g c = g d := by
        obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by
          rwa [Matrix.mul_apply] at hz)
        have h1 : K.op r e c ≠ 0 := fun h0 => he (by
          rw [Matrix.conjTranspose_apply, h0, star_zero, zero_mul])
        have h2 : K.op r e d ≠ 0 := fun h0 => he (by rw [h0, mul_zero])
        exact (h r e c h1).symm.trans (h r e d h2)
      rw [hcd, mul_comm]
  have := congrFun (congrFun hc.eq a) b
  simp only [Dv, Matrix.diagonal_mul, Matrix.mul_diagonal, if_true, mul_one] at this
  by_contra hne
  rw [if_neg hne, zero_mul] at this
  exact hab this.symm

/-- The operators of the completion on `ι × Bool`: `K.op r ⊗ |false⟩⟨false|`, the halting step
`B ⊗ |true⟩⟨false|`, and `1 ⊗ |true⟩⟨true|` on halted states. -/
noncomputable def completeOp : R ⊕ Bool → Matrix (ι × Bool) (ι × Bool) ℂ
  | .inl r => K.op r ⊗ₖ Matrix.single false false 1
  | .inr false => K.haltOp ⊗ₖ Matrix.single true false 1
  | .inr true => 1 ⊗ₖ Matrix.single true true 1

theorem conjTranspose_kronecker_single_mul (M : Matrix ι ι ℂ) (a b : Bool) :
    (M ⊗ₖ Matrix.single a b (1 : ℂ))ᴴ * (M ⊗ₖ Matrix.single a b 1) =
      (Mᴴ * M) ⊗ₖ Matrix.single b b 1 := by
  rw [conjTranspose_kronecker, conjTranspose_single, star_one, ← mul_kronecker_mul,
    single_mul_single_same, mul_one]

/-- **The completion of a Kraus map with a halting flag**: a trace-preserving Kraus family on
`ι × Bool`. -/
noncomputable def complete : KrausChannel (R ⊕ Bool) (ι × Bool) (ι × Bool) where
  op := K.completeOp
  sum_conjTranspose_mul := by
    rw [Fintype.sum_sum_type, Fintype.sum_bool]
    simp only [completeOp, conjTranspose_kronecker_single_mul, conjTranspose_one, Matrix.one_mul]
    rw [← sum_kronecker, ← K.haltOp_spec]
    ext ⟨i, b⟩ ⟨j, c⟩
    cases b <;> cases c <;> simp [kroneckerMap_apply, Matrix.single_apply, Matrix.one_apply]

/-- The block of a matrix on `ι × Bool` at flag `false`. -/
def ffBlock (ρ : Matrix (ι × Bool) (ι × Bool) ℂ) : Matrix ι ι ℂ :=
  ρ.submatrix (·, false) (·, false)

omit [Fintype R] [DecidableEq ι] in
/-- **The flag-`false` block has at most the trace** of a matrix with a nonnegative diagonal. -/
theorem re_trace_ffBlock_le {ρ : Matrix (ι × Bool) (ι × Bool) ℂ} (h : ∀ i, 0 ≤ (ρ i i).re) :
    (ffBlock ρ).trace.re ≤ ρ.trace.re := by
  simp only [Matrix.trace, ffBlock, Matrix.diag_apply, Matrix.submatrix_apply, Complex.re_sum]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Fintype.sum_bool]
  linarith [h (i, true)]

omit [Fintype R] [DecidableEq ι] in
theorem ffBlock_kronecker_single_mul (M : Matrix ι ι ℂ) (a b : Bool)
    (ρ : Matrix (ι × Bool) (ι × Bool) ℂ) :
    ((M ⊗ₖ Matrix.single a b (1 : ℂ)) * ρ * (M ⊗ₖ Matrix.single a b 1)ᴴ).submatrix
        (·, false) (·, false) =
      if a = false then M * ρ.submatrix (·, b) (·, b) * Mᴴ else 0 := by
  ext i j
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, kroneckerMap_apply, Fintype.sum_prod_type, Matrix.single_apply]

/-- **The block at flag `false` follows `K`**: the completion acts there as `K`. -/
theorem ffBlock_complete_apply (ρ : Matrix (ι × Bool) (ι × Bool) ℂ) :
    ffBlock (K.complete ρ) = K (ffBlock ρ) := by
  rw [KrausChannel.apply, ffBlock, submatrix_sum, Fintype.sum_sum_type, Fintype.sum_bool]
  simp only [complete, completeOp, ffBlock_kronecker_single_mul]
  simp [KrausMap.apply, ffBlock]

end KrausMap

/-! ### The halting completion of a core algorithm -/

namespace Alg

variable {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  (A : Alg X Y O)

/-- **The halting completion of `A`**: a trace-preserving general algorithm (`MixedAlg`) on
`QueryReg V 1 X Y × Bool` whose initial state has flag `false`, whose Kraus maps are the
completions `(A.step k).complete`, and whose final measurement is in the computational basis. -/
noncomputable def halting :
    MixedAlg Unit (QueryReg A.V 1 X Y × Bool) A.depth (A.R ⊕ Bool) (QueryReg A.V 1 X Y × Bool) where
  init _ := A.init.tensorKet false
  step _ k := (A.step k).complete
  meas _ := KrausChannel.basis _

@[simp]
theorem halting_meas : A.halting.meas () = KrausChannel.basis _ :=
  rfl

/-- The output read from an outcome of the completed algorithm: `none` on halted outcomes. -/
def haltOut (p : QueryReg A.V 1 X Y × Bool) : Option O :=
  if p.2 then none else some (A.out p.1.1)

theorem ffBlock_halting_applyAt (k : ℕ) (ρ : MState (QueryReg A.V 1 X Y × Bool)) :
    KrausMap.ffBlock (A.halting.applyAt () k ρ).mat =
      KrausMap.stepAt A.step k (KrausMap.ffBlock ρ.mat) := by
  unfold MixedAlg.applyAt KrausMap.stepAt
  split_ifs
  · exact KrausMap.ffBlock_complete_apply _ _
  · rfl

variable [AddGroup Y]

/-- **The completed run agrees with the core run at flag `false`**. -/
theorem ffBlock_halting_stage (f : X → Y) (k : ℕ) :
    KrausMap.ffBlock (A.halting.stage (MixedAlg.liftPerm (queryPerm f)) () k).mat =
      A.stage f k := by
  induction k with
  | zero =>
    rw [MixedAlg.stage, ffBlock_halting_applyAt, Alg.stage, KrausMap.run_zero]
    congr 1
    ext i j
    simp [halting, KrausMap.ffBlock, kroneckerMap_apply]
  | succ k ih =>
    rw [MixedAlg.stage, ffBlock_halting_applyAt, Alg.stage, KrausMap.run_succ, ← Alg.stage, ← ih]
    rfl

/-- **The completed algorithm has the output law of `A`**, with halted outcomes read as
`none`. -/
theorem outLaw_halting (f : X → Y) :
    (A.halting.outLaw (MixedAlg.liftPerm (queryPerm f)) ()).map A.haltOut = A.outLaw f := by
  refine PMF.ext_of_some fun o => ?_
  have hdiag : ∀ i, (A.halting.final (MixedAlg.liftPerm (queryPerm f)) ()).mat (i, false) (i, false) =
      A.final f i i := fun i =>
    congrFun (congrFun (A.ffBlock_halting_stage f A.depth) i) i
  rw [PMF.map_apply, Alg.outLaw, PMF.map_apply, tsum_fintype, tsum_fintype, Fintype.sum_prod_type,
    Fintype.sum_option]
  simp only [haltOut, Fintype.sum_bool, MixedAlg.outLaw, KrausChannel.outcomeLaw_apply, halting_meas,
    KrausChannel.outcomeProb_basis, hdiag]
  simp [Alg.final]
  exact Finset.sum_congr rfl fun i _ => by congr

/-- The relabelling that moves the halting flag and the ancilla of the dilation into the work
register: `(((v, q), b), a) ↦ (((v, b), a), q)`. -/
def haltRelabel (V Anc : Type*) (X Y : Type*) :
    (QueryReg V 1 X Y × Bool) × Anc ≃ QueryReg ((V × Bool) × Anc) 1 X Y where
  toFun p := (((p.1.1.1, p.1.2), p.2), p.1.1.2)
  invFun r := (((r.1.1.1, r.2), r.1.1.2), r.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The ancilla of the dilation of the halting completion. -/
abbrev HaltAnc :=
  MixedAlg.Anc (QueryReg A.V 1 X Y × Bool) A.depth (A.R ⊕ Bool) (QueryReg A.V 1 X Y × Bool)

/-- An output of `A`: `out` at some basis state of the work register. It stands in for
non-termination. -/
noncomputable def defaultOut : O :=
  A.out A.init.nonempty.some.1

end Alg

end GordieHowe.Quantum
