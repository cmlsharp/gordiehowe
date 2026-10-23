-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.Model
public import GordieHowe.Model.Quantum.Pure.QueryAlg
public import GordieHowe.Model.Quantum.O2H.Mixed
public import GordieHowe.Foundations.ToMathlib.PMFOption

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

/-- **The halting operator** of a Kraus map: a matrix `B` with
`Bᴴ * B = 1 - ∑ r, (op r)ᴴ * op r` (`haltOp_spec`), which exists since the right side is positive
semidefinite. -/
noncomputable def haltOp : Matrix ι ι ℂ :=
  (exists_eq_conjTranspose_mul_self (Matrix.le_iff.1 K.sum_le)).choose

theorem haltOp_spec : 1 - ∑ r, (K.op r)ᴴ * K.op r = K.haltOpᴴ * K.haltOp :=
  (exists_eq_conjTranspose_mul_self (Matrix.le_iff.1 K.sum_le)).choose_spec

variable {K} in
/-- **The halting operator of a trace-preserving Kraus map is `0`.** -/
theorem haltOp_eq_zero (htp : ∑ r, (K.op r)ᴴ * K.op r = 1) : K.haltOp = 0 := by
  have h := K.haltOp_spec
  rw [htp, sub_self] at h
  exact Matrix.conjTranspose_mul_self_eq_zero.1 h.symm

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
