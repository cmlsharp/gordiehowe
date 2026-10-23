-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section

/-!
# Complex matrices: traces, sums and positive semidefiniteness

Facts about Mathlib's matrices used by the mixed-state formalism (`GordieHowe/Model/Quantum/Core/Channel.lean`):

- `exists_eq_conjTranspose_mul_self`: a positive semidefinite matrix is `Bᴴ B`;
- `PosSemidef.re_trace_mul_nonneg`: `0 ≤ re (tr (A B))` for positive semidefinite `A`, `B`;
- `re_trace_eq_sum`, `trace_submatrix_equiv`: the trace as a sum of diagonal entries, and its
  invariance under conjugation by a permutation of the basis;
- `sum_kronecker`, `submatrix_sum`: Kronecker products and submatrices commute with finite sums.

The statements are about Mathlib objects only and are candidates for upstreaming.
-/

open Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- A positive semidefinite matrix is `Bᴴ B` for some `B` (its square root). -/
theorem exists_eq_conjTranspose_mul_self [DecidableEq ι] {M : Matrix ι ι ℂ} (hM : M.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, M = Bᴴ * B := by
  refine ⟨CFC.sqrt M, ?_⟩
  have hsa : (CFC.sqrt M)ᴴ = CFC.sqrt M := (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq
  rw [hsa, CFC.sqrt_mul_sqrt_self M hM.nonneg]

/-- The real part of the trace is the sum of the real parts of the diagonal. -/
theorem re_trace_eq_sum (ρ : Matrix ι ι ℂ) : ρ.trace.re = ∑ i, (ρ i i).re := by
  rw [Matrix.trace, Complex.re_sum]
  rfl

/-- Conjugating by a permutation of the basis preserves the trace. -/
theorem trace_submatrix_equiv {R : Type*} [AddCommMonoid R] (ρ : Matrix ι ι R) (e : ι ≃ ι) :
    (ρ.submatrix e e).trace = ρ.trace :=
  Equiv.sum_comp e fun i => ρ i i

/-- A positive semidefinite matrix has a trace with nonnegative real part. -/
theorem PosSemidef.re_trace_nonneg {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) : 0 ≤ ρ.trace.re :=
  (Complex.nonneg_iff.1 hρ.trace_nonneg).1

/-- The trace of a product of two positive semidefinite matrices has nonnegative real part. -/
theorem PosSemidef.re_trace_mul_nonneg [DecidableEq ι] {A B : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  obtain ⟨C, rfl⟩ := exists_eq_conjTranspose_mul_self hA
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact (hB.mul_mul_conjTranspose_same C).re_trace_nonneg

/-- The Kronecker product with a fixed right factor commutes with finite sums. -/
theorem sum_kronecker {α R l m n p : Type*} [CommSemiring R] (s : Finset α)
    (A : α → Matrix l m R) (B : Matrix n p R) :
    (∑ a ∈ s, A a) ⊗ₖ B = ∑ a ∈ s, A a ⊗ₖ B :=
  map_sum ({ toFun := fun M => M ⊗ₖ B
             map_zero' := zero_kronecker B
             map_add' := fun M N => add_kronecker M N B } : Matrix l m R →+ Matrix (l × n) (m × p) R)
    A s

/-- Taking a submatrix commutes with finite sums. -/
theorem submatrix_sum {α R l m n o : Type*} [AddCommMonoid R] (s : Finset α)
    (A : α → Matrix m n R) (e : l → m) (f : o → n) :
    (∑ a ∈ s, A a).submatrix e f = ∑ a ∈ s, (A a).submatrix e f :=
  map_sum ({ toFun := fun M => M.submatrix e f
             map_zero' := by simp
             map_add' := fun M N => rfl } : Matrix m n R →+ Matrix l o R) A s

end Matrix
