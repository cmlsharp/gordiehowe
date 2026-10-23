-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.AffineBatching
public import GordieHowe.ProofSystem.Ligero.MaskedPolynomialTest
public import Mathlib.Algebra.Polynomial.Module.Basic

@[expose] public section

/-!
# The masked polynomial constraint test: batching

The source polynomials of a constraint are batched with uniform coefficients (`batch`); a
response passing a linear check `check` is compared with the batch shifted by a mask. This file
holds the batch, its degree bound and the scalar check of a batch; the cancellation events and
column counts against a list of mask candidates are in `Ligero.MaskedConstraintList`.
-/

namespace GordieHowe.Ligero.MaskedConstraintTest

open Polynomial
open scoped Classical

variable {F : Type} [Field F] {N n : ℕ}

/-- The polynomial computed from the source rows and fresh coefficients. -/
noncomputable def batch (g : Fin n → F[X]) (r : Fin n → F) : F[X] :=
  ∑ i, Polynomial.C (r i) * g i

/-- Residual of each source row under the checked linear functional. -/
def residual (check : F[X] →ₗ[F] F) (g : Fin n → F[X]) (target : Fin n → F) : Fin n → F :=
  fun i => check (g i) - target i

/-- A combination of polynomials of degree `< d` has degree `< d`, for `0 < d`, including the
empty combination. -/
theorem natDegree_batch_lt {d : ℕ} (hd : 0 < d) {g : Fin n → F[X]}
    (hg : ∀ i, (g i).natDegree < d) (r : Fin n → F) : (batch g r).natDegree < d :=
  (natDegree_sum_le_of_forall_le Finset.univ (fun i => Polynomial.C (r i) * g i) (n := d - 1)
    fun i _ => (natDegree_C_mul_le _ _).trans (by have := hg i; omega)).trans_lt (by omega)

/-- A linear combination of degree-bounded source polynomials has the same
strict degree bound, including the empty combination. -/
theorem batch_degree (C : GordieHowe.RSCode F N) (g : Fin n → F[X])
    (hg : ∀ i, (g i).natDegree < C.k) (r : Fin n → F) :
    (batch g r).natDegree < C.k :=
  natDegree_batch_lt C.k_pos hg r

/-- Subtracting the computed source polynomial preserves the degree bound. -/
theorem shifted_degree (C : GordieHowe.RSCode F N) (g : Fin n → F[X])
    (hg : ∀ i, (g i).natDegree < C.k) (r : Fin n → F)
    (p : F[X]) (hp : p.natDegree < C.k) : (p - batch g r).natDegree < C.k :=
  (natDegree_sub_le _ _).trans_lt (max_lt hp (batch_degree C g hg r))

/-- The functional of a batch is the corresponding scalar linear combination. -/
theorem check_batch (check : F[X] →ₗ[F] F) (g : Fin n → F[X]) (r : Fin n → F) :
    check (batch g r) = ∑ i, r i * check (g i) := by
  simp [batch, ← Polynomial.smul_eq_C_mul]

end GordieHowe.Ligero.MaskedConstraintTest
