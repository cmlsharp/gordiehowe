-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Module.Basic
public import GordieHowe.Foundations.ToMathlib.LagrangeEval

@[expose] public section

/-!
# Public coefficient interpolation in the Ligero linear test

The public coefficient row is interpolated on the same message nodes as each
decoded witness row. Multiplying those polynomials produces degree at most
`2k-2`. Summing evaluations at the witness message positions yields the
specified coefficient dot product. Privacy and padding positions can be
excluded by the explicit finite set in `sumEvaluationOn`; a separate mask
is not identified with an honest low-degree polynomial in this module.

The selected verifier uses the W-only functional: `lib/ligero/ligero_verifier.h:219` sums `p.w`
response entries starting at `p.r`. Its `dot_check` interpolates the coefficient rows prepared by
`LigeroCommon::layout_Aext`, whose first `p.r` entries are zero and whose following `p.w` entries
are the coefficients. Thus `sumEvaluationOn` is the interface for that test; `sumEvaluation` is only
the all-message-nodes specialization.
-/

namespace GordieHowe.LigeroInterpolation

open Polynomial
open scoped BigOperators

section

variable {F : Type*} [Field F] {k : ℕ}

/-- Lagrange interpolation is linear in the supplied row values. -/
noncomputable def interpolate (nodes : Fin k → F) : (Fin k → F) →ₗ[F] F[X] :=
  Lagrange.interpolate Finset.univ nodes

theorem interpolate_eval {nodes : Fin k → F} (hinj : Function.Injective nodes)
    (values : Fin k → F) (j : Fin k) :
    (interpolate nodes values).eval (nodes j) = values j :=
  Lagrange.eval_interpolate_at_node values hinj.injOn (Finset.mem_univ j)

/-- **A polynomial of degree `< k` is the interpolant of its values at `k` distinct nodes.** -/
theorem interpolate_eval_nodes {nodes : Fin k → F} (hinj : Function.Injective nodes) {p : F[X]}
    (hp : p.degree < k) : interpolate nodes (fun j => p.eval (nodes j)) = p :=
  (Lagrange.eq_interpolate_of_eval_eq _ hinj.injOn (by simpa using hp) fun _ _ => rfl).symm

/-- The zero row is covered by the strict bound because the dimension is positive. -/
theorem interpolate_degree {nodes : Fin k → F} (hk : 0 < k)
    (hinj : Function.Injective nodes) (values : Fin k → F) :
    (interpolate nodes values).natDegree < k := by
  have hd : (interpolate nodes values).degree < (k : WithBot ℕ) := by
    simpa only [interpolate, Finset.card_univ, Fintype.card_fin] using
      Lagrange.degree_interpolate_lt (s := Finset.univ) values hinj.injOn
  rcases eq_or_ne (interpolate nodes values) 0 with hzero | hzero
  · simpa [hzero] using hk
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hd

/-- The interpolant's value at `x`, by field operations (`Lagrange.basisEval`): the executable
form of `(interpolate nodes values).eval x` (`eval_interpolate`). -/
def interpolateEval (nodes : Fin k → F) (values : Fin k → F) (x : F) : F :=
  ∑ j, values j * Lagrange.basisEval Finset.univ nodes j x

theorem eval_interpolate (nodes : Fin k → F) (values : Fin k → F) (x : F) :
    (interpolate nodes values).eval x = interpolateEval nodes values x := by
  simp only [interpolate, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C,
    Lagrange.eval_basis_eq_basisEval, interpolateEval]

@[simp] theorem interpolate_add (nodes : Fin k → F) (u v : Fin k → F) :
    interpolate nodes (u + v) = interpolate nodes u + interpolate nodes v :=
  (interpolate nodes).map_add u v

@[simp] theorem interpolate_smul (nodes : Fin k → F) (a : F) (u : Fin k → F) :
    interpolate nodes (a • u) = a • interpolate nodes u :=
  (interpolate nodes).map_smul a u

/-- The verifier's sum functional on a chosen message-position set. -/
def sumEvaluationOn (nodes : Fin k → F) (W : Finset (Fin k)) : F[X] →ₗ[F] F where
  toFun p := ∑ j ∈ W, p.eval (nodes j)
  map_add' p q := by simp [Finset.sum_add_distrib]
  map_smul' a p := by simp [Finset.mul_sum]

/-- The special case that sums all systematic message positions. -/
def sumEvaluation (nodes : Fin k → F) : F[X] →ₗ[F] F :=
  sumEvaluationOn nodes Finset.univ

@[simp] theorem sumEvaluationOn_apply (nodes : Fin k → F) (W : Finset (Fin k)) (p : F[X]) :
    sumEvaluationOn nodes W p = ∑ j ∈ W, p.eval (nodes j) := rfl

@[simp] theorem sumEvaluation_apply (nodes : Fin k → F) (p : F[X]) :
    sumEvaluation nodes p = ∑ j, p.eval (nodes j) := rfl

variable {Row : Type*} [Fintype Row]

/-- The row-summed polynomial used for a public-coefficient linear test. -/
noncomputable def decodedDot (nodes : Fin k → F) (coeff : Row → Fin k → F) (fs : Row → F[X]) : F[X] :=
  ∑ row, interpolate nodes (coeff row) * fs row

theorem decodedDot_degree {nodes : Fin k → F} (hk : 0 < k)
    (hinj : Function.Injective nodes) (coeff : Row → Fin k → F)
    (fs : Row → F[X]) (hfs : ∀ row, (fs row).natDegree < k) :
    (decodedDot nodes coeff fs).natDegree < 2 * k - 1 := by
  have hb : (decodedDot nodes coeff fs).natDegree ≤ 2 * (k - 1) := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro row _
    have hc := interpolate_degree hk hinj (coeff row)
    have hw := hfs row
    exact Polynomial.natDegree_mul_le.trans (by omega)
  omega

/-- At a systematic node the public interpolant reproduces its coefficient. -/
theorem decodedDot_eval {nodes : Fin k → F} (hinj : Function.Injective nodes)
    (coeff : Row → Fin k → F) (fs : Row → F[X]) (j : Fin k) :
    (decodedDot nodes coeff fs).eval (nodes j) =
      ∑ row, coeff row j * (fs row).eval (nodes j) := by
  simp only [decodedDot, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    interpolate_eval hinj]

/-- Restricting the verifier sum to witness positions gives the corresponding
dot product, without any condition on omitted privacy positions. -/
theorem sumEvaluationOn_decodedDot {nodes : Fin k → F} (hinj : Function.Injective nodes)
    (W : Finset (Fin k)) (coeff : Row → Fin k → F) (fs : Row → F[X]) :
    sumEvaluationOn nodes W (decodedDot nodes coeff fs) =
      ∑ row, ∑ j ∈ W, coeff row j * (fs row).eval (nodes j) := by
  simp only [sumEvaluationOn_apply, decodedDot_eval hinj]
  exact Finset.sum_comm

theorem sumEvaluation_decodedDot {nodes : Fin k → F} (hinj : Function.Injective nodes)
    (coeff : Row → Fin k → F) (fs : Row → F[X]) :
    sumEvaluation nodes (decodedDot nodes coeff fs) =
      ∑ row, ∑ j, coeff row j * (fs row).eval (nodes j) :=
  sumEvaluationOn_decodedDot hinj Finset.univ coeff fs

/-- With fixed public coefficients, the dot polynomial is linear in witness rows. -/
noncomputable def decodedDotLinear (nodes : Fin k → F) (coeff : Row → Fin k → F) :
    (Row → F[X]) →ₗ[F] F[X] where
  toFun := decodedDot nodes coeff
  map_add' fs gs := by simp [decodedDot, mul_add, Finset.sum_add_distrib]
  map_smul' a fs := by simp [decodedDot, Finset.smul_sum]

@[simp] theorem decodedDotLinear_apply (nodes : Fin k → F) (coeff : Row → Fin k → F)
    (fs : Row → F[X]) : decodedDotLinear nodes coeff fs = decodedDot nodes coeff fs := rfl

end

end GordieHowe.LigeroInterpolation
