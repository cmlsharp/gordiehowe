-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpenParametrization

@[expose] public section

/-!
# Substituting into a multivariate polynomial

Degree bounds and evaluation of `MvPolynomial.aeval` with polynomial values: the natural degree
of a substitution of univariate polynomials, the degree in one variable of a substitution of
multivariate polynomials, and evaluation after substitution (`polynomial_eval_aeval`, the univariate
case, is ArkLib's, imported). Upstream candidate for Mathlib
(`Mathlib/Algebra/MvPolynomial/Degrees.lean` and `Eval.lean`).
-/

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- Substituting univariate polynomials of natural degree at most `B` into `p` gives natural
degree at most `p.totalDegree * B`. -/
theorem natDegree_aeval_le [Fintype σ] {f : σ → Polynomial R} {B : ℕ}
    (hf : ∀ j, (f j).natDegree ≤ B) (p : MvPolynomial σ R) :
    (aeval f p).natDegree ≤ p.totalDegree * B := by
  rw [aeval_eq_eval₂Hom, coe_eval₂Hom, eval₂_eq', Polynomial.algebraMap_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
  calc ∑ i, (f i ^ m i).natDegree ≤ ∑ i, m i * B :=
        Finset.sum_le_sum fun i _ => Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hf i))
    _ = (∑ i, m i) * B := by rw [Finset.sum_mul]
    _ ≤ p.totalDegree * B := Nat.mul_le_mul_right _ (by
        have := le_totalDegree hm
        rwa [Finsupp.sum_fintype _ _ fun _ => rfl] at this)

/-- Substituting multivariate polynomials of degree at most `B` in `v` into `p` gives degree at
most `p.totalDegree * B` in `v`. -/
theorem degreeOf_aeval_le [Fintype σ] {g : σ → MvPolynomial τ R} {B : ℕ} (v : τ)
    (hg : ∀ j, (g j).degreeOf v ≤ B) (p : MvPolynomial σ R) :
    (aeval g p).degreeOf v ≤ p.totalDegree * B := by
  rw [aeval_eq_eval₂Hom, coe_eval₂Hom, eval₂_eq', algebraMap_eq]
  refine (degreeOf_sum_le v _ _).trans (Finset.sup_le fun m hm => ?_)
  refine (degreeOf_C_mul_le _ v _).trans ((degreeOf_prod_le v _ _).trans ?_)
  calc ∑ i, (g i ^ m i).degreeOf v ≤ ∑ i, m i * B :=
        Finset.sum_le_sum fun i _ => (degreeOf_pow_le v _ _).trans (Nat.mul_le_mul_left _ (hg i))
    _ = (∑ i, m i) * B := by rw [Finset.sum_mul]
    _ ≤ p.totalDegree * B := Nat.mul_le_mul_right _ (by
        have := le_totalDegree hm
        rwa [Finsupp.sum_fintype _ _ fun _ => rfl] at this)

/-- Evaluating a substitution of multivariate polynomials evaluates `p` at their values. -/
theorem eval_aeval (s : τ → R) (g : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    eval s (aeval g p) = eval (fun j => eval s (g j)) p := by
  induction p using MvPolynomial.induction_on <;> simp_all

end MvPolynomial
