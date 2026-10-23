-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

/-!
# Affine coefficients and their placement in tableau coordinates

A polynomial of total degree at most one is exactly its constant coefficient
plus the sum of its variable coefficients. Pushing those coefficients to
array locations preserves evaluation even if several variables share a slot.
These are generic algebraic facts, candidates for Mathlib's polynomial and
finite-sum APIs; no prover assignment or placement injectivity is assumed.
-/

namespace GordieHowe.AffineCoordinates

open MvPolynomial
open scoped BigOperators
open scoped Classical

section

variable {F ι : Type*} [Field F]

/-- A monomial with total exponent at most one is constant or a single variable. -/
theorem exponent_eq_zero_or_single (m : ι →₀ ℕ) (hm : (m.sum fun _ e => e) ≤ 1) :
    m = 0 ∨ ∃ i, m = Finsupp.single i 1 := by
  classical
  by_cases hz : (m.sum fun _ e => e) = 0
  · left
    ext i
    by_cases hi : m i = 0
    · exact hi
    · have hmem : i ∈ m.support := Finsupp.mem_support_iff.mpr hi
      have hle : m i ≤ m.sum (fun _ e => e) :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
      simpa [hz] using hle
  · exact Or.inr ((Finsupp.sum_eq_one_iff m).mp (by omega))

/-- The coefficient of a single variable. -/
noncomputable def weight (p : MvPolynomial ι F) (i : ι) : F := p.coeff (Finsupp.single i 1)

variable [Fintype ι]

/-- Exact affine decomposition, including the constant and zero polynomials. -/
theorem affine_decomposition (p : MvPolynomial ι F) (hp : p.totalDegree ≤ 1) :
    p = C p.constantCoeff + ∑ i, C (weight p i) * X i := by
  classical
  ext m
  by_cases hm : m = 0
  · subst m
    simp [weight, constantCoeff_eq, coeff_C_mul, coeff_X]
  · by_cases hs : ∃ i, m = Finsupp.single i 1
    · obtain ⟨i, rfl⟩ := hs
      simp [weight, coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff, Ne.symm hm]
    · have hc : p.coeff m = 0 := by
        by_contra hc
        have hdeg := (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)).trans hp
        exact (exponent_eq_zero_or_single m hdeg).elim hm hs
      have hsingle : ∀ i, Finsupp.single i 1 ≠ m := fun i heq => hs ⟨i, heq.symm⟩
      simp [hc, coeff_C, Ne.symm hm, coeff_C_mul, coeff_X, hsingle]

/-- Evaluation exposes the precise public coefficients of every affine equation. -/
theorem eval_eq_constant_add_sum (p : MvPolynomial ι F) (hp : p.totalDegree ≤ 1)
    (w : ι → F) : eval w p = p.constantCoeff + ∑ i, weight p i * w i := by
  conv_lhs => rw [affine_decomposition p hp]
  simp

variable {Row Col : Type*} [Fintype Row] [Fintype Col] [DecidableEq Row] [DecidableEq Col]

/-- Accumulate all variable coefficients placed in one array location. Computable: a sum over
the variables with a decidable comparison of locations. -/
def coeffAt (loc : ι → Row × Col) (coeff : ι → F) (row : Row) (col : Col) : F :=
  ∑ i, if loc i = (row, col) then coeff i else 0

/-- Slotwise evaluation of accumulated coefficients is exactly evaluation on
the original variables, including repeated locations and zero coefficients. -/
theorem sum_coeffAt_mul (loc : ι → Row × Col) (coeff : ι → F) (values : Row → Col → F) :
    (∑ row, ∑ col, coeffAt loc coeff row col * values row col) =
      ∑ i, coeff i * values (loc i).1 (loc i).2 := by
  classical
  simp only [coeffAt, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext row
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rcases hloc : loc i with ⟨row, col⟩
  simp [Prod.mk.injEq, ite_and, ite_mul]

/-- The affine equation's constant and its array-position weights determine
its exact value on the selected tableau coordinates. -/
theorem eval_at_locations (p : MvPolynomial ι F) (hp : p.totalDegree ≤ 1)
    (loc : ι → Row × Col) (values : Row → Col → F) :
    eval (fun i => values (loc i).1 (loc i).2) p = p.constantCoeff +
      ∑ row, ∑ col, coeffAt loc (weight p) row col * values row col := by
  rw [eval_eq_constant_add_sum p hp, sum_coeffAt_mul]

end

end GordieHowe.AffineCoordinates
