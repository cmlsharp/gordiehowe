-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.PackedClaim
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The equality polynomial in product form

`eqPoly ρ` is `eq(ρ, x) = ∏ i, (ρ i · x i + (1 - ρ i) · (1 - x i))` as a polynomial in `x`, and
`eqProd ρ s` its value at `s`. At the Boolean point with the little-endian bits of `j` it is
`PackedClaim.eqPt ρ j`, the weight that `Eqs::filleq` (`third_party/longfellow/lib/arrays/eqs.h`) tabulates: bit `l` of the
index pairs with coordinate `l`. In characteristic two the factor is `1 + ρ i + s i`, the form the
univariate-skip verifier multiplies out.
-/

namespace GordieHowe.EqPolynomial

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- `eq(ρ, x)` as a polynomial in `x`. -/
noncomputable def eqPoly (ρ : Fin n → K) : MvPolynomial (Fin n) K :=
  ∏ i, (C (ρ i) * X i + C (1 - ρ i) * (1 - X i))

/-- `eq(ρ, s)` for field points. -/
def eqProd (ρ s : Fin n → K) : K :=
  ∏ i, (ρ i * s i + (1 - ρ i) * (1 - s i))

@[simp] theorem eval_eqPoly (ρ s : Fin n → K) : eval s (eqPoly ρ) = eqProd ρ s := by
  simp [eqPoly, eqProd, map_prod]

/-- At the Boolean point with the bits of `j`, `eq` is the tabulated weight. -/
theorem eqProd_bits (ρ : Fin n → K) (j : ℕ) :
    eqProd ρ (fun i => if j.testBit i then 1 else 0) = PackedClaim.eqPt ρ j := by
  unfold eqProd PackedClaim.eqPt
  apply Finset.prod_congr rfl
  intro i _
  split <;> simp_all

/-- The characteristic-two factor `1 + ρ i + s i`. -/
theorem eqProd_charTwo [CharP K 2] (ρ s : Fin n → K) :
    eqProd ρ s = ∏ i, (1 + (ρ i + s i)) := by
  unfold eqProd
  apply Finset.prod_congr rfl
  intro i _
  linear_combination (ρ i * s i - ρ i - s i) * CharTwo.two_eq_zero (R := K)

/-- A factor `a · X u + (1 - a) · (1 - X u)` of `eqPoly` has degree at most one in its own
variable `u` and degree zero in every other variable. -/
theorem degreeOf_eqFactor_le (a : K) (u v : Fin n) :
    (C a * X u + C (1 - a) * (1 - X u) : MvPolynomial (Fin n) K).degreeOf v ≤
      if v = u then 1 else 0 := by
  apply (degreeOf_add_le v _ _).trans
  apply max_le
  · exact (degreeOf_C_mul_le _ _ _).trans (by simp [degreeOf_X])
  · apply (degreeOf_C_mul_le _ _ _).trans
    apply (degreeOf_sub_le v _ _).trans
    simp [degreeOf_X, degreeOf_one]

/-- `eq` has degree at most one in each variable. -/
theorem degreeOf_eqPoly_le (ρ : Fin n → K) (v : Fin n) :
    (eqPoly ρ).degreeOf v ≤ 1 := by
  apply (degreeOf_prod_le v Finset.univ _).trans
  apply (Finset.sum_le_sum fun i _ => degreeOf_eqFactor_le (ρ i) i v).trans
  simp

end GordieHowe.EqPolynomial
