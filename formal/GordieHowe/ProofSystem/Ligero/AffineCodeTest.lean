-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.AffineBatching
public import GordieHowe.ProofSystem.Ligero.MaskedPolynomialTest

@[expose] public section

/-!
# Affine Reed–Solomon code testing

`AffineProximity` isolates a finite-coefficient consequence of BCIKS20 Theorem 1.6 in the
unique-decoding regime, including elementary degenerate cases outside that theorem's positive-radius
statement. It remains an explicit reusable interface for these lower protocol layers. The proved
theorem `GordieHowe.RSCode.affineProximity` in `GordieHowe/Foundations/ReedSolomon/AffineProximity.lean` discharges
it. `projection` is the low-degree test's combination `U 0 + Σ r_i U (i + 1)` of the tableau rows,
which the Ligero verifier checks at the queried columns.
-/

namespace GordieHowe.Ligero.AffineCodeTest

open Polynomial
open scoped Classical
open scoped NNReal

section

variable {F : Type} [Field F] {R N : ℕ}

def projection (U : RSCode.Matrix F (R + 1) N) (r : Fin R → F) (j : Fin N) : F :=
  U 0 j + ∑ i, r i * U i.succ j

/-- **The projected polynomial**: `f_0 + Σ_i r_i f_{i+1}`, the polynomial whose evaluations are
the `projection` of the rows `f`. -/
noncomputable def projectedPolynomial (fs : Fin (R + 1) → F[X]) (r : Fin R → F) : F[X] :=
  fs 0 + ∑ i, r i • fs i.succ

@[simp] theorem eval_projectedPolynomial (fs : Fin (R + 1) → F[X]) (r : Fin R → F)
    (x : F) : (projectedPolynomial fs r).eval x =
      (fs 0).eval x + ∑ i, r i * (fs i.succ).eval x := by
  simp [projectedPolynomial, Polynomial.eval_finsetSum]

theorem projectedPolynomial_degree {C : GordieHowe.RSCode F N}
    {fs : Fin (R + 1) → F[X]} (h : ∀ i, (fs i).natDegree < C.k) (r : Fin R → F) :
    (projectedPolynomial fs r).natDegree < C.k := by
  apply (natDegree_add_le _ _).trans_lt
  apply max_lt (h 0)
  have hb : (∑ i, r i • fs i.succ).natDegree ≤ C.k - 1 :=
    natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (natDegree_smul_le _ _).trans (Nat.le_sub_one_of_lt (h i.succ))
  exact hb.trans_lt (Nat.sub_lt C.k_pos (by decide))

/-- A single projected row is within the code's radius of a response polynomial. -/
structure RowNearby (C : GordieHowe.RSCode F N) (u : Fin N → F) (p : F[X]) : Prop where
  degree : p.natDegree < C.k
  close : (Finset.univ.filter fun j => u j ≠ p.eval (C.D j)).card ≤ C.e

theorem rowNearby_iff {C : GordieHowe.RSCode F N} {u : Fin N → F} {p : F[X]} :
    RowNearby C u p ↔ RSCode.Nearby C (fun _ : Fin 1 => u) (fun _ => p) := by
  constructor
  · intro h
    exact ⟨fun _ => h.degree, by simpa [RSCode.columnErrors] using h.close⟩
  · intro h
    exact ⟨h.degree 0, h.row_close 0⟩

theorem projection_eq_of_column_good {C : GordieHowe.RSCode F N}
    {U : RSCode.Matrix F (R + 1) N} {fs : Fin (R + 1) → F[X]}
    {j : Fin N} (hj : j ∉ RSCode.columnErrors C U fs) (r : Fin R → F) :
    projection U r j = (projectedPolynomial fs r).eval (C.D j) := by
  have hrow : ∀ i, U i j = (fs i).eval (C.D j) := by
    intro i
    by_contra h
    exact hj (RSCode.mem_columnErrors.mpr ⟨i, h⟩)
  simp only [projection, eval_projectedPolynomial, hrow]

theorem projected_nearby {C : GordieHowe.RSCode F N}
    {U : RSCode.Matrix F (R + 1) N} {fs : Fin (R + 1) → F[X]}
    (h : RSCode.Nearby C U fs) (r : Fin R → F) :
    RowNearby C (projection U r) (projectedPolynomial fs r) := by
  refine ⟨projectedPolynomial_degree h.degree r, ?_⟩
  apply (Finset.card_le_card ?_).trans h.close
  intro j hj
  by_contra hgood
  exact (Finset.mem_filter.mp hj).2 (projection_eq_of_column_good hgood r)

/-- The reusable affine RS proximity interface: a far matrix rarely has a
nearby affine projection. The coefficient vector is uniform, including
dependent or zero rows; the conclusion uses common column distance, not
separate row radii.

For `e > 0`, BCIKS20 Theorem 1.6 applies with block length `N`, dimension `C.k`
(the paper's maximum-degree parameter is `C.k - 1`), and radius `e/N`.
`C.radius` gives the inclusive bound `e/N ≤ (1-C.k/N)/2`; this is strictly
below the Johnson radius since `0 < C.k/N < 1`. Uniform coefficients induce
the uniform affine-space distribution even for dependent generators, by
equal-size fibers. The paper's strict probability premise becomes this
non-strict bound by contraposition.

The case `e = 0` needs the elementary bound for intersection of an affine space with a linear code,
rather than the paper's positive-radius theorem. The equal-fiber and zero-radius bridges are proved
by `GordieHowe.RSCode.affineProximity` in `GordieHowe/Foundations/ReedSolomon/AffineProximity.lean`.
No additional field-size condition is
needed: domain injectivity gives `N ≤ |F|`, and equality makes the bound trivial. Source:
https://eprint.iacr.org/2020/654 (version of 2021-07-03), Theorem 1.6 and Theorem 1.2,
unique-decoding branch. -/
def AffineProximity [Fintype F] (C : GordieHowe.RSCode F N) (R : ℕ) : Prop :=
  ∀ U : RSCode.Matrix F (R + 1) N, (¬ ∃ fs, RSCode.Nearby C U fs) →
    (Finset.univ.filter fun r : Fin R → F =>
      ∃ p, RowNearby C (projection U r) p).card * Fintype.card F ≤
        N * Fintype.card F ^ R

end

end GordieHowe.Ligero.AffineCodeTest
