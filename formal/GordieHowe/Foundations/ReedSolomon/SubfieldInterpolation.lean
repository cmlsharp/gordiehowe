-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.Interpolation
public import GordieHowe.Foundations.ToMathlib.SubfieldCode

@[expose] public section

/-! Interpolating subfield-valued rows preserves membership on the code domain. -/
namespace GordieHowe.SubfieldInterpolation
open Polynomial
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ}

/-- All interpolant coefficients lie in the same subfield as its distinct
message nodes and values. The empty-node interpolant is zero. -/
theorem coeff_mem (E : Subfield F) (nodes : Fin k → F)
    (hinj : Function.Injective nodes) (hnodes : ∀ i, nodes i ∈ E)
    (values : Fin k → F) (hvalues : ∀ i, values i ∈ E) (i : ℕ) :
    (LigeroInterpolation.interpolate nodes values).coeff i ∈ E := by
  by_cases hk : k = 0
  · subst k
    simp [LigeroInterpolation.interpolate, Lagrange.interpolate_apply]
  · let S : Finset F := Finset.univ.image nodes
    have hcard : S.card = k := by
      simp only [S, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    apply Polynomial.coeff_mem_of_eval_mem E (S := S)
    · intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact hnodes j
    · rw [hcard]
      exact LigeroInterpolation.interpolate_degree (Nat.pos_of_ne_zero hk) hinj values
    · intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      rw [LigeroInterpolation.interpolate_eval hinj]
      exact hvalues j

/-- Consequently every subfield code-domain point yields a subfield opening. -/
theorem eval_mem (E : Subfield F) (nodes : Fin k → F)
    (hinj : Function.Injective nodes) (hnodes : ∀ i, nodes i ∈ E)
    (values : Fin k → F) (hvalues : ∀ i, values i ∈ E)
    {x : F} (hx : x ∈ E) :
    (LigeroInterpolation.interpolate nodes values).eval x ∈ E :=
  Polynomial.eval_mem_of_coeff_mem E (coeff_mem E nodes hinj hnodes values hvalues) hx

/-- The whole-row condition is sufficient for every query, without restricting
which code columns the verifier opens. -/
theorem row_evaluations_mem {Row Col : Type} (E : Subfield F) (nodes : Fin k → F)
    (hinj : Function.Injective nodes) (hnodes : ∀ i, nodes i ∈ E)
    (values : Row → Fin k → F) (selected : Set Row)
    (hvalues : ∀ row ∈ selected, ∀ i, values row i ∈ E)
    (domain : Col → F) (hdomain : ∀ j, domain j ∈ E)
    (row : Row) (hrow : row ∈ selected) (j : Col) :
    (LigeroInterpolation.interpolate nodes (values row)).eval (domain j) ∈ E :=
  eval_mem E nodes hinj hnodes (values row) (hvalues row hrow) (hdomain j)

end GordieHowe.SubfieldInterpolation
