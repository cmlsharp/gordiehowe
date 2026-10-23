-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# Evaluating a Lagrange basis polynomial

The value of the Lagrange basis polynomial `Lagrange.basis s v i` at a point `r` is the product
`∏ j ∈ s \ {i}, (r - v j) / (v i - v j)` (`Lagrange.eval_basis_eq_basisEval`). `basisEval`
computes it by field operations, with no `Polynomial` arithmetic, so definitions that need the
value can be computable. A candidate for upstreaming to `Mathlib.LinearAlgebra.Lagrange`.
-/

open Polynomial

namespace Lagrange

variable {F ι : Type*} [Field F] [DecidableEq ι]

/-- The value at `r` of the Lagrange basis polynomial of the node `i` over the nodes `v` on `s`:
`∏ j ∈ s \ {i}, (r - v j) / (v i - v j)`. -/
def basisEval (s : Finset ι) (v : ι → F) (i : ι) (r : F) : F :=
  ∏ j ∈ s.erase i, (r - v j) / (v i - v j)

theorem eval_basis_eq_basisEval (s : Finset ι) (v : ι → F) (i : ι) (r : F) :
    (Lagrange.basis s v i).eval r = basisEval s v i r := by
  simp [Lagrange.basis, Lagrange.basisDivisor, eval_prod, basisEval, div_eq_inv_mul]

/-- Reindexing the nodes along an equivalence reindexes the basis values. -/
theorem basisEval_comp_equiv {κ : Type*} [DecidableEq κ] [Fintype ι] [Fintype κ] (v : κ → F)
    (e : ι ≃ κ) (i : ι) (r : F) :
    basisEval Finset.univ (v ∘ e) i r = basisEval Finset.univ v (e i) r := by
  unfold basisEval
  exact Finset.prod_equiv e (by simp) (fun _ _ => rfl)

end Lagrange
