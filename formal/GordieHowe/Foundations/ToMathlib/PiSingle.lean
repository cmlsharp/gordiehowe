-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Pi

@[expose] public section

/-!
# Unit-vector decomposition of a doubly indexed vector

Candidate for upstreaming next to `Finset.univ_sum_single`.
-/

/-- A doubly indexed vector is the sum of its entries times the unit vectors. -/
theorem Pi.sum_smul_single_single {ι κ R : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (x : ι → κ → R) :
    ∑ y, ∑ i, x y i • Pi.single y (Pi.single i (1 : R)) = x := by
  ext y' i'
  simp [Finset.sum_apply, Pi.single_apply, ite_apply]
