-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.OracleTestBoundary
public import GordieHowe.Model.Quantum.O2H.Budget
public import GordieHowe.Model.Quantum.Core.Model
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section

/-!
# Queries that avoid a set of inputs

The class of the oracle-test gap lemma (`BlindExtractor`, `GordieHowe/Model/Quantum/OracleTestBoundary.lean`) is
defined by a property of the extractor's output law: it depends on the oracle `H` only off a set
`X0` of inputs. This file holds lemmas about states and queries that avoid a set of inputs:

- `supported_compl_of_prob_eq_zero`: a vector with no weight on a set `B` is supported outside `B`;
- `testAccept_smul`: scaling the residual vector by `c` scales the acceptance of the test of the
  oracle-test gap lemma by `‖c‖ ^ 2`;
- `queryPerm_symm_mem_queried_iff`, `queryPerm_symm_eq_of_notMem_queried`: the inverse query
  keeps the basis states that query a set `S`, and two oracles that agree off `S` have the same
  inverse query on the basis states that do not query `S`.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace GordieHowe.Quantum

variable {Z W X Y : Type} [Fintype W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] {n d : ℕ}

/-- A vector with no weight on `B` is supported outside `B`. -/
theorem supported_compl_of_prob_eq_zero {ι : Type*} [Fintype ι] {B : Set ι} {v : QState ι}
    (h : prob B v = 0) : Supported Bᶜ v := by
  intro r hr
  have hm : mask B v = 0 := by
    rw [prob, sq_eq_zero_iff, norm_eq_zero] at h
    exact h
  have := congrArg (fun u : QState ι => u r) hm
  simp only [not_not, Set.mem_compl_iff] at hr
  simpa [mask_apply_of_mem _ hr] using this

/-! ### The extractor as a blind ensemble -/

variable {K : Type} [Fintype K]

theorem testAccept_smul (X0 : Finset X) (G : X → Y) (c : ℂ) (φ : QState (X × Y)) :
    testAccept X0 G (c • φ) = ‖c‖ ^ 2 * testAccept X0 G φ := by
  rw [testAccept_eq, testAccept_eq, inner_smul_right, norm_mul, mul_pow]

/-! ### Mixed algorithms: extractors with measurements -/

section Mixed

open scoped ComplexOrder

omit [Fintype W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- The inverse query keeps the query inputs, so it keeps the basis states that query `S`. -/
theorem queryPerm_symm_mem_queried_iff (H : X → Y) {S : Set X} (r : QueryReg W n X Y) :
    (queryPerm H).symm r ∈ queried S ↔ r ∈ queried S := by
  simp [queried, queryPerm_symm_apply]

omit [Fintype W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- **Two oracles that agree off `S` have the same inverse query** on the basis states that do not
query `S`. -/
theorem queryPerm_symm_eq_of_notMem_queried {S : Set X} {H H' : X → Y}
    (hHH' : ∀ x ∉ S, H x = H' x) {r : QueryReg W n X Y} (hr : r ∉ queried S) :
    (queryPerm H).symm r = (queryPerm H').symm r := by
  simp only [queried, Set.mem_ofPred_eq, not_exists] at hr
  rw [queryPerm_symm_apply, queryPerm_symm_apply]
  simp [hHH' _ (hr _)]

end Mixed

end GordieHowe.Quantum
