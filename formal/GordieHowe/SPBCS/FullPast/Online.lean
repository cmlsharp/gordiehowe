-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.Verifier
public import GordieHowe.SPBCS.Extraction.KnowledgeError
public import GordieHowe.Model.QROM.QueryBits
public import GordieHowe.Model.QROM.QueryCount
public import GordieHowe.SPBCS.Extraction.OnlineExtract
public import GordieHowe.SPBCS.Extraction.OnlineExtractROM
public import GordieHowe.Model.ROM.Model

@[expose] public section

/-!
# Query counts of the series–parallel base model

Pieces of the online extractability of the spBCS compiler in the QROM (`GordieHowe/SPBCS/Online.lean`:
the instance `GordieHowe.SPBCS.toQVerifier`, its query budget `GordieHowe.SPBCS.kqOf` and its knowledge error
`GordieHowe.SPBCS.knowledgeError_toQVerifier`), stated at the series–parallel base model (`GordieHowe.SPBCS.FullPast`):

- `GordieHowe.SPBCS.Base.sum_length_openedIn`: the opened leaves of the trees of the positions `ps` number one
  per position.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  (M : Base P t X k kN kS L e) {V : X → FullTr P t → Bool}

/-! ### The verifier's query count -/

section QueryCount

variable {M} (h : Query k kN kS L → Out k e) {x : X} (π : M.NIProof) (Q : M.IOPQueries V x)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
open Classical in
/-- The opened leaves of the trees of the positions `ps`, one per position. -/
theorem sum_length_openedIn {ps : List M.Pos} {as : List (MerkleLeaf kN L)}
    (hl : ps.length = as.length) :
    ((M.trees ps).map fun τ => (M.openedIn τ ps as).length).sum = ps.length := by
  have hfst : (ps.zip as).map (Pos.treeOf ∘ Prod.fst) = ps.map Pos.treeOf := by
    rw [← List.map_map, List.map_fst_zip hl.le]
  have hcount : ∀ τ, (M.openedIn τ ps as).length = (ps.map Pos.treeOf).count τ := by
    intro τ
    rw [← hfst, List.count, List.countP_map, openedIn, List.length_filterMap_eq_countP]
    congr 1
    funext pa
    by_cases hτ : pa.1.treeOf = τ <;> simp [hτ]
  simp only [hcount, trees]
  rw [List.sum_map_count_dedup_eq_length, List.length_map]

end QueryCount

end Base
end GordieHowe.SPBCS
