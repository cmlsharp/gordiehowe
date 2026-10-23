-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Merkle.Extract

@[expose] public section

/-!
# The digests a Merkle view visits

The view of an `n`-leaf tree below `rt` read from a database (`view`, `GordieHowe/SPBCS/Merkle/Extract.lean`)
looks up the preimages of the digests at its heap positions `p < 2n` and the root `rt`
(`visited`, at most `2n + 1` digests). Recording a new answer whose digest is not one of them
leaves the view unchanged (`view_extend_of_notMem_visited`). This is the equality form of
CMS19 Lemma 6.4 (p. 31; `view_subtree_extend`) used for the instability of the targeted
extractor: an extraction outcome read from views at fixed roots changes under one more recorded
query only if the answer's digest hits one of the visited digests.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

variable {k kN kS L e : ℕ}

/-- **The digests visited by the view of an `n`-leaf tree below `rt`**: the root and the labels
at the heap positions `p < 2n`. -/
def visited (D : ODB k kN kS L e) (n : ℕ) (rt : Digest k) : Finset (Digest k) :=
  insert rt ((Finset.range (2 * n)).biUnion fun p => (label D n rt p).toFinset)

variable {D : ODB k kN kS L e} {n : ℕ} {rt : Digest k} {x : Query k kN kS L} {y : Out k e}

theorem card_visited_le (D : ODB k kN kS L e) (n : ℕ) (rt : Digest k) :
    (visited D n rt).card ≤ 2 * n + 1 := by
  refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ p ∈ Finset.range (2 * n), (label D n rt p).toFinset.card
      ≤ ∑ _p ∈ Finset.range (2 * n), 1 :=
        Finset.sum_le_sum fun p _ => by cases label D n rt p <;> simp
    _ = 2 * n := by simp

theorem mem_visited_of_label {p : ℕ} (hp : p < 2 * n) {u : Digest k} (h : label D n rt p = some u) :
    u ∈ visited D n rt :=
  Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨p, Finset.mem_range.2 hp, by simp [h]⟩)

/-- A new answer whose digest is not visited changes no label. -/
theorem label_extend_of_notMem_visited (hx : x ∉ D) (hy : y.digest ∉ visited D n rt) :
    ∀ p, label (D.extend x y) n rt p = label D n rt p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    match p with
    | 0 => simp [label_zero]
    | 1 => simp [label_one]
    | p + 2 =>
      rw [label_succ_succ, label_succ_succ, ih _ (by omega)]
      split_ifs with hp
      · cases hv : label D n rt ((p + 2) / 2) with
        | none => rfl
        | some v =>
          have hne : y.digest ≠ v := by
            rintro rfl
            exact hy (mem_visited_of_label (by omega) hv)
          simp [children_extend_of_ne hx hne]
      · rfl

/-- **A new answer whose digest is not visited leaves the view unchanged** (the equality form of
CMS19 Lemma 6.4, p. 31). -/
theorem view_extend_of_notMem_visited (hx : x ∉ D) (hy : y.digest ∉ visited D n rt) :
    view (D.extend x y) n rt = view D n rt := by
  have hl := label_extend_of_notMem_visited hx hy
  refine MerkleView.ext (funext hl) (funext fun j => ?_)
  simp only [view, leafAt, hl]
  cases hv : label D n rt (n + j) with
  | none => rfl
  | some v =>
    have hne : y.digest ≠ v := by
      rintro rfl
      exact hy (mem_visited_of_label (by omega) hv)
    simp [Merkle.opening_extend_of_ne hx hne]

end GordieHowe.SPBCS
