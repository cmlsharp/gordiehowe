-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.List.Range

@[expose] public section

/-!
# A vector's list as a total read over `List.range`

Candidate for upstreaming next to core's `Vector.toList`.
-/

/-- A vector's list is the total read `getD` at each index below its length. -/
theorem Vector.toList_eq_map_range_getD {α : Type*} {n : ℕ} (v : Vector α n) (d : α) :
    v.toList = (List.range n).map fun i => v.toArray.getD i d := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, Array.getD_eq_getD_getElem?]
  rw [Vector.length_toList] at h1
  simp [h1]
