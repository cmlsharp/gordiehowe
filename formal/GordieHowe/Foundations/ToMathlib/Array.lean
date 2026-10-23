-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.List.Nodup

@[expose] public section

/-!
# Reading an array filled by `set!` at distinct indices

Candidates for upstreaming next to core's `Array.getElem!_set!_self`.
-/

namespace Array

variable {α : Type*} [Inhabited α]

/-- Setting indices `p j` for `j ∈ l` leaves an index outside `l.map p` unchanged. -/
theorem getElem!_foldl_set!_of_notMem (p : ℕ → ℕ) (g : ℕ → α) {l : List ℕ} {init : Array α}
    {k : ℕ} (hk : k ∉ l.map p) :
    (l.foldl (fun B j => B.set! (p j) (g j)) init)[k]! = init[k]! := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    rw [List.foldl_cons, ih hk.2, getElem!_set!_ne _ _ _ _ (Ne.symm hk.1)]

/-- Setting in-bounds indices `p j` for `j ∈ l`, with `p` injective on `l`, stores `g i`
at `p i`. -/
theorem getElem!_foldl_set! (p : ℕ → ℕ) (g : ℕ → α) {l : List ℕ} {init : Array α}
    (hnd : (l.map p).Nodup) (hlt : ∀ i ∈ l, p i < init.size) {i : ℕ} (hi : i ∈ l) :
    (l.foldl (fun B j => B.set! (p j) (g j)) init)[p i]! = g i := by
  induction l generalizing init with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    by_cases hia : i = a
    · subst hia
      rw [getElem!_foldl_set!_of_notMem p g hnd.1]
      exact getElem!_set!_self _ _ _ (hlt i (by simp))
    · exact ih hnd.2 (fun j hj => by simpa [size_set!] using hlt j (by simp [hj]))
        ((List.mem_cons.mp hi).resolve_left hia)

end Array
