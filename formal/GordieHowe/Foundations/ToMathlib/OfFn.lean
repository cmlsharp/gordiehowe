-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.List.OfFn

@[expose] public section

/-!
# `List.ofFn` of a mapped read

Candidates for upstreaming next to `List.ofFn_getElem` and `Vector.toList`.
-/

/-- Reading a vector entrywise through `f` is mapping `f` over its list. -/
theorem Vector.ofFn_get_map {α β : Type*} {n : ℕ} (v : Vector α n) (f : α → β) :
    List.ofFn (fun j => f (v.get j)) = v.toList.map f := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_ofFn, List.getElem_map, Vector.getElem_toList]
  rfl

/-- Reading a list of length `n` through `getD` and `f` at each index below `n` is mapping `f`
over it. -/
theorem List.ofFn_getD_map {α β : Type*} {n : ℕ} {l : List α} (hl : l.length = n) (d : α)
    (f : α → β) : List.ofFn (fun j : Fin n => f (l.getD j d)) = l.map f := by
  apply List.ext_getElem (by simp [hl])
  intro i h₁ h₂
  rw [List.length_ofFn] at h₁
  simp [List.getElem?_eq_getElem (hl ▸ h₁)]
