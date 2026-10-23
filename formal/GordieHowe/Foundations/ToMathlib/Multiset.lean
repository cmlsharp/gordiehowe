-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Set.Function

@[expose] public section

/-!
# Multisets: equality from images under a map injective on their elements

Candidate for upstreaming to Mathlib (`Mathlib/Data/Multiset/Filter.lean`, next to
`Multiset.count_map_eq_count`).
-/

namespace Multiset

/-- A map injective on the elements of two multisets is injective on them: equal images give
equal multisets. -/
theorem eq_of_map_eq_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    {s t : Multiset α} (hf : Set.InjOn f {x | x ∈ s ∨ x ∈ t}) (h : s.map f = t.map f) : s = t := by
  ext x
  by_cases hx : x ∈ s ∨ x ∈ t
  · have hs := count_map_eq_count f s (hf.mono fun y hy => Or.inl hy)
    have ht := count_map_eq_count f t (hf.mono fun y hy => Or.inr hy)
    have hcs : count (f x) (s.map f) = count x s := by
      by_cases hxs : x ∈ s
      · exact hs x hxs
      · rw [count_eq_zero.mpr hxs, count_eq_zero]
        intro hm
        obtain ⟨y, hy, hyx⟩ := mem_map.mp hm
        exact hxs (hf (Or.inl hy) hx hyx ▸ hy)
    have hct : count (f x) (t.map f) = count x t := by
      by_cases hxt : x ∈ t
      · exact ht x hxt
      · rw [count_eq_zero.mpr hxt, count_eq_zero]
        intro hm
        obtain ⟨y, hy, hyx⟩ := mem_map.mp hm
        exact hxt (hf (Or.inr hy) hx hyx ▸ hy)
    rw [← hcs, ← hct, h]
  · push Not at hx
    rw [count_eq_zero.mpr hx.1, count_eq_zero.mpr hx.2]

end Multiset
