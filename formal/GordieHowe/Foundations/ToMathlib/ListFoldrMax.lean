-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-!
# A `max` fold over a list as the supremum over its elements

`List.foldr_max_eq_sup_toFinset`: folding `max (f b)` over a list of naturals from `0` is the
supremum of `f` over the list's elements. Definitions that must stay free of Mathlib
(`GordieHoweNative`) write a supremum as this fold.
-/

/-- **A `max` fold from `0` is the supremum over the list's elements.** -/
theorem List.foldr_max_eq_sup_toFinset {β : Type*} [DecidableEq β] (l : List β) (f : β → ℕ) :
    l.foldr (fun b a => max (f b) a) 0 = l.toFinset.sup f := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.toFinset_cons, Finset.sup_insert]
