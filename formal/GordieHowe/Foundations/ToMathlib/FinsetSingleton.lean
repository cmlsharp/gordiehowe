-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Finset.Basic

@[expose] public section

/-!
# The element of a singleton finite set

`Finset.getSingleton? s` is `some a` when `s = {a}` and `none` otherwise
(`Finset.getSingleton?_eq_some_iff`). It reads the underlying list of `s` through `Quot.lift`
(a list is a singleton exactly when every permutation of it is), so it is computable and needs no
decidable equality. A candidate for upstreaming to `Mathlib.Data.Finset.Basic`.
-/

namespace Finset

variable {α : Type*}

/-- The element of a singleton list, `none` for any other list. -/
def _root_.List.getSingleton? : List α → Option α
  | [a] => some a
  | _ => none

theorem _root_.List.Perm.getSingleton?_eq {l l' : List α} (h : l.Perm l') :
    l.getSingleton? = l'.getSingleton? := by
  match l, l', h with
  | [a], l', h => rw [List.singleton_perm.mp h]
  | [], l', h => rw [List.Perm.nil_eq h]
  | a :: b :: l, l', h =>
    match l', h with
    | [c], h => exact absurd (List.perm_singleton.mp h) (by simp)
    | [], h => exact absurd (List.Perm.eq_nil h) (by simp)
    | _ :: _ :: _, _ => rfl

/-- **The element of a singleton finite set**: `some a` when `s = {a}`, `none` otherwise. -/
def getSingleton? (s : Finset α) : Option α :=
  Quot.liftOn s.val List.getSingleton? fun _ _ h => h.getSingleton?_eq

theorem getSingleton?_eq_some_iff {s : Finset α} {a : α} : s.getSingleton? = some a ↔ s = {a} := by
  rcases s with ⟨⟨l⟩, hnd⟩
  change l.getSingleton? = some a ↔ (⟨Quot.mk _ l, hnd⟩ : Finset α) = {a}
  rw [← Finset.val_inj]
  change l.getSingleton? = some a ↔ (l : Multiset α) = ([a] : List α)
  rw [Multiset.coe_eq_coe]
  constructor
  · intro h
    match l, h with
    | [b], h => cases h; exact List.Perm.refl _
  · intro h
    rw [h.getSingleton?_eq]
    rfl

end Finset
