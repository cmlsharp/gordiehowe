-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Multiset.ZeroCons

@[expose] public section

/-!
# The element of a one-element multiset

`Multiset.single? s` is `some a` when `s = {a}` and `none` otherwise: a computable way to read the
unique element of a multiset that has one. Candidate for upstreaming to Mathlib
(`Mathlib/Data/Multiset/ZeroCons.lean`, next to `Multiset.card_eq_one`).
-/

namespace Multiset

variable {α : Type*}

/-- The head of a one-element list, `none` for other lists. -/
def _root_.List.single? : List α → Option α
  | [a] => some a
  | _ => none

theorem _root_.List.single?_perm : ∀ {l l' : List α}, l.Perm l' → l.single? = l'.single?
  | [], _, p => by rw [List.nil_perm.1 p]
  | [a], _, p => by rw [← List.singleton_perm.1 p]
  | a :: b :: l, l', p => by
    rcases l' with _ | ⟨c, _ | ⟨d, l'⟩⟩
    · exact absurd p.length_eq (by simp)
    · exact absurd p.length_eq (by simp)
    · rfl

/-- **The element of a one-element multiset**, `none` for other multisets. -/
def single? (s : Multiset α) : Option α :=
  Quot.liftOn s List.single? fun _ _ p => List.single?_perm p

@[simp] theorem single?_singleton (a : α) : ({a} : Multiset α).single? = some a := rfl

theorem single?_eq_some_iff {s : Multiset α} {a : α} : s.single? = some a ↔ s = {a} := by
  induction s using Quot.inductionOn with
  | h l =>
    show l.single? = some a ↔ (l : Multiset α) = ({a} : Multiset α)
    rw [show ({a} : Multiset α) = ([a] : List α) from rfl, Multiset.coe_eq_coe,
      List.perm_singleton]
    rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩
    · simp [List.single?]
    · simp [List.single?]
    · simp [List.single?]

/-- A multiset whose elements are all equal and that contains `a` has the single element `a`
when it has no duplicates. -/
theorem single?_eq_some_of_nodup {s : Multiset α} (hs : s.Nodup) {a : α} (ha : a ∈ s)
    (hall : ∀ b ∈ s, b = a) : s.single? = some a := by
  rw [single?_eq_some_iff]
  obtain ⟨t, rfl⟩ := exists_cons_of_mem ha
  rw [nodup_cons] at hs
  have ht : t = 0 := by
    rw [eq_zero_iff_forall_notMem]
    intro b hb
    exact hs.1 (hall b (mem_cons_of_mem hb) ▸ hb)
  rw [ht]
  rfl

end Multiset
