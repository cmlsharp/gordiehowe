-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.CheckValues
public import GordieHoweNative.Language.Honest.CheckP

@[expose] public section

/-!
# GordieHowe: checks over two aligned lists

`allIdx2` checks a predicate at every index of two lists read together, the second padded with a
default, and `allIdx2_sound` gives the predicate at every index of the first.

The definitions are in `GordieHoweNative/Language/Honest/CheckP.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## One pass over two lists -/

theorem allIdx2_nil {α β : Type} (p : ℕ → α → β → Bool) (d : β) (m : List β) (i : ℕ) :
    allIdx2 p d [] m i = true := rfl

theorem allIdx2_sound {α β : Type} [Inhabited α] (p : ℕ → α → β → Bool) (d : β) :
    ∀ (l : List α) (m : List β) (i : ℕ), allIdx2 p d l m i = true →
      ∀ j < l.length, p (i + j) (l.getD j default) (m.getD j d) = true
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | x :: xs, m, i, h, j, hj => by
    rw [allIdx2_cons, Bool.and_eq_true] at h
    cases j with
    | zero =>
      cases m <;> simpa using h.1
    | succ j =>
      have := allIdx2_sound p d xs m.tail (i + 1) h.2 j (by simpa using hj)
      rw [show i + (j + 1) = i + 1 + j by omega]
      cases m <;> simpa using this

theorem allIdx2_iff {α β : Type} [Inhabited α] (p : ℕ → α → β → Bool) (d : β) :
    ∀ (l : List α) (m : List β) (i : ℕ), allIdx2 p d l m i = true ↔
      ∀ j < l.length, p (i + j) (l.getD j default) (m.getD j d) = true
  | [], _, i => by simp [allIdx2_nil]
  | x :: xs, m, i => by
    rw [allIdx2_cons, Bool.and_eq_true, allIdx2_iff p d xs m.tail (i + 1)]
    constructor
    · rintro ⟨h0, h⟩ j hj
      cases j with
      | zero => cases m <;> simpa using h0
      | succ j =>
        have := h j (by simpa using hj)
        rw [show i + (j + 1) = i + 1 + j by omega]
        cases m <;> simpa using this
    · intro h
      refine ⟨by cases m <;> simpa using h 0 (by simp), fun j hj => ?_⟩
      have := h (j + 1) (by simpa using hj)
      rw [show i + (j + 1) = i + 1 + j by omega] at this
      cases m <;> simpa using this

/-! ## Ranges of positions

`allIdx2` on the positions `[i, j)` (`allIdx2In`), as `allIdxIn` for one list: two consecutive
ranges join with no re-check (`allIdx2In_append`) and `[0, n)` gives the whole check
(`allIdx2_of_allIdx2In`). The kernel passes the positions before `i` of both lists by `dropK` and
checks the next `j - i` by the recursors (`allIdx2N`). -/

/-- **`allIdx2 p d (l.take n) m i`**, by the recursors (`allIdx2N_eq`). -/
noncomputable def allIdx2N {α β : Type} (p : ℕ → α → β → Bool) (d : β) (n : ℕ) :
    List α → List β → ℕ → Bool :=
  @Nat.rec (fun _ => List α → List β → ℕ → Bool) (fun _ _ _ => true)
    (fun _ ih l m i => @List.casesOn α (fun _ => Bool) l true fun x xs =>
      @List.casesOn β (fun _ => Bool) m
        (p i x d && @Nat.casesOn (fun _ => Bool) i (ih xs [] 1) fun k => ih xs [] (k + 2))
        fun y ys => p i x y && @Nat.casesOn (fun _ => Bool) i (ih xs ys 1) fun k => ih xs ys (k + 2))
    n

theorem allIdx2N_eq {α β : Type} (p : ℕ → α → β → Bool) (d : β) :
    ∀ (n : ℕ) (l : List α) (m : List β) (i : ℕ), allIdx2N p d n l m i = allIdx2 p d (l.take n) m i
  | 0, l, _, _ => by rw [List.take_zero]; rfl
  | _ + 1, [], _, _ => rfl
  | n + 1, x :: xs, [], i => by
    have : allIdx2N p d (n + 1) (x :: xs) [] i = (p i x d && allIdx2N p d n xs [] (i + 1)) := by
      cases i <;> rfl
    rw [this, allIdx2N_eq p d n xs [] (i + 1), List.take_succ_cons, allIdx2_cons]
    rfl
  | n + 1, x :: xs, y :: ys, i => by
    have : allIdx2N p d (n + 1) (x :: xs) (y :: ys) i =
        (p i x y && allIdx2N p d n xs ys (i + 1)) := by
      cases i <;> rfl
    rw [this, allIdx2N_eq p d n xs ys (i + 1), List.take_succ_cons, allIdx2_cons]
    rfl

/-- **`allIdx2` on the positions `[i, j)`** (`allIdx2In_iff`), by the recursors. -/
noncomputable def allIdx2In {α β : Type} (p : ℕ → α → β → Bool) (d : β) (l : List α) (m : List β)
    (i j : ℕ) : Bool :=
  allIdx2N p d (j - i) (dropK i l) (dropK i m) i

/-- **`allIdx2In`, by `List.drop` and `List.take`**: the code compiled for it. -/
def allIdx2InC {α β : Type} (p : ℕ → α → β → Bool) (d : β) (l : List α) (m : List β)
    (i j : ℕ) : Bool :=
  allIdx2 p d ((l.drop i).take (j - i)) (m.drop i) i

theorem allIdx2In_eq {α β : Type} (p : ℕ → α → β → Bool) (d : β) (l : List α) (m : List β)
    (i j : ℕ) : allIdx2In p d l m i j = allIdx2 p d ((l.drop i).take (j - i)) (m.drop i) i := by
  rw [allIdx2In, allIdx2N_eq, dropK_eq, dropK_eq]

@[csimp] theorem allIdx2In_csimp : @allIdx2In = @allIdx2InC := by
  funext α β p d l m i j
  exact allIdx2In_eq p d l m i j

theorem allIdx2In_iff {α β : Type} [Inhabited α] (p : ℕ → α → β → Bool) (d : β) (l : List α)
    (m : List β) (i j : ℕ) :
    allIdx2In p d l m i j = true ↔
      ∀ k, i ≤ k → k < j → k < l.length → p k (l.getD k default) (m.getD k d) = true := by
  rw [allIdx2In_eq, allIdx2_iff]
  simp only [List.length_take, List.length_drop, List.getD_eq_getElem?_getD, List.getElem?_take,
    List.getElem?_drop]
  constructor
  · intro h k hik hkj hkl
    have := h (k - i) (by omega)
    simp only [show k - i < j - i by omega, ite_true, Nat.add_sub_cancel' hik] at this
    exact this
  · intro h t ht
    simp only [show t < j - i by omega, ite_true]
    exact h (i + t) (by omega) (by omega) (by omega)

/-- **Two consecutive ranges of positions** check as one. -/
theorem allIdx2In_append {α β : Type} [Inhabited α] {p : ℕ → α → β → Bool} {d : β} {l : List α}
    {m : List β} {i j k : ℕ} (h₁ : allIdx2In p d l m i j = true)
    (h₂ : allIdx2In p d l m j k = true) : allIdx2In p d l m i k = true := by
  rw [allIdx2In_iff] at h₁ h₂ ⊢
  intro t hit htk htl
  by_cases htj : t < j
  · exact h₁ t hit htj htl
  · exact h₂ t (by omega) htk htl

/-- **The positions `[0, n)` of a list of at most `n` elements** check as the whole list. -/
theorem allIdx2_of_allIdx2In {α β : Type} [Inhabited α] {p : ℕ → α → β → Bool} {d : β}
    {l : List α} {m : List β} {n : ℕ} (h : allIdx2In p d l m 0 n = true) (hn : l.length ≤ n) :
    allIdx2 p d l m 0 = true := by
  rw [allIdx2In_iff] at h
  rw [allIdx2_iff]
  intro t ht
  rw [Nat.zero_add]
  exact h t (Nat.zero_le _) (by omega) ht

variable (ir : RealizedProgram) (primeNodes : ℕ → List String)

variable (L : ℕ → ℕ → Option Ivl)

end GordieHowe.RealizedProgram
