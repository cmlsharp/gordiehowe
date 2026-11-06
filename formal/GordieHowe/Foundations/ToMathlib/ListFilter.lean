-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# A prefix's accepted count and the filtered list

General facts about `List.filter`, `List.take` and `List.countP`: the accepted entries before
position `i` are a prefix of the filtered list, and entry `k` of the filtered list is the accepted
entry with `k` accepted entries before it (`GordieHowe.firstAccepted_eq_some_iff`).
-/

/-- Filtering the first `i` entries of a list is the same as taking the first
`(l.take i).countP p` entries of the fully filtered list: the two ways of
describing "the accepted entries before position `i`" agree. -/
theorem List.take_filter_eq_filter_take_countP {α : Type*} (p : α → Bool) :
    ∀ (l : List α) (i : ℕ), (l.take i).filter p = (l.filter p).take ((l.take i).countP p) := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons a t ih =>
    intro i
    match i with
    | 0 => simp
    | (m + 1) =>
      by_cases ha : p a = true
      · simp [ha, ih m]
      · simp [ha, ih m]

/-- The number of accepted entries in a prefix is at most the number accepted
overall. -/
theorem List.countP_take_le {α : Type*} (p : α → Bool) (l : List α) (i : ℕ) :
    (l.take i).countP p ≤ (l.filter p).length := by
  rw [List.countP_eq_length_filter]
  exact (List.Sublist.filter p (List.take_sublist i l)).length_le

/-- If position `i` is accepted, it is the `(l.take i).countP p`-th entry of
the filtered list: the number of accepted entries strictly before `i` is
exactly its index after filtering. This is the combinatorial core of
`firstAccepted`: it says a selected position's rank among the accepted
entries is its prefix count. -/
theorem List.getElem_filter_of_countP_take {α : Type*} (p : α → Bool) (l : List α)
    (i : ℕ) (hi : i < l.length) (hp : p l[i] = true) :
    ∃ hj : (l.take i).countP p < (l.filter p).length,
      (l.filter p)[(l.take i).countP p]'hj = l[i] := by
  have hj1 : (l.take (i + 1)).countP p = (l.take i).countP p + 1 := by
    rw [List.take_succ_eq_append_getElem hi, List.countP_append]
    simp [hp]
  have key0 : (l.filter p).take ((l.take i).countP p) ++ [l[i]]
      = (l.filter p).take ((l.take (i + 1)).countP p) := by
    calc (l.filter p).take ((l.take i).countP p) ++ [l[i]]
        = (l.take i).filter p ++ [l[i]] := by
          rw [List.take_filter_eq_filter_take_countP p l i]
      _ = (l.take i).filter p ++ (List.filter p [l[i]]) := by simp [hp]
      _ = List.filter p (l.take i ++ [l[i]]) := by rw [List.filter_append]
      _ = List.filter p (l.take (i + 1)) := by rw [List.take_succ_eq_append_getElem hi]
      _ = (l.filter p).take ((l.take (i + 1)).countP p) :=
          List.take_filter_eq_filter_take_countP p l (i + 1)
  generalize hjdef : (l.take i).countP p = j at *
  have hle : j + 1 ≤ (l.filter p).length := hj1 ▸ List.countP_take_le p l (i + 1)
  have hj : j < (l.filter p).length := by omega
  refine ⟨hj, ?_⟩
  rw [hj1] at key0
  have hlen : (List.take j (l.filter p)).length = j := by
    rw [List.length_take]; omega
  have h1 : ((l.filter p).take j ++ [l[i]])[j]? = some l[i] := by
    rw [List.getElem?_append_right (by omega)]
    simp [hlen]
  rw [key0, List.getElem?_take_of_lt (Nat.lt_succ_self j)] at h1
  rw [List.getElem?_eq_getElem hj] at h1
  simpa using h1

/-- Converse of `List.getElem_filter_of_countP_take`: every rank below the
length of the filtered list is realized by some accepted entry of the
original list at that rank. -/
theorem List.exists_getElem_countP_take_eq {α : Type*} (p : α → Bool) (l : List α)
    (k : ℕ) (hk : k < (l.filter p).length) :
    ∃ (i : ℕ) (hi : i < l.length), p l[i] = true ∧ (l.take i).countP p = k := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a t ih =>
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha] at hk
      match k, hk with
      | 0, hk =>
        refine ⟨0, by simp, by simpa using ha, by simp⟩
      | (m + 1), hk =>
        have hm : m < (t.filter p).length := by simpa using hk
        obtain ⟨i0, hi0, hp0, hc0⟩ := ih m hm
        refine ⟨i0 + 1, by simpa using hi0, ?_, ?_⟩
        · simpa using hp0
        · simp [ha, hc0]
    · rw [List.filter_cons_of_neg (by simpa using ha)] at hk
      obtain ⟨i0, hi0, hp0, hc0⟩ := ih k hk
      refine ⟨i0 + 1, by simpa using hi0, ?_, ?_⟩
      · simpa using hp0
      · simp [ha, hc0]
