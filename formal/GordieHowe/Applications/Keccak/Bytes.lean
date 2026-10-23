-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

/-!
# Byte strings and streams

Shared by both signature specifications.  `SHAKE256` enters every
specification through the function type `XOF`.
-/

namespace GordieHowe

/-- A hash function from bytes and a requested output length to bytes. -/
abbrev XOF := List ℕ → ℕ → List ℕ

/-- 16-bit big-endian samples from a fixed-length byte string: sample `i` is
formed from bytes `2i` and `2i+1`. -/
def samples16 {S : ℕ} (bytes : Fin (2 * S) → ℕ) (i : Fin S) : ℕ :=
  256 * bytes ⟨2 * (i : ℕ), by have := i.isLt; omega⟩
    + bytes ⟨2 * (i : ℕ) + 1, by have := i.isLt; omega⟩

/-- The byte at position `j` recovered from `S` 16-bit samples: the high byte
of the sample at `j / 2` if `j` is even, the low byte if `j` is odd. Inverse
to `samples16`. -/
def sampleByte {S : ℕ} (v : Fin S → ℕ) (j : Fin (2 * S)) : ℕ :=
  if (j : ℕ) % 2 = 0 then v ⟨(j : ℕ) / 2, by have := j.isLt; omega⟩ / 256
  else v ⟨(j : ℕ) / 2, by have := j.isLt; omega⟩ % 256

theorem sampleByte_lt {S : ℕ} {v : Fin S → ℕ} (hv : ∀ i, v i < 65536) (j : Fin (2 * S)) :
    sampleByte v j < 256 := by
  unfold sampleByte
  have := hv ⟨(j : ℕ) / 2, by have := j.isLt; omega⟩
  split_ifs <;> omega

theorem samples16_sampleByte {S : ℕ} (v : Fin S → ℕ) (hv : ∀ i, v i < 65536) (i : Fin S) :
    samples16 (fun j => sampleByte v j) i = v i := by
  have hidx1 : (⟨((⟨2 * (i : ℕ), by have := i.isLt; omega⟩ : Fin (2 * S)) : ℕ) / 2,
      by have := i.isLt; omega⟩ : Fin S) = i := by
    apply Fin.ext
    show (2 * (i : ℕ)) / 2 = (i : ℕ)
    omega
  have hidx2 : (⟨((⟨2 * (i : ℕ) + 1, by have := i.isLt; omega⟩ : Fin (2 * S)) : ℕ) / 2,
      by have := i.isLt; omega⟩ : Fin S) = i := by
    apply Fin.ext
    show (2 * (i : ℕ) + 1) / 2 = (i : ℕ)
    omega
  have hv' := hv i
  unfold samples16 sampleByte
  dsimp only
  rw [if_pos (show (2 * (i : ℕ)) % 2 = 0 by omega),
    if_neg (show ¬ (2 * (i : ℕ) + 1) % 2 = 0 by omega),
    hidx1, hidx2]
  omega

theorem sampleByte_samples16 {S : ℕ} (bytes : Fin (2 * S) → ℕ) (hb : ∀ j, bytes j < 256)
    (j : Fin (2 * S)) : sampleByte (fun i => samples16 bytes i) j = bytes j := by
  have hqlt : (j : ℕ) / 2 < S := by have := j.isLt; omega
  have hsamp : samples16 bytes (⟨(j : ℕ) / 2, hqlt⟩ : Fin S)
      = 256 * bytes ⟨2 * ((j : ℕ) / 2), by omega⟩
        + bytes ⟨2 * ((j : ℕ) / 2) + 1, by omega⟩ := rfl
  unfold sampleByte
  dsimp only
  rcases Nat.mod_two_eq_zero_or_one (j : ℕ) with h0 | h1
  · rw [if_pos h0, hsamp]
    have hb1 := hb ⟨2 * ((j : ℕ) / 2), by omega⟩
    have hb2 := hb ⟨2 * ((j : ℕ) / 2) + 1, by omega⟩
    have hjeq : j = (⟨2 * ((j : ℕ) / 2), by omega⟩ : Fin (2 * S)) :=
      Fin.ext (show (j : ℕ) = 2 * ((j : ℕ) / 2) by omega)
    conv_rhs => rw [hjeq]
    omega
  · rw [if_neg (by omega), hsamp]
    have hb1 := hb ⟨2 * ((j : ℕ) / 2), by omega⟩
    have hb2 := hb ⟨2 * ((j : ℕ) / 2) + 1, by omega⟩
    have hjeq : j = (⟨2 * ((j : ℕ) / 2) + 1, by omega⟩ : Fin (2 * S)) :=
      Fin.ext (show (j : ℕ) = 2 * ((j : ℕ) / 2) + 1 by omega)
    conv_rhs => rw [hjeq]
    omega

/-- Pairing bytes into 16-bit big-endian samples is a bijection between `2S`
bytes below `256` and `S` samples below `65536`: `samples16` read as the
forward direction, `sampleByte` as the inverse. -/
def samples16Equiv (S : ℕ) : (Fin (2 * S) → Fin 256) ≃ (Fin S → Fin 65536) where
  toFun bytes i := ⟨samples16 (fun j => (bytes j : ℕ)) i, by
    unfold samples16
    dsimp only
    have h1 := (bytes ⟨2 * (i : ℕ), by have := i.isLt; omega⟩).isLt
    have h2 := (bytes ⟨2 * (i : ℕ) + 1, by have := i.isLt; omega⟩).isLt
    omega⟩
  invFun v j := ⟨sampleByte (fun i => (v i : ℕ)) j,
    sampleByte_lt (fun i => (v i).isLt) j⟩
  left_inv bytes := by
    funext j
    apply Fin.ext
    exact sampleByte_samples16 (fun j' => (bytes j' : ℕ)) (fun j' => (bytes j').isLt) j
  right_inv v := by
    funext i
    apply Fin.ext
    exact samples16_sampleByte (fun i' => (v i' : ℕ)) (fun i' => (v i').isLt) i

theorem samples16Equiv_apply {S : ℕ} (bytes : Fin (2 * S) → Fin 256) (i : Fin S) :
    ((samples16Equiv S bytes i : ℕ)) = samples16 (fun j => (bytes j : ℕ)) i := rfl

/-- The first `n` entries of `stream` satisfying `accept`, in order, or `none` if fewer than `n`
exist. Every ordered-selection gadget is proved against this. -/
def firstAccepted (accept : ℕ → Bool) {S : ℕ} (stream : Fin S → ℕ) (n : ℕ) : Option (Fin n → ℕ) :=
  let acc := (List.ofFn stream).filter accept
  if h : n ≤ acc.length then
    some fun i => acc[i]'(by have := i.isLt; omega)
  else none

/-! ### List lemmas: relating a prefix's accepted count to the filtered list

These are general facts about `List.filter`, `List.take` and `List.countP`,
kept here because they exist to support `firstAccepted`. -/

/-- Filtering the first `i` entries of a list is the same as taking the first
`(l.take i).countP p` entries of the fully filtered list: the two ways of
describing "the accepted entries before position `i`" agree. -/
theorem _root_.List.take_filter_eq_filter_take_countP {α : Type*} (p : α → Bool) :
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
theorem _root_.List.countP_take_le {α : Type*} (p : α → Bool) (l : List α) (i : ℕ) :
    (l.take i).countP p ≤ (l.filter p).length := by
  rw [List.countP_eq_length_filter]
  exact (List.Sublist.filter p (List.take_sublist i l)).length_le

/-- If position `i` is accepted, it is the `(l.take i).countP p`-th entry of
the filtered list: the number of accepted entries strictly before `i` is
exactly its index after filtering. This is the combinatorial core of
`firstAccepted`: it says a selected position's rank among the accepted
entries is its prefix count. -/
theorem _root_.List.getElem_filter_of_countP_take {α : Type*} (p : α → Bool) (l : List α)
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
theorem _root_.List.exists_getElem_countP_take_eq {α : Type*} (p : α → Bool) (l : List α)
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

/-- `firstAccepted` unfolded: it succeeds exactly when at least `n` entries of
`stream` are accepted, and then `out` is the entrywise readout of the filtered
list. -/
theorem firstAccepted_eq_some_iff {accept : ℕ → Bool} {S : ℕ} {stream : Fin S → ℕ} {n : ℕ}
    {out : Fin n → ℕ} :
    firstAccepted accept stream n = some out ↔
      ∃ h : n ≤ ((List.ofFn stream).filter accept).length,
        ∀ i : Fin n, out i = ((List.ofFn stream).filter accept)[i]'(by have := i.isLt; omega) := by
  unfold firstAccepted
  dsimp only
  by_cases h : n ≤ ((List.ofFn stream).filter accept).length
  · rw [dite_eq_left h]
    constructor
    · intro heq
      refine ⟨h, fun i => ?_⟩
      have := congrFun (Option.some.inj heq) i
      exact this.symm
    · rintro ⟨h', hout⟩
      congr 1
      funext i
      exact (hout i).symm
  · rw [dite_eq_right h]
    constructor
    · exact fun heq => absurd heq (by simp)
    · rintro ⟨h', -⟩
      exact absurd h' h

theorem firstAccepted_accept {accept : ℕ → Bool} {S n : ℕ} {stream : Fin S → ℕ}
    {out : Fin n → ℕ} (h : firstAccepted accept stream n = some out) (i : Fin n) :
    accept (out i) = true := by
  obtain ⟨hlen, hout⟩ := firstAccepted_eq_some_iff.mp h
  rw [hout i]
  exact (List.mem_filter.mp (List.getElem_mem (by omega))).2

/-- `firstAccepted` fails exactly when fewer than `n` entries of `stream` are
accepted. -/
theorem firstAccepted_eq_none_iff {accept : ℕ → Bool} {S : ℕ} {stream : Fin S → ℕ} {n : ℕ} :
    firstAccepted accept stream n = none ↔
      ((List.ofFn stream).filter accept).length < n := by
  unfold firstAccepted
  by_cases h : n ≤ ((List.ofFn stream).filter accept).length
  · rw [dif_pos h]
    simp only [reduceCtorEq, false_iff]
    omega
  · rw [dif_neg h]
    simp only [true_iff]
    omega

end GordieHowe
