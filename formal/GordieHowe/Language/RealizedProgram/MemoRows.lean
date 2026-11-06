-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Check
public import GordieHoweNative.Language.RealizedProgram.MemoRows

public section

namespace GordieHowe.RealizedProgram

/-- Accepted supplied entries give exactly the canonical memo table, for any
recurrence, default, initial index, and initial table. -/
theorem memoRowsB_sound {γ β : Type} [DecidableEq β]
    (F : (Nat → β) → Nat → γ → β) (d : β) :
    ∀ (xs : List γ) (ys : List β) (j : Nat) (t : NatTrie β),
      memoRowsB F d xs ys j t = true → memoAux F d xs j t = memoRowsTable ys j t
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp only [memoRowsB_nil_cons, Bool.false_eq_true] at h
  | _ :: _, [], _, _, h => by simp only [memoRowsB_cons_nil, Bool.false_eq_true] at h
  | x :: xs, y :: ys, j, t, h => by
    have hs : F (t.getD · d) j x = y ∧ memoRowsB F d xs ys (j+1) (t.set j y) = true := by
      simpa only [memoRowsB_cons_cons, Bool.and_eq_true, decide_eq_true_eq] using h
    rw [memoAux_cons, memoRowsTable_cons, hs.1]
    exact memoRowsB_sound F d xs ys (j+1) (t.set j y) hs.2

/-- Accepted supplied rows are the exact canonical list, including order and
multiplicity, after any accumulated prefix. -/
theorem memoRowsB_soundList {γ β : Type} [DecidableEq β]
    (F : (Nat → β) → Nat → γ → β) (d : β) :
    ∀ (xs : List γ) (ys : List β) (j : Nat) (t : NatTrie β) (acc : List β),
      memoRowsB F d xs ys j t = true →
      (memoAuxL F d xs j t acc).2 = acc.reverse ++ ys
  | [], [], _, _, _, _ => by simp [memoAuxL_nil]
  | [], _ :: _, _, _, _, h => by simp only [memoRowsB_nil_cons, Bool.false_eq_true] at h
  | _ :: _, [], _, _, _, h => by simp only [memoRowsB_cons_nil, Bool.false_eq_true] at h
  | x :: xs, y :: ys, j, t, acc, h => by
    have hs : F (t.getD · d) j x = y ∧ memoRowsB F d xs ys (j+1) (t.set j y) = true := by
      simpa only [memoRowsB_cons_cons, Bool.and_eq_true, decide_eq_true_eq] using h
    rw [memoAuxL_cons, hs.1,
      memoRowsB_soundList F d xs ys (j+1) (t.set j y) (y :: acc) hs.2]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- The canonical memo entries pass the supplied-row checker, without an
acyclicity or well-formedness premise. -/
theorem memoRowsB_complete {γ β : Type} [DecidableEq β]
    (F : (Nat → β) → Nat → γ → β) (d : β) :
    ∀ xs j t, memoRowsB F d xs (memoAuxL F d xs j t []).2 j t = true
  | [], _, _ => rfl
  | x :: xs, j, t => by
    rw [memoAuxL_cons, memoAuxL_snd]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    rw [memoRowsB_cons_cons]
    simp only [decide_true, Bool.true_and]
    exact memoRowsB_complete F d xs (j+1) (t.set j (F (t.getD · d) j x))

end GordieHowe.RealizedProgram
