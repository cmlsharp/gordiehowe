-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Check

public section

namespace GordieHowe.RealizedProgram

/-- Check supplied memo entries in order, using only entries already checked.
A length mismatch is rejected. The recurrence may refer to any index, including
current and later indices, which read the supplied default until set. -/
@[expose] def memoRowsB {γ β : Type} [DecidableEq β]
    (F : (Nat → β) → Nat → γ → β) (d : β) :
    List γ → List β → Nat → NatTrie β → Bool
  | [], [], _, _ => true
  | x :: xs, y :: ys, j, t =>
      decide (F (t.getD · d) j x = y) && memoRowsB F d xs ys (j + 1) (t.set j y)
  | _, _, _, _ => false

/-- Empty input and supplied lists pass. -/
theorem memoRowsB_nil_nil {γ β : Type} [DecidableEq β]
    (F : (Nat → β) → Nat → γ → β) (d : β) (j : Nat) (t : NatTrie β) :
    memoRowsB F d [] [] j t = true := rfl

/-- Extra supplied rows are rejected. -/
theorem memoRowsB_nil_cons {γ β : Type} [DecidableEq β]
    (F : (Nat → β) → Nat → γ → β) (d y : β) (ys : List β)
    (j : Nat) (t : NatTrie β) : memoRowsB F d [] (y :: ys) j t = false := rfl

/-- Missing supplied rows are rejected. -/
theorem memoRowsB_cons_nil {γ β : Type} [DecidableEq β]
    (F : (Nat → β) → Nat → γ → β) (d : β) (x : γ) (xs : List γ)
    (j : Nat) (t : NatTrie β) : memoRowsB F d (x :: xs) [] j t = false := rfl

/-- Check the current row before continuing with that row in the prefix table. -/
theorem memoRowsB_cons_cons {γ β : Type} [DecidableEq β]
    (F : (Nat → β) → Nat → γ → β) (d : β) (x : γ) (xs : List γ)
    (y : β) (ys : List β) (j : Nat) (t : NatTrie β) :
    memoRowsB F d (x :: xs) (y :: ys) j t =
      (decide (F (t.getD · d) j x = y) && memoRowsB F d xs ys (j+1) (t.set j y)) := rfl

/-- Set successive entries of a table from supplied rows, starting at `j`.
The checker establishes equality with the canonical memo table before a consumer
can use these entries as facts about that recurrence. -/
@[expose] def memoRowsTable {β : Type} : List β → Nat → NatTrie β → NatTrie β
  | [], _, t => t
  | y :: ys, j, t => memoRowsTable ys (j + 1) (t.set j y)

/-- An empty supplied list leaves the table unchanged. -/
theorem memoRowsTable_nil {β : Type} (j : Nat) (t : NatTrie β) :
    memoRowsTable [] j t = t := rfl

/-- Insert the first supplied row before the remainder. -/
theorem memoRowsTable_cons {β : Type} (y : β) (ys : List β) (j : Nat) (t : NatTrie β) :
    memoRowsTable (y :: ys) j t = memoRowsTable ys (j+1) (t.set j y) := rfl

end GordieHowe.RealizedProgram
