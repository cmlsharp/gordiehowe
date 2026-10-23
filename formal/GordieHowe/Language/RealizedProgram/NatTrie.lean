-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

@[expose] public section

/-!
# GordieHowe: a finite map on the naturals for kernel reduction

`NatTrie α` is a binary trie keyed by naturals: key `0` at the root, key `2m + 1` at key `m` of the
first subtrie and key `2m + 2` at key `m` of the second. A lookup or an update reads `O(log k)`
nodes, with `Nat` division and remainder, which the kernel evaluates on literals by GMP; a list
lookup `List.getD l k` reads `k` cells. The validity checkers of the plan's program
(`GordieHowe/Language/RealizedProgram/Check.lean`) keep their tables in it.

`NatTrie.set` recurses on a fuel argument (`k + 1`), not by well-founded recursion, so the kernel
reduces it.
-/

namespace GordieHowe.RealizedProgram

/-- **A binary trie keyed by naturals**: empty, or a node with the entry of key `0` and the
subtries of the odd keys (`2m + 1` at `m`) and of the even positive keys (`2m + 2` at `m`). -/
inductive NatTrie (α : Type) where
  /-- The empty map. -/
  | nil
  /-- The entry of key `0`, and the subtries of the odd and the even positive keys. -/
  | node (root : Option α) (odd even : NatTrie α)
  deriving Inhabited

namespace NatTrie

variable {α : Type}

/-- The entry of key `0`. -/
def root : NatTrie α → Option α
  | nil => none
  | node a _ _ => a

/-- The subtrie of the odd keys. -/
def odd : NatTrie α → NatTrie α
  | nil => nil
  | node _ o _ => o

/-- The subtrie of the even positive keys. -/
def even : NatTrie α → NatTrie α
  | nil => nil
  | node _ _ e => e

/-- **The entry of key `k`.** -/
def get? : NatTrie α → Nat → Option α
  | nil, _ => none
  | node a o e, k =>
    match k with
    | 0 => a
    | k + 1 => if k % 2 = 0 then get? o (k / 2) else get? e (k / 2)

/-- **The entry of key `k`**, `d` when absent. -/
def getD (t : NatTrie α) (k : Nat) (d : α) : α := (t.get? k).getD d

/-- **The map with key `k` set to `x`**, with `f` levels of fuel (enough when `k < f`). -/
def setAux : Nat → NatTrie α → Nat → α → NatTrie α
  | 0, t, _, _ => t
  | f + 1, t, k, x =>
    match k with
    | 0 => node (some x) t.odd t.even
    | k + 1 =>
      if k % 2 = 0 then node t.root (setAux f t.odd (k / 2) x) t.even
      else node t.root t.odd (setAux f t.even (k / 2) x)

/-- **The map with key `k` set to `x`.** -/
def set (t : NatTrie α) (k : Nat) (x : α) : NatTrie α := setAux (k + 1) t k x

@[simp] theorem get?_nil (k : Nat) : (nil : NatTrie α).get? k = none := by
  cases k <;> rfl

theorem get?_zero (t : NatTrie α) : t.get? 0 = t.root := by
  cases t <;> rfl

theorem get?_succ (t : NatTrie α) (k : Nat) :
    t.get? (k + 1) = if k % 2 = 0 then t.odd.get? (k / 2) else t.even.get? (k / 2) := by
  cases t <;> simp [get?, odd, even]

theorem get?_setAux :
    ∀ (f : Nat) (t : NatTrie α) (k j : Nat) (x : α), k < f →
      (setAux f t k x).get? j = if j = k then some x else t.get? j
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, t, k, j, x, h => by
    cases k with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => simp only [setAux, get?, get?_succ t j]; simp
    | succ k =>
      have hk : k / 2 < f := by omega
      cases j with
      | zero => simp only [setAux]; split <;> simp [get?, get?_zero]
      | succ j =>
        simp only [setAux, get?_succ t j]
        split <;> rename_i hk2
        · simp only [get?, get?_setAux f t.odd (k / 2) (j / 2) x hk]
          split <;> rename_i hj2 <;> by_cases hjk : j = k <;> simp_all <;> omega
        · simp only [get?, get?_setAux f t.even (k / 2) (j / 2) x hk]
          split <;> rename_i hj2 <;> by_cases hjk : j = k <;> simp_all <;> omega

/-- **Setting a key changes only that key.** -/
theorem get?_set (t : NatTrie α) (k j : Nat) (x : α) :
    (t.set k x).get? j = if j = k then some x else t.get? j :=
  get?_setAux _ t k j x (Nat.lt_succ_self k)

theorem getD_set (t : NatTrie α) (k j : Nat) (x d : α) :
    (t.set k x).getD j d = if j = k then x else t.getD j d := by
  simp only [getD, get?_set]
  split <;> rfl

end NatTrie

end GordieHowe.RealizedProgram
