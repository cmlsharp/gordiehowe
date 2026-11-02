-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Std

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.NatTrie`

The definitions of `GordieHowe.Language.RealizedProgram.NatTrie` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/NatTrie.lean`, which imports this module.
-/

@[expose] public section

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

/-- **The entries of a list at its even positions** `0, 2, 4, …`, in order. -/
def evens : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: r => x :: evens r

theorem getElem?_evens : ∀ (l : List α) (m : Nat), (evens l)[m]? = l[2 * m]?
  | [], _ => rfl
  | [_], 0 => rfl
  | [_], m + 1 => by
    simp only [evens, List.getElem?_cons_succ, List.getElem?_nil]
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, List.getElem?_cons_succ, List.getElem?_nil]
  | _ :: _ :: _, 0 => rfl
  | _ :: _ :: r, m + 1 => by
    rw [evens, List.getElem?_cons_succ, getElem?_evens r m,
      show 2 * (m + 1) = 2 * m + 1 + 1 by omega, List.getElem?_cons_succ, List.getElem?_cons_succ]

theorem length_evens_le : ∀ l : List α, (evens l).length ≤ l.length
  | [] => Nat.le_refl _
  | [_] => Nat.le_refl _
  | _ :: _ :: r => by
    have := length_evens_le r
    simp only [evens, List.length_cons]
    omega

/-- **The trie of a list's entries**, with a level of fuel per cell of `f` (enough when the list has
at most as many entries as `f`). -/
def ofSeqAux : List α → List α → NatTrie α
  | [], _ => nil
  | _ :: _, [] => nil
  | _ :: f, x :: xs => node (some x) (ofSeqAux f (evens xs)) (ofSeqAux f (evens xs.tail))

/-- **The entries of a list at its even and at its odd positions**, in one walk by the recursor
(`splitK_eq`). -/
noncomputable def splitK (l : List α) : List α × List α :=
  @List.rec α (fun _ => List α × List α) ([], []) (fun x _ ih => (x :: ih.2, ih.1)) l

theorem splitK_eq : ∀ l : List α, splitK l = (evens l, evens l.tail)
  | [] => rfl
  | [_] => rfl
  | x :: y :: r => by
    change (x :: (splitK (y :: r)).2, (splitK (y :: r)).1) = _
    rw [splitK_eq (y :: r)]
    rfl

/-- **`ofSeqAux`, by the recursors** (`ofSeqK_eq`): each node's subtries from one `splitK` of the
rest. -/
noncomputable def ofSeqK (f l : List α) : NatTrie α :=
  @List.rec α (fun _ => List α → NatTrie α) (fun _ => nil)
    (fun _ _ ih l => @List.casesOn α (fun _ => NatTrie α) l nil fun x xs =>
      node (some x) (ih (splitK xs).1) (ih (splitK xs).2)) f l

theorem ofSeqK_eq : ∀ f l : List α, ofSeqK f l = ofSeqAux f l
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: f, x :: xs => by
    change node (some x) (ofSeqK f (splitK xs).1) (ofSeqK f (splitK xs).2) = _
    rw [ofSeqK_eq f, ofSeqK_eq f, splitK_eq, ofSeqAux]

@[csimp] theorem ofSeqK_csimp : @ofSeqK = @ofSeqAux := by
  funext α f l
  exact ofSeqK_eq f l

/-- **The trie of a list's entries**, entry `k` at key `k` (`ofSeq_eq`). -/
def ofSeq (l : List α) : NatTrie α := ofSeqK l l

theorem ofSeq_eq (l : List α) : ofSeq l = ofSeqAux l l := ofSeqK_eq l l

theorem get?_ofSeqAux :
    ∀ (f l : List α), l.length ≤ f.length → ∀ k, (ofSeqAux f l).get? k = l[k]?
  | [], [], _, k => by simp [ofSeqAux]
  | [], _ :: _, h, _ => absurd h (by simp)
  | _ :: _, [], _, k => by simp [ofSeqAux]
  | _ :: _, _ :: _, _, 0 => rfl
  | _ :: f, x :: xs, h, k + 1 => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    have he := Nat.le_trans (length_evens_le xs) h
    have ho : (evens xs.tail).length ≤ f.length :=
      Nat.le_trans (length_evens_le xs.tail) (by rw [List.length_tail]; omega)
    rw [ofSeqAux, List.getElem?_cons_succ]
    simp only [get?]
    split <;> rename_i hk
    · rw [get?_ofSeqAux f _ he, getElem?_evens]
      congr 1
      omega
    · rw [get?_ofSeqAux f _ ho, getElem?_evens, List.getElem?_tail]
      congr 1
      omega

/-- **The trie of a list reads as the list** at every key. -/
theorem get?_ofSeq (l : List α) (k : Nat) : (ofSeq l).get? k = l[k]? := by
  rw [ofSeq_eq]
  exact get?_ofSeqAux _ l (Nat.le_refl _) k

theorem getD_ofSeq (l : List α) (k : Nat) (d : α) : (ofSeq l).getD k d = l.getD k d := by
  rw [getD, get?_ofSeq, List.getD_eq_getElem?_getD]

end NatTrie

end GordieHowe.RealizedProgram
