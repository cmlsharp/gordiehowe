-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Lemmas
public import GordieHowe.Language.RealizedProgram.NatTrie
public import GordieHoweNative.Language.RealizedProgram.Check

@[expose] public section

/-!
# GordieHowe: the checker of the plan's program

Boolean checks of the validity conditions (`GordieHowe/Language/RealizedProgram/Valid.lean`), written for kernel reduction and run by
`decide +kernel`: `WellFormed` takes its `Decidable` instance from `wellFormedB`
(`wellFormedB_iff`), and `ReadsSound`, `DegreesSound` and `TargetsAdmit` are decided through
`readsB`, `degreesB` and `targetsB` (`readsB_iff`, `degreesB_iff`, `targetsB_iff`). The other
conditions over the values are checked in `GordieHowe/Language/RealizedProgram/CheckValues.lean`.

**Value table.** A check over the values reads the value it visits from the list (`allIdx`) and any
other value through `valT` (`valueT`, `O(log v)` steps), and a set of naturals through `natSet`
(a batch's parts, a circuit's predicates and input blocks), not by a list lookup or a list
membership per element.

**Memoized tables.** The definitions of `GordieHowe/Language/RealizedProgram/Valid.lean` follow a shared expression
through fuel (`GordieHowe.RealizedProgram.refClosure`, `GordieHowe.RealizedProgram.refLen`, `GordieHowe.RealizedProgram.refDeg`, `GordieHowe.RealizedProgram.refZero`) and a
value through the values it reads (`GordieHowe.RealizedProgram.nodeReads`, `GordieHowe.RealizedProgram.nodeDegAt`), recomputing an entry
at each reference: their cost is that of the expressions written as trees. The checker computes each
property once per entry, in index order (`memo`: entry `j` from the entries it reads, all of
smaller index), and keeps the entries in a `NatTrie`:

* per shared expression: the closures such as the values read, deduplicated (`closureT`), the length
  (`lenT`), the degree for given value degrees (`degT`) and the vanishing at zero (`zeroT`);
* per value: the reads (`readsT`) and the per-coordinate degrees in each challenge (`valDegT`),
  with the shared expressions' per-coordinate degrees (`refDegVT`), kept as arithmetic runs
  (`RunVec`, `GordieHowe/Language/RealizedProgram/RunVec.lean`): an expression of thousands of coordinates has a few
  runs, the powers of a challenge one.

A table equals its recursive definition when the shared expressions read only entries of smaller
index (`RefsOrdered`) and, for the per-value tables, the values read only values of smaller
identifier (`WellFormed`): `memo_getD` and `iter_rel_memo` in general, then one lemma per table.

**Traversal.** A property of every position of a list is checked in one pass (`allIdx`), not by a
lookup `List.getD l k` per position, which costs `k` steps; the predicates are looked up in a
`NatTrie` (`predT`). The kernel does not share the evaluation of a term an argument passes into a
loop: an index map's range check compares its largest entry with the operand's length once
(`IndexMap.inRangeNat`), not each run's ends.

The definitions are in `GordieHoweNative/Language/RealizedProgram/Check.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export

/-- A nondefault shared-expression lookup has a valid index. -/
theorem expr_lt_of_ne_default {ir : RealizedProgram} {k : ℕ}
    (h : ir.expr k ≠ default) : k < ir.exprs.length := by
  by_contra hn
  apply h
  rw [ir.expr_eq_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (Nat.le_of_not_lt hn), Option.getD_none]

/-! ## Lists -/

theorem allIdx_nil {α : Type} (p : ℕ → α → Bool) (i : ℕ) : allIdx p [] i = true := rfl

theorem allIdx_iff {α : Type} [Inhabited α] (p : ℕ → α → Bool) :
    ∀ (l : List α) (i : ℕ), allIdx p l i = true ↔ ∀ j < l.length, p (i + j) (l.getD j default) = true
  | [], i => by simp [allIdx_nil]
  | x :: xs, i => by
    rw [allIdx_cons, Bool.and_eq_true, allIdx_iff p xs (i + 1)]
    constructor
    · rintro ⟨h0, h⟩ j hj
      cases j with
      | zero => simpa using h0
      | succ j =>
        have := h j (by simpa using hj)
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using this
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun j hj => ?_⟩
      have := h (j + 1) (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

/-! ## Ranges of positions

A check of every position of a long list splits into checks of the ranges of positions `[i, j)`
(`allIdxIn`), which join with no re-check (`allIdxIn_append`) and give the whole check
(`allIdx_of_allIdxIn`); a check of every number below a bound splits the same way (`allNatIn`). The
kernel evaluates a range's check by walks written with the recursors: `dropK` passes the positions
before `i` with one `List.casesOn` each, evaluating none of their elements, and `allIdxN` checks the
next `j - i` positions, matching on the position (`Nat.casesOn`) at each step, so the kernel keeps it
a literal. Compiled code runs `allIdx` of `List.drop` and `List.take` (`allIdxIn_csimp`). -/

/-- **`l.drop n`**, by the recursor on `n` (`dropK_eq`), each step matching on the list. -/
noncomputable def dropK {α : Type} (n : ℕ) (l : List α) : List α :=
  @Nat.rec (fun _ => List α → List α) (fun l => l)
    (fun _ ih l => @List.casesOn α (fun _ => List α) l [] fun _ xs => ih xs) n l

theorem dropK_eq {α : Type} : ∀ (n : ℕ) (l : List α), dropK n l = l.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: xs => dropK_eq n xs

/-- **`l.drop n`**: the code compiled for `dropK`. -/
def dropC {α : Type} (n : ℕ) (l : List α) : List α := l.drop n

@[csimp] theorem dropK_csimp : @dropK = @dropC := by
  funext α n l
  exact dropK_eq n l

/-- **`allIdx p (l.take n) i`**, by the recursor on `n` (`allIdxN_eq`). -/
noncomputable def allIdxN {α : Type} (p : ℕ → α → Bool) (n : ℕ) : List α → ℕ → Bool :=
  @Nat.rec (fun _ => List α → ℕ → Bool) (fun _ _ => true)
    (fun _ ih l i => @List.casesOn α (fun _ => Bool) l true fun x xs =>
      p i x && @Nat.casesOn (fun _ => Bool) i (ih xs 1) fun k => ih xs (k + 2)) n

theorem allIdxN_succ_cons {α : Type} (p : ℕ → α → Bool) (n : ℕ) (x : α) (xs : List α) (i : ℕ) :
    allIdxN p (n + 1) (x :: xs) i = (p i x && allIdxN p n xs (i + 1)) := by
  cases i <;> rfl

theorem allIdxN_eq {α : Type} (p : ℕ → α → Bool) :
    ∀ (n : ℕ) (l : List α) (i : ℕ), allIdxN p n l i = allIdx p (l.take n) i
  | 0, l, _ => by rw [List.take_zero]; rfl
  | _ + 1, [], _ => rfl
  | n + 1, x :: xs, i => by
    rw [allIdxN_succ_cons, allIdxN_eq p n xs, List.take_succ_cons, allIdx_cons]

/-- **A predicate holds at every position of `[i, j)` of a list** (`allIdxIn_iff`), by the
recursors (see above). -/
noncomputable def allIdxIn {α : Type} (p : ℕ → α → Bool) (l : List α) (i j : ℕ) : Bool :=
  allIdxN p (j - i) (dropK i l) i

/-- **`allIdxIn`, by `List.drop` and `List.take`**: the code compiled for it. -/
def allIdxInC {α : Type} (p : ℕ → α → Bool) (l : List α) (i j : ℕ) : Bool :=
  allIdx p ((l.drop i).take (j - i)) i

theorem allIdxIn_eq {α : Type} (p : ℕ → α → Bool) (l : List α) (i j : ℕ) :
    allIdxIn p l i j = allIdx p ((l.drop i).take (j - i)) i := by
  rw [allIdxIn, allIdxN_eq, dropK_eq]

@[csimp] theorem allIdxIn_csimp : @allIdxIn = @allIdxInC := by
  funext α p l i j
  exact allIdxIn_eq p l i j

theorem allIdxIn_iff {α : Type} [Inhabited α] (p : ℕ → α → Bool) (l : List α) (i j : ℕ) :
    allIdxIn p l i j = true ↔
      ∀ k, i ≤ k → k < j → k < l.length → p k (l.getD k default) = true := by
  rw [allIdxIn_eq, allIdx_iff]
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
theorem allIdxIn_append {α : Type} [Inhabited α] {p : ℕ → α → Bool} {l : List α} {i j k : ℕ}
    (h₁ : allIdxIn p l i j = true) (h₂ : allIdxIn p l j k = true) : allIdxIn p l i k = true := by
  rw [allIdxIn_iff] at h₁ h₂ ⊢
  intro t hit htk htl
  by_cases htj : t < j
  · exact h₁ t hit htj htl
  · exact h₂ t (by omega) htk htl

/-- **The positions `[0, n)` of a list of at most `n` elements** check as the whole list. -/
theorem allIdx_of_allIdxIn {α : Type} [Inhabited α] {p : ℕ → α → Bool} {l : List α} {n : ℕ}
    (h : allIdxIn p l 0 n = true) (hn : l.length ≤ n) : allIdx p l 0 = true := by
  rw [allIdxIn_iff] at h
  rw [allIdx_iff]
  intro t ht
  rw [Nat.zero_add]
  exact h t (Nat.zero_le _) (by omega) ht

/-- **A check of every element is one of every position.** -/
theorem all_eq_allIdx {α : Type} (f : α → Bool) :
    ∀ (l : List α) (i : ℕ), l.all f = allIdx (fun _ x => f x) l i
  | [], _ => rfl
  | x :: xs, i => by rw [List.all_cons, allIdx_cons, all_eq_allIdx f xs (i + 1)]

/-- **Two checks of every position, in one walk.** -/
theorem allIdx_and {α : Type} (p q : ℕ → α → Bool) :
    ∀ (l : List α) (i : ℕ), allIdx (fun k x => p k x && q k x) l i = (allIdx p l i && allIdx q l i)
  | [], _ => rfl
  | x :: xs, i => by
    rw [allIdx_cons, allIdx_cons, allIdx_cons, allIdx_and p q xs (i + 1)]
    cases p i x <;> cases q i x <;> simp

/-- **The bit set of the failing positions**: bit `v` is set exactly when `v` is the position,
counted from `i`, of an entry failing `f` there. -/
theorem testBit_failBits {α : Type} (f : ℕ → α → Bool) :
    ∀ (l : List α) (i v : ℕ),
      (failBits f l i).testBit v = true ↔ ∃ j x, l[j]? = some x ∧ v = i + j ∧ f v x = false
  | [], i, v => by simp [failBits]
  | x :: xs, i, v => by
    rw [failBits_cons, show ∀ a b : ℕ, Nat.lor a b = a ||| b from fun _ _ => rfl, Nat.testBit_or,
      Bool.or_eq_true, testBit_failBits f xs]
    constructor
    · rintro (h | ⟨j, y, hy, rfl, hf⟩)
      · cases hx : f i x <;> simp only [hx, Bool.cond_true, Bool.cond_false, Nat.zero_testBit,
          Nat.testBit_two_pow, decide_eq_true_eq, Bool.false_eq_true] at h
        subst h
        exact ⟨0, x, rfl, by omega, hx⟩
      · exact ⟨j + 1, y, by simpa using hy, by omega, hf⟩
    · rintro ⟨j, y, hy, rfl, hf⟩
      cases j with
      | zero =>
        cases hy
        rw [Nat.add_zero] at hf
        left
        simp [hf]
      | succ j =>
        right
        exact ⟨j, y, by simpa using hy, by omega, hf⟩

/-- **The bit test is `f` at the entry**, a default entry past the end. -/
theorem bitTest_eq {α : Type} [Inhabited α] (f : ℕ → α → Bool) (l : List α) (v : ℕ) :
    bitTest (failBits f l 0) l.length (f v default) v = f v (l.getD v default) := by
  unfold bitTest
  split_ifs with hv
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some]
    cases hf : f v l[v]
    · rw [Bool.not_eq_false', testBit_failBits]
      exact ⟨v, l[v], List.getElem?_eq_getElem hv, by omega, hf⟩
    · rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, testBit_failBits]
      rintro ⟨j, y, hy, hj, hf'⟩
      rw [Nat.zero_add] at hj
      subst hj
      rw [List.getElem?_eq_getElem hv] at hy
      cases hy
      rw [hf] at hf'
      cases hf'
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]

/-- **`(List.range' i n).all P`**, by the recursor on `n` (`allNatN_eq`). -/
noncomputable def allNatN (P : ℕ → Bool) (n : ℕ) : ℕ → Bool :=
  @Nat.rec (fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih i => P i && @Nat.casesOn (fun _ => Bool) i (ih 1) fun k => ih (k + 2)) n

theorem allNatN_eq (P : ℕ → Bool) : ∀ (n i : ℕ), allNatN P n i = (List.range' i n).all P
  | 0, _ => rfl
  | n + 1, i => by
    have : allNatN P (n + 1) i = (P i && allNatN P n (i + 1)) := by cases i <;> rfl
    rw [this, allNatN_eq P n (i + 1), List.range'_succ, List.all_cons]

/-- **A predicate holds at every number of `[i, j)`** (`allNatIn_iff`), by the recursor. -/
noncomputable def allNatIn (P : ℕ → Bool) (i j : ℕ) : Bool := allNatN P (j - i) i

@[csimp] theorem allNatIn_csimp : @allNatIn = @allNatInC := by
  funext P i j
  exact allNatN_eq P (j - i) i

theorem allNatIn_iff (P : ℕ → Bool) (i j : ℕ) :
    allNatIn P i j = true ↔ ∀ k, i ≤ k → k < j → P k = true := by
  rw [allNatIn, allNatN_eq, List.all_eq_true]
  simp only [List.mem_range'_1]
  constructor
  · intro h k hik hkj
    exact h k ⟨hik, by omega⟩
  · intro h k ⟨hik, hkj⟩
    exact h k hik (by omega)

/-- **Two consecutive ranges of numbers** check as one. -/
theorem allNatIn_append {P : ℕ → Bool} {i j k : ℕ} (h₁ : allNatIn P i j = true)
    (h₂ : allNatIn P j k = true) : allNatIn P i k = true := by
  rw [allNatIn_iff] at h₁ h₂ ⊢
  intro t hit htk
  by_cases htj : t < j
  · exact h₁ t hit htj
  · exact h₂ t (by omega) htk

/-- **The numbers `[0, n)`** check as every number below `m ≤ n`. -/
theorem all_range_of_allNatIn {P : ℕ → Bool} {n m : ℕ} (h : allNatIn P 0 n = true) (hm : m ≤ n) :
    (List.range m).all P = true := by
  rw [allNatIn_iff] at h
  rw [List.all_eq_true]
  intro t ht
  exact h t (Nat.zero_le _) (by have := List.mem_range.1 ht; omega)

theorem mem_insertAll {α : Type} [DecidableEq α] {x : α} :
    ∀ (acc l : List α), x ∈ insertAll acc l ↔ x ∈ acc ∨ x ∈ l
  | acc, [] => by simp [insertAll]
  | acc, y :: ys => by
    rw [insertAll, mem_insertAll, List.mem_insert_iff, List.mem_cons]
    tauto

/-! ## Tables computed in order -/

theorem memoAuxL_fst {γ β : Type} (F : (ℕ → β) → ℕ → γ → β) (d : β) :
    ∀ (xs : List γ) (j : ℕ) (t : NatTrie β) (acc : List β),
      (memoAuxL F d xs j t acc).1 = memoAux F d xs j t
  | [], _, _, _ => rfl
  | _ :: xs, j, _, _ => memoAuxL_fst F d xs (j + 1) _ _

theorem memo_eq {γ β : Type} (F : (ℕ → β) → ℕ → γ → β) (d : β) (L : List γ) :
    memo F d L = memoAux F d L 0 .nil :=
  memoAuxL_fst F d L 0 .nil []

theorem memoAuxL_snd {γ β : Type} (F : (ℕ → β) → ℕ → γ → β) (d : β) :
    ∀ (xs : List γ) (j : ℕ) (t : NatTrie β) (acc : List β),
      (memoAuxL F d xs j t acc).2 = acc.reverse ++ (memoAuxL F d xs j t []).2
  | [], _, _, _ => by simp [memoAuxL]
  | x :: xs, j, t, acc => by
    rw [memoAuxL, memoAuxL, memoAuxL_snd F d xs (j + 1) _ (_ :: acc),
      memoAuxL_snd F d xs (j + 1) _ [_]]
    simp

theorem memoAux_getD_lt {γ β : Type} (F : (ℕ → β) → ℕ → γ → β) (d : β) :
    ∀ (xs : List γ) (j : ℕ) (t : NatTrie β) (k : ℕ), k < j →
      (memoAux F d xs j t).getD k d = t.getD k d
  | [], _, _, _, _ => rfl
  | _ :: xs, j, t, k, hk => by
    rw [memoAux, memoAux_getD_lt F d xs (j + 1) _ k (by omega), NatTrie.getD_set,
      if_neg (by omega)]

theorem length_memoAuxL_snd {γ β : Type} (F : (ℕ → β) → ℕ → γ → β) (d : β) :
    ∀ (xs : List γ) (j : ℕ) (t : NatTrie β), (memoAuxL F d xs j t []).2.length = xs.length
  | [], _, _ => rfl
  | x :: xs, j, t => by
    rw [memoAuxL, memoAuxL_snd, List.length_append, length_memoAuxL_snd F d xs (j + 1) _]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.length_singleton,
      List.length_cons, List.length_nil]
    omega

theorem getD_memoAuxL_snd {γ β : Type} (F : (ℕ → β) → ℕ → γ → β) (d : β) :
    ∀ (xs : List γ) (j : ℕ) (t : NatTrie β) (k : ℕ), k < xs.length →
      (memoAuxL F d xs j t []).2.getD k d = (memoAux F d xs j t).getD (j + k) d
  | [], _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | x :: xs, j, t, 0, _ => by
    rw [memoAuxL, memoAuxL_snd, memoAux, memoAux_getD_lt F d xs (j + 1) _ (j + 0) (by omega),
      NatTrie.getD_set]
    simp
  | x :: xs, j, t, k + 1, hk => by
    rw [memoAuxL, memoAuxL_snd, memoAux,
      show j + (k + 1) = j + 1 + k by omega]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.getD_cons_succ]
    exact getD_memoAuxL_snd F d xs (j + 1) _ k (by simpa using hk)

section Memo

variable {γ β : Type} [Inhabited γ] {F : (ℕ → β) → ℕ → γ → β} {d : β} {L : List γ}
  {D : ℕ → List ℕ}

/-- **Entries depend on earlier entries**: entry `j` reads only the entries `D j`, each of smaller
index, through the reader `r`. -/
structure MemoDeps (F : (ℕ → β) → ℕ → γ → β) (L : List γ) (D : ℕ → List ℕ) : Prop where
  /-- Each entry reads entries of smaller index. -/
  lt : ∀ j < L.length, ∀ k ∈ D j, k < j
  /-- Each entry depends only on the entries it reads. -/
  congr : ∀ j < L.length, ∀ r r' : ℕ → β, (∀ k ∈ D j, r k = r' k) →
    F r j (L.getD j default) = F r' j (L.getD j default)

theorem memoAux_inv (hF : MemoDeps F L D) :
    ∀ (xs : List γ) (i : ℕ) (t : NatTrie β), L.drop i = xs →
      (∀ j < i, t.getD j d = F (t.getD · d) j (L.getD j default)) →
      ∀ j < L.length, (memoAux F d xs i t).getD j d =
        F ((memoAux F d xs i t).getD · d) j (L.getD j default)
  | [], i, t, hxs, hinv => by
    have hi : L.length ≤ i := by have := congrArg List.length hxs; simp at this; omega
    intro j hj
    exact hinv j (by omega)
  | x :: xs, i, t, hxs, hinv => by
    have hi : i < L.length := by
      by_contra h
      rw [List.drop_eq_nil_of_le (by omega)] at hxs
      cases hxs
    have hx : L.getD i default = x := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      have := congrArg List.head? hxs
      rw [List.head?_drop] at this
      simpa [List.getElem?_eq_getElem hi] using this
    have hrest : L.drop (i + 1) = xs := by
      rw [← List.drop_drop, hxs]
      rfl
    refine memoAux_inv hF xs (i + 1) _ hrest ?_
    intro j hj
    have hagree : ∀ k ∈ D j, ∀ k' ∈ [k], k' < i →
        (t.set i (F (t.getD · d) i x)).getD k' d = t.getD k' d := by
      intro k _ k' _ hk'
      rw [NatTrie.getD_set, ite_eq_right (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [NatTrie.getD_set, ite_eq_right (by omega), hinv j hj]
      refine hF.congr j (by omega) _ _ fun k hk => ?_
      rw [NatTrie.getD_set, ite_eq_right (by have := hF.lt j (by omega) k hk; omega)]
    · rw [NatTrie.getD_set, ite_eq_left rfl, ← hx]
      refine hF.congr j hi _ _ fun k hk => ?_
      rw [NatTrie.getD_set, ite_eq_right (by have := hF.lt j hi k hk; omega)]

/-- **Entry `j` of the table is its step at the table.** -/
theorem memo_getD (hF : MemoDeps F L D) {j : ℕ} (hj : j < L.length) :
    (memo F d L).getD j d = F ((memo F d L).getD · d) j (L.getD j default) :=
  memo_eq F d L ▸ memoAux_inv hF L 0 .nil (by simp) (fun _ h => absurd h (Nat.not_lt_zero _)) j hj

omit [Inhabited γ] in
theorem memoAux_get?_of_le :
    ∀ (xs : List γ) (i : ℕ) (t : NatTrie β), (∀ j, i ≤ j → t.get? j = none) →
      ∀ j, i + xs.length ≤ j → (memoAux F d xs i t).get? j = none
  | [], i, t, h, j, hj => h j (by simpa using hj)
  | x :: xs, i, t, h, j, hj => by
    refine memoAux_get?_of_le xs (i + 1) _ (fun j' hj' => ?_) j (by simp at hj; omega)
    rw [NatTrie.get?_set, ite_eq_right (by omega), h j' (by omega)]

omit [Inhabited γ] in
/-- **The table is `d` past the list's end.** -/
theorem memo_getD_of_le {j : ℕ} (hj : L.length ≤ j) : (memo F d L).getD j d = d := by
  simp only [NatTrie.getD, memo_eq,
    memoAux_get?_of_le L 0 .nil (fun _ _ => NatTrie.get?_nil _) j (by simpa using hj),
    Option.getD_none]

omit [Inhabited γ] in
/-- **The list of a table's entries reads as the table**, past the list's end too. -/
theorem getD_memoList (j : ℕ) : (memoList F d L).getD j d = (memo F d L).getD j d := by
  by_cases hj : j < L.length
  · rw [memoList, getD_memoAuxL_snd F d L 0 .nil j hj, memo_eq, Nat.zero_add]
  · rw [memo_getD_of_le (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
      rw [memoList, length_memoAuxL_snd]; omega), Option.getD_none]

/-- **A recursion with fuel agrees with the table**: when the fuel step `G` and the table's step `F`
are related by `R` wherever their readers are related on the entries read, the recursion `iter`
with `n` levels is related to the table at every entry below `n`. -/
theorem iter_rel_memo {β' : Type} {R : β' → β → Prop} {iter : ℕ → ℕ → β'}
    {G : (ℕ → β') → ℕ → β'} (hiter : ∀ n j, iter (n + 1) j = G (iter n) j)
    (hrel : ∀ j < L.length, ∀ (r : ℕ → β') (r' : ℕ → β), (∀ k ∈ D j, R (r k) (r' k)) →
      R (G r j) (F r' j (L.getD j default)))
    (hF : MemoDeps F L D) :
    ∀ n j, j < n → j < L.length → R (iter n j) ((memo F d L).getD j d)
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, j, hjn, hj => by
    rw [hiter, memo_getD hF hj]
    exact hrel j hj _ _ fun k hk => by
      have := hF.lt j hj k hk
      exact iter_rel_memo hiter hrel hF n k (by omega) (by omega)

end Memo

/-! ## The values as a table

A condition on value `v` that reads another value `u` reads it through `valueT` (`O(log u)` steps in
a `NatTrie`), not through `RealizedProgram.value` (a list lookup of `u` steps): a check over all
values is then near-linear, not quadratic. The per-value functions below are the definitions of
`GordieHowe/Language/RealizedProgram/Valid.lean` on a value (`Value.isCommittedB`, `fieldOfV`, …) or
through the table (`valueFieldT`, `isPublicT`), each with its equation. -/

section ValueTable

variable (ir : RealizedProgram)

/-- **A check of every value, in one pass**, as a statement on `RealizedProgram.value`. -/
theorem allIdx_values_iff (p : ℕ → Value → Bool) :
    allIdx p ir.values 0 = true ↔ ∀ v < ir.values.length, p v (ir.value v) = true := by
  rw [allIdx_iff]
  simp only [Nat.zero_add, value_eq_getD]

theorem isCommitted_eq (v : ℕ) : ir.isCommitted v = (ir.value v).isCommittedB := rfl

/-- Whether a value is pad-realized (`RealizedProgram.isPadRealized`). -/
def _root_.GordieHowe.RealizedProgram.Value.isPadRealizedB (x : Value) : Bool :=
  match x.realization with
  | .pad _ => true
  | .commitment _ => false

theorem isPadRealized_eq (v : ℕ) : ir.isPadRealized v = (ir.value v).isPadRealizedB := rfl

theorem isLateV_iff (v : ℕ) : ir.isLateV (ir.value v) = true ↔ ir.IsLate v := by
  simp [isLateV, IsLate, and_assoc]

theorem valueField_eq (v : ℕ) : ir.valueField v = ir.fieldOfV (ir.value v) := rfl

theorem valueFieldT_eq (v : ℕ) : ir.valueFieldT v = ir.valueField v := by
  rw [valueFieldT, valueT_eq, valueField_eq]

theorem isPublicT_eq (v : ℕ) : ir.isPublicT v = ir.isPublic v := by
  rw [isPublicT, valueT_eq, isPublic, isCommitted_eq, isLateNode]

theorem isBatchNodeT_eq (v : ℕ) : ir.isBatchNodeT v = ir.isBatchNode v := by
  rw [isBatchNodeT, valueT_eq]
  rfl

theorem isQuadCellT_eq (v : ℕ) : ir.isQuadCellT v = ir.isQuadCell v := by
  rw [isQuadCellT, valueT_eq]
  rfl

theorem isQuadraticT_eq (e e' : Expr) : ir.isQuadraticT e e' = ir.isQuadratic e e' := by
  unfold isQuadraticT isQuadratic
  split <;> simp only [isQuadCellT_eq]

theorem fieldOkV_iff (v : ℕ) : ir.fieldOkV (ir.value v) = true ↔ ir.FieldOk v := by
  unfold fieldOkV FieldOk
  cases (ir.value v).field <;> simp [and_assoc]

end ValueTable

/-! ## Lengths through the value table -/

section LenV

variable (ir : RealizedProgram)

theorem colsV_eq : ∀ op : NamedOp, ir.colsV op = NamedOp.cols ir op
  | .batched b op => by rw [colsV, NamedOp.cols, colsV_eq op]
  | .negacyclicConv _ _ | .polyMatVec _ _ _ _ | .polyBroadcast _ _ _ | .ntt _ _ _ | .inverseNtt _ _
  | .nttTranspose _ _ | .rowDot _ _ _ | .macConv _ _ _ _ | .acyclicConv _ _ | .diagonal _ | .scale _
  | .constDiagonal _ | .sum _ | .fromDigits _ _ => by simp [colsV, NamedOp.cols, valueT_eq]

theorem rowsV_eq : ∀ op : NamedOp, ir.rowsV op = NamedOp.rows ir op
  | .batched b op => by rw [rowsV, NamedOp.rows, rowsV_eq op]
  | .negacyclicConv _ _ | .polyMatVec _ _ _ _ | .polyBroadcast _ _ _ | .ntt _ _ _ | .inverseNtt _ _
  | .nttTranspose _ _ | .rowDot _ _ _ | .macConv _ _ _ _ | .acyclicConv _ _ | .diagonal _ | .scale _
  | .constDiagonal _ | .sum _ | .fromDigits _ _ => by simp [rowsV, NamedOp.rows, valueT_eq]

/-- `NamedOp.readLen`, the values through the table. -/
def readLenV : NamedOp → ℕ
  | .negacyclicConv h _ => (ir.valueT h).size
  | .polyMatVec a _ _ _ => (ir.valueT a).size
  | .polyBroadcast t _ _ => (ir.valueT t).size
  | .rowDot _ R W => R * W
  | .macConv r _ _ _ => (ir.valueT r).size
  | .acyclicConv h _ => (ir.valueT h).size
  | .diagonal d => (ir.valueT d).size
  | .scale _ => 1
  | .constDiagonal d => (ir.valueT d).size
  | .batched _ op => readLenV op
  | _ => 0

theorem readLenV_eq : ∀ op : NamedOp, ir.readLenV op = NamedOp.readLen ir op
  | .batched _ op => by rw [readLenV, NamedOp.readLen, readLenV_eq op]
  | .negacyclicConv _ _ | .polyMatVec _ _ _ _ | .polyBroadcast _ _ _ | .ntt _ _ _ | .inverseNtt _ _
  | .nttTranspose _ _ | .rowDot _ _ _ | .macConv _ _ _ _ | .acyclicConv _ _ | .diagonal _ | .scale _
  | .constDiagonal _ | .sum _ | .fromDigits _ _ => by simp [readLenV, NamedOp.readLen, valueT_eq]

mutual

theorem lenV_eq (rl : ℕ → ℕ) : ∀ e : Expr, ir.lenV rl e = Expr.len ir rl e
  | .leaf v => by rw [lenV, Expr.len, valueT_eq]
  | .add e _ | .sub e _ | .scale _ e | .mul e _ | .mux _ e _ => by
    simp only [lenV, Expr.len, lenV_eq rl e]
  | .prod _ e => by simp only [lenV, Expr.len, lenV_eq rl e]
  | .reindex idx _ => by rw [lenV, Expr.len, IndexMap.sizeK_eq]
  | .linear _ _ | .ref _ => rfl
  | .concat e e' => by simp only [lenV, Expr.len, lenV_eq rl e, lenV_eq rl e']
  | .apply op e => by simp only [lenV, Expr.len, lenV_eq rl e, colsV_eq, rowsV_eq]
  | .logic _ _ args => by simp only [lenV, Expr.len, lenListV_eq rl args]

theorem lenListV_eq (rl : ℕ → ℕ) : ∀ es : List Expr, ir.lenListV rl es = Expr.lenList ir rl es
  | [] => rfl
  | e :: es => by simp only [lenListV, Expr.lenList, lenV_eq rl e, lenListV_eq rl es]

end

end LenV

/-! ## Congruence of the expression functions -/

section Congr

variable (ir : RealizedProgram)

mutual

/-- An expression's length depends only on its shared expressions' lengths. -/
theorem Expr.len_congr {rl rl' : ℕ → ℕ} :
    ∀ e : Expr, (∀ k ∈ e.refs, rl k = rl' k) → Expr.len ir rl e = Expr.len ir rl' e
  | .leaf _, _ => rfl
  | .add e _, h | .sub e _, h | .mul e _, h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [Expr.len, Expr.len_congr e fun k hk => h k (.inl hk)]
  | .scale _ e, h | .prod _ e, h | .apply _ e, h => by
    simp only [Expr.refs] at h
    simp only [Expr.len, Expr.len_congr e h]
  | .reindex _ _, _ | .linear _ _, _ => rfl
  | .concat e e', h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [Expr.len, Expr.len_congr e fun k hk => h k (.inl hk),
      Expr.len_congr e' fun k hk => h k (.inr hk)]
  | .mux _ t _, h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [Expr.len, Expr.len_congr t fun k hk => h k (.inl (.inr hk))]
  | .ref k, h => by simp only [Expr.len, h k (by simp [Expr.refs])]
  | .logic _ _ args, h => by
    simp only [Expr.refs] at h
    simp only [Expr.len, Expr.lenList_congr args h]

/-- The lengths of a list of expressions depend only on their shared expressions' lengths. -/
theorem Expr.lenList_congr {rl rl' : ℕ → ℕ} :
    ∀ es : List Expr, (∀ k ∈ Expr.refsList es, rl k = rl' k) →
      Expr.lenList ir rl es = Expr.lenList ir rl' es
  | [], _ => rfl
  | e :: es, h => by
    simp only [Expr.refsList, List.mem_append] at h
    simp only [Expr.lenList, Expr.len_congr e fun k hk => h k (.inl hk),
      Expr.lenList_congr es fun k hk => h k (.inr hk)]

end

end Congr

mutual

/-- An expression's degree depends only on its values' degrees and its shared expressions'. -/
theorem Expr.deg_congr {nd nd' rd rd' : ℕ → ℕ} :
    ∀ e : Expr, (∀ v ∈ e.directNodes, nd v = nd' v) → (∀ k ∈ e.refs, rd k = rd' k) →
      e.deg nd rd = e.deg nd' rd'
  | .leaf v, h, _ => by simp only [Expr.deg, h v (by simp [Expr.directNodes])]
  | .add e e', h, hr | .sub e e', h, hr | .mul e e', h, hr | .concat e e', h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    simp only [Expr.deg, Expr.deg_congr e (fun v hv => h v (.inl hv)) (fun k hk => hr k (.inl hk)),
      Expr.deg_congr e' (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))]
  | .scale c e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    simp only [Expr.deg, Expr.deg_congr e (fun v hv => h v (.inr hv)) hr,
      List.map_congr_left fun v hv => h v (.inl hv)]
  | .reindex _ e, h, hr | .prod _ e, h, hr => by
    simp only [Expr.directNodes, Expr.refs] at h hr
    simp only [Expr.deg, Expr.deg_congr e h hr]
  | .linear rows e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    simp only [Expr.deg, Expr.deg_congr e (fun v hv => h v (.inr hv)) hr]
    congr 2
    refine List.map_congr_left fun v hv => h v (.inl ?_)
    simp only [Expr.rowCoefs, List.mem_flatMap, List.mem_map] at hv ⊢
    obtain ⟨c, ⟨row, hrow, t, ht, rfl⟩, hv⟩ := hv
    exact ⟨row, hrow, t, ht, hv⟩
  | .mux b t e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    simp only [Expr.deg, Expr.deg_congr b (fun v hv => h v (.inl (.inl hv)))
        (fun k hk => hr k (.inl (.inl hk))),
      Expr.deg_congr t (fun v hv => h v (.inl (.inr hv))) (fun k hk => hr k (.inl (.inr hk))),
      Expr.deg_congr e (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))]
  | .apply op e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    simp only [Expr.deg, Expr.deg_congr e (fun v hv => h v (.inr hv)) hr,
      List.map_congr_left fun v hv => h v (.inl (List.mem_append.1 hv))]
  | .ref k, _, hr => by simp only [Expr.deg, hr k (by simp [Expr.refs])]
  | .logic _ _ args, h, hr => by
    simp only [Expr.directNodes, Expr.refs] at h hr
    simp only [Expr.deg, Expr.degList_congr args h hr]

/-- The degrees of a list of expressions depend only on what they read directly. -/
theorem Expr.degList_congr {nd nd' rd rd' : ℕ → ℕ} :
    ∀ es : List Expr, (∀ v ∈ Expr.directNodesList es, nd v = nd' v) →
      (∀ k ∈ Expr.refsList es, rd k = rd' k) → Expr.degList nd rd es = Expr.degList nd' rd' es
  | [], _, _ => rfl
  | e :: es, h, hr => by
    simp only [Expr.directNodesList, Expr.refsList, List.mem_append] at h hr
    simp only [Expr.degList, Expr.deg_congr e (fun v hv => h v (.inl hv)) (fun k hk => hr k (.inl hk)),
      Expr.degList_congr es (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))]

end

/-- An expression's vanishing at zero depends only on its shared expressions'. -/
theorem Expr.zeroAtZero_congr {rz rz' : ℕ → Bool} :
    ∀ e : Expr, (∀ k ∈ e.refs, rz k = rz' k) → e.zeroAtZero rz = e.zeroAtZero rz'
  | .leaf _, _ | .logic _ _ _, _ => rfl
  | .add e e', h | .sub e e', h | .mul e e', h | .concat e e', h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [Expr.zeroAtZero, Expr.zeroAtZero_congr e fun k hk => h k (.inl hk),
      Expr.zeroAtZero_congr e' fun k hk => h k (.inr hk)]
  | .scale _ e, h | .reindex _ e, h | .linear _ e, h | .prod _ e, h | .apply _ e, h => by
    simp only [Expr.refs] at h
    simp only [Expr.zeroAtZero, Expr.zeroAtZero_congr e h]
  | .mux b t e, h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [Expr.zeroAtZero, Expr.zeroAtZero_congr b fun k hk => h k (.inl (.inl hk)),
      Expr.zeroAtZero_congr t fun k hk => h k (.inl (.inr hk)),
      Expr.zeroAtZero_congr e fun k hk => h k (.inr hk)]
  | .ref k, h => by simp only [Expr.zeroAtZero, h k (by simp [Expr.refs])]

namespace IndexMap

theorem boundAux_le_iff (n : ℕ) :
    ∀ (a : ℕ) (m : IndexMap), boundAux a m ≤ n ↔ a ≤ n ∧ ∀ r ∈ m, runBound r ≤ n
  | a, [] => by simp [boundAux]
  | a, r :: rs => by
    rw [boundAux, boundAux_le_iff n _ rs]
    have h : (if Nat.ble a (runBound r) then runBound r else a) ≤ n ↔ a ≤ n ∧ runBound r ≤ n := by
      by_cases hb : Nat.ble a (runBound r) = true
      · rw [if_pos hb]
        have := Nat.le_of_ble_eq_true hb
        constructor
        · intro h'; exact ⟨by omega, h'⟩
        · exact fun h' => h'.2
      · rw [if_neg hb]
        have : ¬ a ≤ runBound r := fun h' => hb (Nat.ble_eq_true_of_le h')
        constructor
        · intro h'; exact ⟨h', by omega⟩
        · exact fun h' => h'.1
    rw [h]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-! ### The walks the kernel evaluates

`inRangeNat` reads its two per-map facts through walks written with the recursors and with
`Nat.beq`, `Nat.ble` and `cond`, which the kernel evaluates on literals in one step each: a
structural `List.all` costs a `brecOn` step per run and `decide` several. `boundK` keeps the
largest bound so far a literal: each step's `Nat.casesOn` on the accumulator makes the kernel
evaluate it, so no chain of pending comparisons builds up (as in `boundAux`, whose accumulator the
kernel evaluates only at the end). Compiled code runs `lowOk` and `bound` (`lowOkK_csimp`,
`boundK_csimp`). -/

theorem runInRange_eq_bound (n : ℕ) (r : ℕ × ℤ × ℕ) :
    runInRange n r = (runLowOk r && decide (runBound r ≤ n)) := by
  obtain ⟨s, d, c⟩ := r
  apply Bool.eq_iff_iff.2
  cases d <;> by_cases hc : c = 0 <;>
    simp only [runInRange, runLowOk, runBound, hc, ite_true, ite_false, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.true_and, true_or, false_or,
      true_and] <;> first | omega | simp

theorem all_runInRange (m : IndexMap) (n : ℕ) :
    m.all (runInRange n) = m.inRangeNat n := by
  rw [Bool.eq_iff_iff]
  simp only [inRangeNat, lowOkK_eq, boundK_eq, bound, Bool.and_eq_true, List.all_eq_true,
    Nat.ble_eq, boundAux_le_iff, runInRange_eq_bound, decide_eq_true_eq, Nat.zero_le, true_and]
  constructor
  · intro h
    exact ⟨fun r hr => (h r hr).1, fun r hr => (h r hr).2⟩
  · rintro ⟨h1, h2⟩ r hr
    exact ⟨h1 r hr, h2 r hr⟩

theorem runInRange_eq (n : ℕ) (r : ℕ × ℤ × ℕ) :
    runInRange n r = (r.2.2 == 0 ||
      (0 ≤ (r.1 : ℤ) + r.2.1 * (r.2.2 - 1 : ℕ) && r.1 < n &&
        (r.1 : ℤ) + r.2.1 * (r.2.2 - 1 : ℕ) < n)) := by
  obtain ⟨s, d, c⟩ := r
  cases d with
  | ofNat d =>
    simp only [runInRange]
    congr 1
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast]
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨⟨by positivity, h1⟩, ?_⟩; exact_mod_cast h2
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, by exact_mod_cast h2⟩
  | negSucc m =>
    simp only [runInRange]
    congr 1
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_eq, Int.negSucc_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨?_, h2⟩, ?_⟩
      · have : ((m + 1) * (c - 1) : ℕ) ≤ s := h1
        have h3 : (((m + 1) * (c - 1) : ℕ) : ℤ) ≤ s := by exact_mod_cast this
        push_cast at h3; nlinarith
      · have : (0 : ℤ) ≤ (m + 1) * ((c - 1 : ℕ) : ℤ) := by positivity
        nlinarith
    · rintro ⟨⟨h1, h2⟩, _⟩
      refine ⟨?_, h2⟩
      have h3 : (((m + 1) * (c - 1) : ℕ) : ℤ) ≤ s := by push_cast; nlinarith
      exact_mod_cast h3

theorem inRangeNat_eq (m : IndexMap) (n : ℕ) : m.inRangeNat n = m.inRange n := by
  rw [← all_runInRange]
  simp only [inRange]
  congr 1
  funext r
  exact runInRange_eq n r

end IndexMap

/-! ## Per-coordinate degrees as runs -/

/-- `IndexMap.entry` is the run function `RunVec.entryOf`. -/
theorem IndexMap.entry_eq_entryOf : ∀ (m : IndexMap) (i : ℕ), m.entry i = RunVec.entryOf m i
  | [], _ => rfl
  | (s, d, c) :: rest, i => by
    simp only [IndexMap.entry, RunVec.entryOf, IndexMap.entry_eq_entryOf rest]

/-- **A coefficient's degree**, the values' degrees read from the runs `nv`. -/
def Coef.degV (nv : ℕ → RunVec) : Coef → ℕ
  | .const _ => 0
  | .node v i => (nv v).get i

/-- **`NamedOp.opDeg`**, the values' degrees read from the runs `nv`. -/
def NamedOp.opDegV (ir : RealizedProgram) (nv : ℕ → RunVec) (op : NamedOp) : ℕ :=
  ((op.operands ++ op.foreignOperands).map fun v => (nv v).maxUpTo (ir.readLenV op)).foldr max 0

/-- **A sparse row's degree**: the largest over its terms of the coefficient's degree plus the
coordinate's. -/
def rowDegV (nv : ℕ → RunVec) (x : RunVec) (row : List (ℕ × Coef)) : ℕ :=
  (row.map fun t => t.2.degV nv + x.get t.1).foldr max 0

section DegV

variable (ir : RealizedProgram)

mutual

/-- **The per-coordinate degrees of an expression, as runs** (`Expr.degAt`), the values' and the
shared expressions' degrees read from the runs `nv` and `rv`, the shared expressions' lengths
from `rl`. -/
def Expr.degV (nv rv : ℕ → RunVec) (rl : ℕ → ℕ) : Expr → RunVec
  | .leaf v => nv v
  | .add e e' => RunVec.zip RunVec.segMax (Expr.degV nv rv rl e) (Expr.degV nv rv rl e')
  | .sub e e' => RunVec.zip RunVec.segMax (Expr.degV nv rv rl e) (Expr.degV nv rv rl e')
  | .scale c e => (Expr.degV nv rv rl e).shift (c.degV nv)
  | .mul e e' => RunVec.zip RunVec.segAdd (Expr.degV nv rv rl e) (Expr.degV nv rv rl e')
  | .reindex idx e => (Expr.degV nv rv rl e).reindex idx
  | .concat e e' => RunVec.concat (ir.lenV rl e) (Expr.degV nv rv rl e) (Expr.degV nv rv rl e')
  | .linear rows e => RunVec.ofList rows (rowDegV nv (Expr.degV nv rv rl e)) 0
  | .prod n e => (Expr.degV nv rv rl e).chunks RunVec.Agg.add n 1 0
  | .mux b t e =>
      RunVec.zip RunVec.segAdd (Expr.degV nv rv rl b)
        (RunVec.zip RunVec.segMax (Expr.degV nv rv rl t) (Expr.degV nv rv rl e))
  | .apply op e => (Expr.degV nv rv rl e).chunks RunVec.Agg.max (ir.colsV op) (ir.rowsV op)
      (op.opDegV ir nv)
  | .ref k => rv k
  | .logic _ w args =>
      (((Expr.degVList nv rv rl args).map fun x => x.chunks RunVec.Agg.max w 1 0).foldr
        (RunVec.zip RunVec.segMax) (RunVec.const 0)).scale (2 * w)

/-- The per-coordinate degrees of a list of expressions, as runs. -/
def Expr.degVList (nv rv : ℕ → RunVec) (rl : ℕ → ℕ) : List Expr → List RunVec
  | [] => []
  | e :: es => Expr.degV nv rv rl e :: Expr.degVList nv rv rl es

end

end DegV

/-! ## The runs are the per-coordinate degrees -/

theorem Coef.degV_eq (nv : ℕ → RunVec) (c : Coef) : c.degV nv = c.degAt fun v => (nv v).get := by
  cases c <;> rfl

theorem NamedOp.opDegV_eq (ir : RealizedProgram) (nv : ℕ → RunVec) (op : NamedOp) :
    op.opDegV ir nv = op.opDeg ir fun v => (nv v).get := by
  simp only [NamedOp.opDegV, NamedOp.opDeg, RunVec.maxUpTo_eq, readLenV_eq]

theorem RunVec.get_foldr_zip_max (l : List RunVec) (i : ℕ) :
    (l.foldr (RunVec.zip RunVec.segMax) (RunVec.const 0)).get i = (l.map (·.get i)).foldr max 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.foldr_cons, RunVec.get_zip, ih, List.map_cons]

section Get

variable {ir} (nv rv : ℕ → RunVec) (rl : ℕ → ℕ)

mutual

/-- **The runs of an expression are its per-coordinate degrees.** -/
theorem Expr.degV_get : ∀ (e : Expr) (i : ℕ),
    (Expr.degV ir nv rv rl e).get i = Expr.degAt ir (fun v => (nv v).get) (fun k => (rv k).get) rl e i
  | .leaf _, _ => rfl
  | .add e e', i | .sub e e', i => by
    simp only [Expr.degV, Expr.degAt, RunVec.get_zip, Expr.degV_get e, Expr.degV_get e']
  | .mul e e', i => by
    simp only [Expr.degV, Expr.degAt, RunVec.get_zip, Expr.degV_get e, Expr.degV_get e']
  | .scale c e, i => by
    simp only [Expr.degV, Expr.degAt, RunVec.get_shift, Expr.degV_get e, Coef.degV_eq]
  | .reindex idx e, i => by
    simp only [Expr.degV, Expr.degAt, RunVec.get_reindex, Expr.degV_get e,
      IndexMap.entry_eq_entryOf]
  | .concat e e', i => by
    simp only [Expr.degV, Expr.degAt, RunVec.get_concat, Expr.degV_get e, Expr.degV_get e',
      lenV_eq]
  | .linear rows e, i => by
    simp only [Expr.degV, Expr.degAt, RunVec.get_ofList _ _ _ [], rowDegV, Expr.degV_get e,
      Coef.degV_eq]
    split_ifs with hi
    · rfl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  | .prod n e, i => by
    simp only [Expr.degV, Expr.degAt, RunVec.get_chunks, RunVec.Agg.add_below, Nat.div_one,
      Expr.degV_get e, Nat.zero_add]
  | .mux b t e, i => by
    simp only [Expr.degV, Expr.degAt, RunVec.get_zip, Expr.degV_get b, Expr.degV_get t,
      Expr.degV_get e]
  | .apply op e, i => by
    simp only [Expr.degV, Expr.degAt, RunVec.get_chunks, RunVec.Agg.max_below, Expr.degV_get e,
      NamedOp.opDegV_eq, colsV_eq, rowsV_eq]
  | .ref _, _ => rfl
  | .logic _ w args, i => by
    simp only [Expr.degV, Expr.degAt, RunVec.get_scale, RunVec.get_foldr_zip_max, List.map_map]
    congr 2
    rw [← Expr.degVList_get args]
    simp only [List.map_map]
    congr 1
    funext x
    simp [RunVec.get_chunks, RunVec.Agg.max_below]

/-- **The runs of a list of expressions are their per-coordinate degrees.** -/
theorem Expr.degVList_get : ∀ es : List Expr,
    (Expr.degVList ir nv rv rl es).map RunVec.get =
      Expr.degAtList ir (fun v => (nv v).get) (fun k => (rv k).get) rl es
  | [] => rfl
  | e :: es => by
    simp only [Expr.degVList, Expr.degAtList, List.map_cons, Expr.degVList_get es]
    congr 1
    funext i
    exact Expr.degV_get e i

end

end Get

/-! ## Congruence -/

section Congr

variable {ir}

theorem Coef.degAt_congr {nd nd' : ℕ → ℕ → ℕ} {c : Coef} (h : ∀ v ∈ c.nodes, nd v = nd' v) :
    c.degAt nd = c.degAt nd' := by
  cases c with
  | const => rfl
  | node v i => simp only [Coef.degAt, h v (by simp [Coef.nodes])]

theorem Coef.degV_congr {nv nv' : ℕ → RunVec} {c : Coef} (h : ∀ v ∈ c.nodes, nv v = nv' v) :
    c.degV nv = c.degV nv' := by
  cases c with
  | const => rfl
  | node v i => simp only [Coef.degV, h v (by simp [Coef.nodes])]

theorem NamedOp.opDeg_congr {nd nd' : ℕ → ℕ → ℕ} {op : NamedOp}
    (h : ∀ v ∈ op.operands ++ op.foreignOperands, nd v = nd' v) :
    op.opDeg ir nd = op.opDeg ir nd' := by
  simp only [NamedOp.opDeg]
  rw [List.map_congr_left fun v hv => by rw [h v hv]]

theorem NamedOp.opDegV_congr {nv nv' : ℕ → RunVec} {op : NamedOp}
    (h : ∀ v ∈ op.operands ++ op.foreignOperands, nv v = nv' v) :
    op.opDegV ir nv = op.opDegV ir nv' := by
  simp only [NamedOp.opDegV]
  rw [List.map_congr_left fun v hv => by rw [h v hv]]

mutual

/-- **An expression's per-coordinate degrees depend only on what it reads directly.** -/
theorem Expr.degAt_congr {nd nd' rd rd' : ℕ → ℕ → ℕ} {rl rl' : ℕ → ℕ} :
    ∀ e : Expr, (∀ v ∈ e.directNodes, nd v = nd' v) → (∀ k ∈ e.refs, rd k = rd' k) →
      (∀ k ∈ e.refs, rl k = rl' k) → Expr.degAt ir nd rd rl e = Expr.degAt ir nd' rd' rl' e
  | .leaf v, h, _, _ => by
    funext i
    simp only [Expr.degAt, h v (by simp [Expr.directNodes])]
  | .add e e', h, hr, hl | .sub e e', h, hr, hl | .mul e e', h, hr, hl => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr hl
    funext i
    simp only [Expr.degAt, Expr.degAt_congr e (fun v hv => h v (.inl hv))
      (fun k hk => hr k (.inl hk)) (fun k hk => hl k (.inl hk)),
      Expr.degAt_congr e' (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))
        (fun k hk => hl k (.inr hk))]
  | .concat e e', h, hr, hl => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr hl
    funext i
    simp only [Expr.degAt, Expr.degAt_congr e (fun v hv => h v (.inl hv))
      (fun k hk => hr k (.inl hk)) (fun k hk => hl k (.inl hk)),
      Expr.degAt_congr e' (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))
        (fun k hk => hl k (.inr hk)), Expr.len_congr ir e fun k hk => hl k (.inl hk)]
  | .scale c e, h, hr, hl => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr hl
    funext i
    simp only [Expr.degAt, Expr.degAt_congr e (fun v hv => h v (.inr hv)) hr hl,
      Coef.degAt_congr fun v hv => h v (.inl hv)]
  | .reindex idx e, h, hr, hl => by
    simp only [Expr.directNodes, Expr.refs] at h hr hl
    funext i
    simp only [Expr.degAt, Expr.degAt_congr e h hr hl]
  | .linear rows e, h, hr, hl => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr hl
    funext i
    simp only [Expr.degAt, Expr.degAt_congr e (fun v hv => h v (.inr hv)) hr hl]
    congr 1
    exact List.map_congr_left fun t ht => by
      rw [Coef.degAt_congr fun v hv => h v (.inl (mem_rowNodes_of_mem_getD ht hv))]
  | .prod n e, h, hr, hl => by
    simp only [Expr.directNodes, Expr.refs] at h hr hl
    funext i
    simp only [Expr.degAt, Expr.degAt_congr e h hr hl]
  | .mux b t e, h, hr, hl => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr hl
    funext i
    simp only [Expr.degAt, Expr.degAt_congr b (fun v hv => h v (.inl (.inl hv)))
      (fun k hk => hr k (.inl (.inl hk))) (fun k hk => hl k (.inl (.inl hk))),
      Expr.degAt_congr t (fun v hv => h v (.inl (.inr hv))) (fun k hk => hr k (.inl (.inr hk)))
        (fun k hk => hl k (.inl (.inr hk))),
      Expr.degAt_congr e (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))
        (fun k hk => hl k (.inr hk))]
  | .apply op e, h, hr, hl => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr hl
    funext i
    simp only [Expr.degAt, Expr.degAt_congr e (fun v hv => h v (.inr hv)) hr hl,
      NamedOp.opDeg_congr fun v hv => h v (.inl (List.mem_append.1 hv))]
  | .ref k, _, hr, _ => by
    funext i
    simp only [Expr.degAt, hr k (by simp [Expr.refs])]
  | .logic _ w args, h, hr, hl => by
    simp only [Expr.directNodes, Expr.refs] at h hr hl
    funext i
    simp only [Expr.degAt, Expr.degAtList_congr args h hr hl]

theorem Expr.degAtList_congr {nd nd' rd rd' : ℕ → ℕ → ℕ} {rl rl' : ℕ → ℕ} :
    ∀ es : List Expr, (∀ v ∈ Expr.directNodesList es, nd v = nd' v) →
      (∀ k ∈ Expr.refsList es, rd k = rd' k) → (∀ k ∈ Expr.refsList es, rl k = rl' k) →
      Expr.degAtList ir nd rd rl es = Expr.degAtList ir nd' rd' rl' es
  | [], _, _, _ => rfl
  | e :: es, h, hr, hl => by
    simp only [Expr.directNodesList, Expr.refsList, List.mem_append] at h hr hl
    simp only [Expr.degAtList, Expr.degAt_congr e (fun v hv => h v (.inl hv))
      (fun k hk => hr k (.inl hk)) (fun k hk => hl k (.inl hk)),
      Expr.degAtList_congr es (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))
        (fun k hk => hl k (.inr hk))]

end

mutual

/-- **An expression's runs depend only on what it reads directly.** -/
theorem Expr.degV_congr {nv nv' rv rv' : ℕ → RunVec} {rl : ℕ → ℕ} :
    ∀ e : Expr, (∀ v ∈ e.directNodes, nv v = nv' v) → (∀ k ∈ e.refs, rv k = rv' k) →
      Expr.degV ir nv rv rl e = Expr.degV ir nv' rv' rl e
  | .leaf v, h, _ => by simp only [Expr.degV, h v (by simp [Expr.directNodes])]
  | .add e e', h, hr | .sub e e', h, hr | .mul e e', h, hr | .concat e e', h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    simp only [Expr.degV, Expr.degV_congr e (fun v hv => h v (.inl hv)) (fun k hk => hr k (.inl hk)),
      Expr.degV_congr e' (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))]
  | .scale c e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    simp only [Expr.degV, Expr.degV_congr e (fun v hv => h v (.inr hv)) hr,
      Coef.degV_congr fun v hv => h v (.inl hv)]
  | .reindex _ e, h, hr | .prod _ e, h, hr => by
    simp only [Expr.directNodes, Expr.refs] at h hr
    simp only [Expr.degV, Expr.degV_congr e h hr]
  | .linear rows e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    simp only [Expr.degV, Expr.degV_congr e (fun v hv => h v (.inr hv)) hr]
    simp only [RunVec.ofList]
    congr 2
    refine List.map_congr_left fun row hrow => ?_
    simp only [rowDegV]
    refine congrArg (fun x => (1, x, 0))
      (congrArg (List.foldr max 0) (List.map_congr_left fun t ht => ?_))
    rw [Coef.degV_congr fun v hv =>
      h v (.inl (List.mem_flatMap.2 ⟨row, hrow, List.mem_flatMap.2 ⟨t, ht, hv⟩⟩))]
  | .mux b t e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    simp only [Expr.degV, Expr.degV_congr b (fun v hv => h v (.inl (.inl hv)))
      (fun k hk => hr k (.inl (.inl hk))),
      Expr.degV_congr t (fun v hv => h v (.inl (.inr hv))) (fun k hk => hr k (.inl (.inr hk))),
      Expr.degV_congr e (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))]
  | .apply op e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    simp only [Expr.degV, Expr.degV_congr e (fun v hv => h v (.inr hv)) hr,
      NamedOp.opDegV_congr fun v hv => h v (.inl (List.mem_append.1 hv))]
  | .ref k, _, hr => by simp only [Expr.degV, hr k (by simp [Expr.refs])]
  | .logic _ w args, h, hr => by
    simp only [Expr.directNodes, Expr.refs] at h hr
    simp only [Expr.degV, Expr.degVList_congr args h hr]

theorem Expr.degVList_congr {nv nv' rv rv' : ℕ → RunVec} {rl : ℕ → ℕ} :
    ∀ es : List Expr, (∀ v ∈ Expr.directNodesList es, nv v = nv' v) →
      (∀ k ∈ Expr.refsList es, rv k = rv' k) →
      Expr.degVList ir nv rv rl es = Expr.degVList ir nv' rv' rl es
  | [], _, _ => rfl
  | e :: es, h, hr => by
    simp only [Expr.directNodesList, Expr.refsList, List.mem_append] at h hr
    simp only [Expr.degVList, Expr.degV_congr e (fun v hv => h v (.inl hv))
      (fun k hk => hr k (.inl hk)),
      Expr.degVList_congr es (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))]

end

end Congr

section

variable (ir : RealizedProgram)

/-! ## Shapes with given lengths -/

mutual

/-- **`exprShapeOk` with the shared expressions' lengths `rl`.** -/
def shapeOkWith (rl : ℕ → ℕ) : Expr → Bool
  | .leaf _ => true
  | .add e e' => shapeOkWith rl e && shapeOkWith rl e' && Expr.len ir rl e == Expr.len ir rl e'
  | .sub e e' => shapeOkWith rl e && shapeOkWith rl e' && Expr.len ir rl e == Expr.len ir rl e'
  | .scale _ e => shapeOkWith rl e
  | .mul e e' => shapeOkWith rl e && shapeOkWith rl e' && Expr.len ir rl e == Expr.len ir rl e'
  | .reindex idx e => shapeOkWith rl e && idx.inRangeNat (Expr.len ir rl e)
  | .concat e e' => shapeOkWith rl e && shapeOkWith rl e'
  | .linear rows e => shapeOkWith rl e && rows.all (·.all (·.1 < Expr.len ir rl e))
  | .prod n e => shapeOkWith rl e && 0 < n && Expr.len ir rl e % n == 0
  | .mux b t e =>
      shapeOkWith rl b && shapeOkWith rl t && shapeOkWith rl e &&
        Expr.len ir rl b == Expr.len ir rl t && Expr.len ir rl t == Expr.len ir rl e
  | .apply op e =>
      shapeOkWith rl e && op.widthsOk ir && Expr.len ir rl e % NamedOp.cols ir op == 0
  | .ref _ => true
  | .logic op w args => shapeOkWithList rl args && logicShapeOk op w (Expr.lenList ir rl args)

/-- `shapeOkWith` on a list of expressions. -/
def shapeOkWithList (rl : ℕ → ℕ) : List Expr → Bool
  | [] => true
  | e :: es => shapeOkWith rl e && shapeOkWithList rl es

end

mutual

theorem shapeOkV_eq (rl : ℕ → ℕ) : ∀ e : Expr, ir.shapeOkV rl e = ir.shapeOkWith rl e
  | .leaf _ | .ref _ => rfl
  | .add e e' | .sub e e' | .mul e e' | .concat e e' => by
    simp only [shapeOkV, shapeOkWith, shapeOkV_eq rl e, shapeOkV_eq rl e', lenV_eq]
  | .scale _ e | .reindex _ e | .linear _ e | .prod _ e => by
    simp only [shapeOkV, shapeOkWith, shapeOkV_eq rl e, lenV_eq]
  | .mux b t e => by
    simp only [shapeOkV, shapeOkWith, shapeOkV_eq rl b, shapeOkV_eq rl t, shapeOkV_eq rl e, lenV_eq]
  | .apply op e => by
    simp only [shapeOkV, shapeOkWith, shapeOkV_eq rl e, lenV_eq, colsV_eq, rowsV_eq,
      NamedOp.widthsOk]
  | .logic op w args => by
    simp only [shapeOkV, shapeOkWith, shapeOkVList_eq rl args, lenListV_eq]

theorem shapeOkVList_eq (rl : ℕ → ℕ) :
    ∀ es : List Expr, ir.shapeOkVList rl es = ir.shapeOkWithList rl es
  | [] => rfl
  | e :: es => by simp only [shapeOkVList, shapeOkWithList, shapeOkV_eq rl e, shapeOkVList_eq rl es]

end

/-- The lengths of a list of expressions (`Expr.lenList`) at the program's depth. -/
theorem map_exprLen_eq :
    ∀ es : List Expr, es.map ir.exprLen = Expr.lenList ir (ir.refLen ir.exprs.length) es
  | [] => rfl
  | e :: es => by simp only [List.map_cons, Expr.lenList, exprLen, map_exprLen_eq es]

mutual

theorem exprShapeOk_eq : ∀ e : Expr, ir.exprShapeOk e = ir.shapeOkWith (ir.refLen ir.exprs.length) e
  | .leaf _ | .ref _ => rfl
  | .add e e' | .sub e e' | .mul e e' | .concat e e' => by
    simp only [exprShapeOk, shapeOkWith, exprLen, exprShapeOk_eq e, exprShapeOk_eq e']
  | .scale _ e | .prod _ e | .apply _ e => by
    simp only [exprShapeOk, shapeOkWith, exprLen, exprShapeOk_eq e]
  | .reindex _ e => by
    simp only [exprShapeOk, shapeOkWith, exprLen, exprShapeOk_eq e, IndexMap.inRangeNat_eq]
  | .linear _ e => by
    simp only [exprShapeOk, shapeOkWith, exprLen, exprShapeOk_eq e]
    rfl
  | .mux b t e => by
    simp only [exprShapeOk, shapeOkWith, exprLen, exprShapeOk_eq b, exprShapeOk_eq t,
      exprShapeOk_eq e]
  | .logic op w args => by
    simp only [exprShapeOk, shapeOkWith, exprShapeOkList_eq args, map_exprLen_eq]

theorem exprShapeOkList_eq :
    ∀ es : List Expr, ir.exprShapeOkList es = ir.shapeOkWithList (ir.refLen ir.exprs.length) es
  | [] => rfl
  | e :: es => by simp only [exprShapeOkList, shapeOkWithList, exprShapeOk_eq e,
      exprShapeOkList_eq es]

end

mutual

theorem shapeOkWith_congr {rl rl' : ℕ → ℕ} :
    ∀ e : Expr, (∀ k ∈ e.refs, rl k = rl' k) → ir.shapeOkWith rl e = ir.shapeOkWith rl' e
  | .leaf _, _ | .ref _, _ => rfl
  | .add e e', h | .sub e e', h | .mul e e', h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [shapeOkWith, shapeOkWith_congr e fun k hk => h k (.inl hk),
      shapeOkWith_congr e' fun k hk => h k (.inr hk), Expr.len_congr ir e fun k hk => h k (.inl hk),
      Expr.len_congr ir e' fun k hk => h k (.inr hk)]
  | .concat e e', h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [shapeOkWith, shapeOkWith_congr e fun k hk => h k (.inl hk),
      shapeOkWith_congr e' fun k hk => h k (.inr hk)]
  | .scale _ e, h => by
    simp only [Expr.refs] at h
    simp only [shapeOkWith, shapeOkWith_congr e h]
  | .reindex _ e, h | .linear _ e, h | .prod _ e, h | .apply _ e, h => by
    simp only [Expr.refs] at h
    simp only [shapeOkWith, shapeOkWith_congr e h, Expr.len_congr ir e h]
  | .mux b t e, h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [shapeOkWith, shapeOkWith_congr b fun k hk => h k (.inl (.inl hk)),
      shapeOkWith_congr t fun k hk => h k (.inl (.inr hk)),
      shapeOkWith_congr e fun k hk => h k (.inr hk),
      Expr.len_congr ir b fun k hk => h k (.inl (.inl hk)),
      Expr.len_congr ir t fun k hk => h k (.inl (.inr hk)),
      Expr.len_congr ir e fun k hk => h k (.inr hk)]
  | .logic _ _ args, h => by
    simp only [Expr.refs] at h
    simp only [shapeOkWith, shapeOkWithList_congr args h, Expr.lenList_congr ir args h]

theorem shapeOkWithList_congr {rl rl' : ℕ → ℕ} :
    ∀ es : List Expr, (∀ k ∈ Expr.refsList es, rl k = rl' k) →
      ir.shapeOkWithList rl es = ir.shapeOkWithList rl' es
  | [], _ => rfl
  | e :: es, h => by
    simp only [Expr.refsList, List.mem_append] at h
    simp only [shapeOkWithList, shapeOkWith_congr e fun k hk => h k (.inl hk),
      shapeOkWithList_congr es fun k hk => h k (.inr hk)]

end

/-! ## The shared expressions' tables -/

/-- **The shared expressions read only entries of smaller index.** -/
def RefsOrdered : Prop := ∀ k < ir.exprs.length, ∀ k' ∈ (ir.expr k).refs, k' < k

theorem refsOrderedB_iff : ir.refsOrderedB = true ↔ ir.RefsOrdered := by
  simp only [refsOrderedB, allIdx_iff, Nat.zero_add, List.all_eq_true, decide_eq_true_eq,
    RefsOrdered, expr_eq_getD]

/-- **The table of the shared expressions' degrees**, the values having degrees `nd`. -/
def degT (nd : ℕ → ℕ) : NatTrie ℕ := memo (fun rd _ e => e.deg nd rd) 0 ir.exprs

/-- **The table of the shared expressions' vanishing at zero.** -/
def zeroT : NatTrie Bool := memo (fun rz _ e => e.zeroAtZero rz) false ir.exprs

/-- An expression's degree, the values having degrees `nd`, through the table. -/
def degM (nd : ℕ → ℕ) (e : Expr) : ℕ := e.deg nd ((ir.degT nd).getD · 0)

/-- An expression's vanishing at zero, through the table. -/
def zeroM (e : Expr) : Bool := e.zeroAtZero (ir.zeroT.getD · false)

/-! ## The values' tables -/

theorem getD_readsL (v : ℕ) : ir.readsL.getD v [] = ir.readsT.getD v [] := getD_memoList v

/-- **The table of the shared expressions' per-coordinate degrees**, the values' degrees read from
the runs `nv`. -/
def refDegVT (nv : ℕ → RunVec) : NatTrie RunVec :=
  memo (fun rv _ e => Expr.degV ir nv rv (ir.lenT.getD · 0) e) default ir.exprs

/-- An expression's per-coordinate degrees, the values' degrees read from `nv`, through the
table. -/
def degVM (nv : ℕ → RunVec) (e : Expr) : RunVec :=
  Expr.degV ir nv ((ir.refDegVT nv).getD · default) (ir.lenT.getD · 0) e

/-- **The step of `valDegT c`**: the per-coordinate degrees of value `v` in challenge `c`, from
those of the values it reads (`r`). -/
def valDegStep (c : ℕ) (r : ℕ → RunVec) (_ : ℕ) (x : Value) : RunVec :=
  match x.kind with
  | .pub (.expr e) => ir.degVM r e
  | .challenge c' => RunVec.const (if c' = c then 1 else 0)
  | _ => RunVec.const 0

/-- **The table of the values' per-coordinate degrees in challenge `c`** (`nodeDegAt`). -/
def valDegT (c : ℕ) : NatTrie RunVec := memo (ir.valDegStep c) default ir.values

/-- The per-coordinate degrees of value `v` in challenge `c`, through the table. -/
def valDegM (c v : ℕ) : RunVec := (ir.valDegT c).getD v default

/-- **A search through a sublist**: `any` over the elements a filter keeps is `any` over the list,
where every element it drops fails. -/
theorem any_filter_eq {α : Type} (L : List α) (p f : α → Bool)
    (h : ∀ x ∈ L, p x = false → f x = false) : (L.filter p).any f = L.any f := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hx : p x = true
    · simp [List.filter_cons, hx, ih']
    · have hf := h x List.mem_cons_self (by simpa using hx)
      simp [List.filter_cons, hx, ih', hf]

/-- **A first match through a sublist**: `findSome?` over the elements a filter keeps is
`findSome?` over the list, where every element it drops gives `none`. -/
theorem findSome?_filter_eq {α β : Type} (L : List α) (p : α → Bool) (f : α → Option β)
    (h : ∀ x ∈ L, p x = false → f x = none) : (L.filter p).findSome? f = L.findSome? f := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hx : p x = true
    · simp only [List.filter_cons, hx, if_true, List.findSome?_cons, ih']
    · have hf := h x List.mem_cons_self (by simpa using hx)
      simp only [List.filter_cons, hx, Bool.false_eq_true, if_false, List.findSome?_cons, hf, ih']

/-! ## The tables are the recursive definitions -/

section Tables

variable {ir}

/-- **The shared expressions' tables are computed in order** when each entry reads only entries
of smaller index. -/
theorem memoDeps_exprs (ho : ir.RefsOrdered) {β : Type} {F : (ℕ → β) → ℕ → Expr → β}
    (hF : ∀ r r' j e, (∀ k ∈ e.refs, r k = r' k) → F r j e = F r' j e) :
    MemoDeps F ir.exprs fun k => (ir.expr k).refs :=
  ⟨ho, fun j _ r r' h => hF r r' j _ (by rw [← expr_eq_getD]; exact h)⟩

theorem closureStep_congr {α : Type} [DecidableEq α] (g : Expr → List α) (r r' : ℕ → List α)
    (j : ℕ) (e : Expr) (h : ∀ k ∈ e.refs, r k = r' k) : closureStep g r j e = closureStep g r' j e := by
  simp only [closureStep, List.flatMap_congr h]

/-- **The closure table holds the closure's elements**: entry `k` has the elements of
`refClosure g n k` at every fuel `n > k`. -/
theorem mem_closureT (ho : ir.RefsOrdered) {α : Type} [DecidableEq α] (g : Expr → List α)
    {n k : ℕ} (hkn : k < n) (hk : k < ir.exprs.length) (x : α) :
    x ∈ ir.refClosure g n k ↔ x ∈ (ir.closureT g).getD k [] :=
  iter_rel_memo (R := fun l l' => ∀ x, x ∈ l ↔ x ∈ l') (iter := ir.refClosure g)
    (G := fun r k => g (ir.expr k) ++ (ir.expr k).refs.flatMap r) (fun _ _ => rfl)
    (fun j _ r r' h x => by
      rw [← expr_eq_getD]
      simp only [closureStep, mem_insertAll, List.mem_append, List.mem_flatMap, List.not_mem_nil,
        false_or]
      exact or_congr Iff.rfl (exists_congr fun k => and_congr_right fun hk => h k hk x))
    (memoDeps_exprs ho (closureStep_congr g)) n k hkn hk x

/-- **The elements of an expression's closure**, through the table. -/
theorem mem_closure_iff (ho : ir.RefsOrdered) {α : Type} [DecidableEq α] (g : Expr → List α)
    {e : Expr} (he : ∀ k ∈ e.refs, k < ir.exprs.length) (x : α) :
    x ∈ ir.closure g e ↔ x ∈ g e ∨ ∃ k ∈ e.refs, x ∈ (ir.closureT g).getD k [] := by
  simp only [closure, List.mem_append, List.mem_flatMap]
  exact or_congr Iff.rfl (exists_congr fun k => and_congr_right fun hk =>
    mem_closureT ho g (he k hk) (he k hk) x)

/-- **`closAll` is the closure's universal statement.** -/
theorem closAll_iff (ho : ir.RefsOrdered) {α : Type} [DecidableEq α] (g : Expr → List α)
    (p : α → Bool) {e : Expr} (he : ∀ k ∈ e.refs, k < ir.exprs.length) :
    ir.closAll g p e = true ↔ ∀ x ∈ ir.closure g e, p x = true := by
  simp only [closAll, Bool.and_eq_true, List.all_eq_true, mem_closure_iff ho g he]
  constructor
  · rintro ⟨h1, h2⟩ x (hx | ⟨k, hk, hx⟩)
    · exact h1 x hx
    · exact h2 k hk x hx
  · intro h
    exact ⟨fun x hx => h x (.inl hx), fun k hk x hx => h x (.inr ⟨k, hk, hx⟩)⟩

/-- **Two tests agreeing on a list's elements test it alike.** -/
theorem all_congr_mem {α : Type} {l : List α} {f f' : α → Bool} (h : ∀ x ∈ l, f x = f' x) :
    l.all f = l.all f' :=
  Bool.eq_iff_iff.2 (by simp only [List.all_eq_true]; exact forall₂_congr fun x hx => by rw [h x hx])

/-- **The flags' table holds the closures' flags**: entry `k` is whether every element of
`refClosure g n k` satisfies `p`, at every fuel `n > k`. -/
theorem closFlagT_getD (ho : ir.RefsOrdered) {α : Type} (g : Expr → List α) (p : α → Bool)
    {n k : ℕ} (hkn : k < n) (hk : k < ir.exprs.length) :
    (ir.refClosure g n k).all p = (ir.closFlagT g p).getD k false :=
  iter_rel_memo (R := Eq) (iter := fun n k => (ir.refClosure g n k).all p)
    (G := fun r k => (g (ir.expr k)).all p && (ir.expr k).refs.all r)
    (fun n j => by simp only [refClosure, List.all_append, List.all_flatMap])
    (fun j _ r r' h => by
      rw [← expr_eq_getD]
      exact congrArg _ (all_congr_mem h))
    (memoDeps_exprs ho fun r r' _ e h => congrArg _ (all_congr_mem h))
    n k hkn hk

/-- **`closFlag` is the closure's test** for an expression whose references are entries. -/
theorem closFlag_eq (ho : ir.RefsOrdered) {α : Type} (g : Expr → List α) (p : α → Bool)
    {e : Expr} (he : ∀ k ∈ e.refs, k < ir.exprs.length) :
    ir.closFlag g p e = (ir.closure g e).all p := by
  rw [closFlag, closure, List.all_append, List.all_flatMap]
  refine congrArg _ (all_congr_mem fun k hk => ?_)
  have h := bitTest_eq (fun _ (b : Bool) => b) (ir.closFlagL g p) k
  change bitTest (ir.closFlagBits g p) (ir.closFlagL g p).length false k = _ at h
  rw [h, show (default : Bool) = false from rfl, closFlagL, getD_memoList, ← closFlagT,
    closFlagT_getD ho g p (he k hk) (he k hk)]

/-- **The values an expression reads**, through the table. -/
theorem mem_nodesOf (ho : ir.RefsOrdered) {e : Expr} (he : ∀ k ∈ e.refs, k < ir.exprs.length)
    (v : ℕ) : v ∈ ir.nodesOf e ↔ v ∈ ir.exprNodes e := by
  rw [exprNodes, mem_closure_iff ho _ he]
  simp only [nodesOf, List.mem_append, List.mem_flatMap]

/-- **The length table holds the lengths** (`refLen`) at every fuel above the entry. -/
theorem lenT_getD (ho : ir.RefsOrdered) {n k : ℕ} (hkn : k < n) (hk : k < ir.exprs.length) :
    ir.refLen n k = ir.lenT.getD k 0 :=
  iter_rel_memo (R := Eq) (G := fun r k => Expr.len ir r (ir.expr k)) (fun _ _ => rfl)
    (fun _ _ _ _ h => by rw [← expr_eq_getD, lenV_eq]; exact Expr.len_congr ir _ h)
    (memoDeps_exprs ho fun _ _ _ e h => by rw [lenV_eq, lenV_eq]; exact Expr.len_congr ir e h)
    n k hkn hk

/-- **An expression's length**, through the table. -/
theorem lenOf_eq (ho : ir.RefsOrdered) {e : Expr} (he : ∀ k ∈ e.refs, k < ir.exprs.length) :
    ir.lenOf e = ir.exprLen e := by
  rw [lenOf, lenV_eq]
  exact Expr.len_congr ir e fun k hk => (lenT_getD ho (he k hk) (he k hk)).symm

/-- **An expression's shape**, through the table. -/
theorem shapeOkWith_lenT (ho : ir.RefsOrdered) {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) :
    ir.shapeOkWith (ir.lenT.getD · 0) e = ir.exprShapeOk e := by
  rw [exprShapeOk_eq]
  exact shapeOkWith_congr ir e fun k hk => (lenT_getD ho (he k hk) (he k hk)).symm

/-- **The degree table holds the degrees** (`refDeg`) at every fuel above the entry. -/
theorem degT_getD (ho : ir.RefsOrdered) (nd : ℕ → ℕ) {n k : ℕ} (hkn : k < n)
    (hk : k < ir.exprs.length) : ir.refDeg nd n k = (ir.degT nd).getD k 0 :=
  iter_rel_memo (R := Eq) (G := fun r k => (ir.expr k).deg nd r) (fun _ _ => rfl)
    (fun _ _ _ _ h => by rw [← expr_eq_getD]; exact Expr.deg_congr _ (fun _ _ => rfl) h)
    (memoDeps_exprs ho fun _ _ _ e h => Expr.deg_congr e (fun _ _ => rfl) h) n k hkn hk

/-- **An expression's degree**, through the table. -/
theorem degM_eq (ho : ir.RefsOrdered) (nd : ℕ → ℕ) {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) : ir.degM nd e = ir.degOf nd e :=
  Expr.deg_congr e (fun _ _ => rfl) fun k hk => (degT_getD ho nd (he k hk) (he k hk)).symm

/-- **The vanishing table holds the vanishing** (`refZero`) at every fuel above the entry. -/
theorem zeroT_getD (ho : ir.RefsOrdered) {n k : ℕ} (hkn : k < n) (hk : k < ir.exprs.length) :
    ir.refZero n k = ir.zeroT.getD k false :=
  iter_rel_memo (R := Eq) (G := fun r k => (ir.expr k).zeroAtZero r) (fun _ _ => rfl)
    (fun _ _ _ _ h => by rw [← expr_eq_getD]; exact Expr.zeroAtZero_congr _ h)
    (memoDeps_exprs ho fun _ _ _ e h => Expr.zeroAtZero_congr e h) n k hkn hk

/-- **An expression's vanishing at zero**, through the table. -/
theorem zeroM_eq (ho : ir.RefsOrdered) {e : Expr} (he : ∀ k ∈ e.refs, k < ir.exprs.length) :
    ir.zeroM e = ir.zeroOf e :=
  Expr.zeroAtZero_congr e fun k hk => (zeroT_getD ho (he k hk) (he k hk)).symm

end Tables

/-- **The step of `nodeReads`.** -/
def nodeReadsStep (r : ℕ → List Read) (v : ℕ) : List Read :=
  match (ir.value v).kind with
  | .pub (.expr e) => (ir.exprNodes e).flatMap r
  | .pub (.opaque _ args) => args.flatMap r
  | .challenge c => [.chal c]
  | .late => [.late v]
  | .bits w _ => r w
  | .message u => [.late u]
  | _ => []

/-- **The shared expressions' runs with `n` levels**, the recursion the table computes. -/
def refDegVIter (nv : ℕ → RunVec) : ℕ → ℕ → RunVec
  | 0, _ => default
  | n + 1, k => Expr.degV ir nv (refDegVIter nv n) (ir.lenT.getD · 0) (ir.expr k)

/-- **The step of `nodeDegAt c`.** -/
def nodeDegAtStep (c : ℕ) (r : ℕ → ℕ → ℕ) (v : ℕ) : ℕ → ℕ :=
  match (ir.value v).kind with
  | .pub (.expr e) => ir.degAtOf r e
  | .challenge c' => fun _ => if c' = c then 1 else 0
  | _ => fun _ => 0

section ValueTables

variable {ir}

/-- **Well-formed shared expressions read only earlier entries.** -/
theorem WellFormed.refsOrdered (hwf : ir.WellFormed) : ir.RefsOrdered :=
  fun k hk => (hwf.exprs k hk).1

/-- **A well-formed value reads only values of smaller identifier.** -/
theorem WellFormed.valueDeps_lt (hwf : ir.WellFormed) {v : ℕ} (hv : v < ir.values.length) :
    ∀ u ∈ ir.valueDeps v, u < v := by
  have h := (hwf.values v hv).2
  unfold valueDeps
  rcases hk : (ir.value v).kind with _ | ⟨_ | ⟨_, args⟩ | e⟩ | _ | _ | _ | ⟨w, sel⟩ | _ | _ <;>
    rw [hk] at h <;> simp only [KindOk, PubDefOk] at h <;> simp
  · exact h
  · exact h.2
  · exact h.1

/-- **A well-formed public expression's shared expressions exist.** -/
theorem WellFormed.pubExpr_refs (hwf : ir.WellFormed) {v : ℕ} (hv : v < ir.values.length)
    {e : Expr} (hk : (ir.value v).kind = .pub (.expr e)) : ∀ k ∈ e.refs, k < ir.exprs.length := by
  have h := (hwf.values v hv).2
  rw [hk] at h
  exact h.1.refs

theorem nodeReads_succ (n v : ℕ) : ir.nodeReads (n + 1) v = ir.nodeReadsStep (ir.nodeReads n) v :=
  rfl

/-- A private value reads no challenges or late values, at any fuel. -/
theorem nodeReads_of_priv {v : ℕ} (hk : (ir.value v).kind = .priv) :
    ∀ n, ir.nodeReads n v = []
  | 0 => rfl
  | n + 1 => by rw [nodeReads_succ, nodeReadsStep, hk]

/-- An opaque public value with no arguments reads no challenges or late values. -/
theorem nodeReads_of_opaque_nil {v : ℕ} {name : String}
    (hk : (ir.value v).kind = .pub (.opaque name [])) :
    ∀ n, ir.nodeReads n v = []
  | 0 => rfl
  | n + 1 => by rw [nodeReads_succ, nodeReadsStep, hk]; rfl

/-- A constant reads no challenges or late values, at any fuel. -/
theorem nodeReads_of_constant {v : ℕ} {es : List ℕ} (hk : (ir.value v).kind = .constant es) :
    ∀ n, ir.nodeReads n v = []
  | 0 => rfl
  | n + 1 => by rw [nodeReads_succ, nodeReadsStep, hk]

/-- The values a shared expression without shared references reads are its direct values. -/
theorem exprNodes_ref_of_refs_nil {k : ℕ} {e : Expr} (hk : k < ir.exprs.length)
    (he : ir.expr k = e) (hr : e.refs = []) : ir.exprNodes (.ref k) = e.directNodes := by
  obtain ⟨n, hn⟩ : ∃ n, ir.exprs.length = n + 1 := ⟨ir.exprs.length - 1, by omega⟩
  simp only [exprNodes, closure, hn, Expr.refs, List.flatMap_cons, List.flatMap_nil,
    Expr.directNodes, refClosure, he, hr, List.nil_append, List.append_nil]

theorem value_eq_default {v : ℕ} (hv : ir.values.length ≤ v) : ir.value v = default := by
  rw [value_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none hv]
  rfl

/-- A value bound to its digits reads no challenges or late values, at any fuel. -/
theorem nodeReads_of_bound {v : ℕ} {e : Expr} (hk : (ir.value v).kind = .bound e) :
    ∀ n, ir.nodeReads n v = []
  | 0 => rfl
  | n + 1 => by rw [nodeReads_succ, nodeReadsStep, hk]

/-- A bit view of a private value reads no challenges or late values, at any fuel. -/
theorem nodeReads_of_bits_priv {v w : ℕ} {sel : IndexMap} (hk : (ir.value v).kind = .bits w sel)
    (hw : (ir.value w).kind = .priv) : ∀ n, ir.nodeReads n v = []
  | 0 => rfl
  | n + 1 => by rw [nodeReads_succ, nodeReadsStep, hk]; exact nodeReads_of_priv hw n

theorem nodeReads_of_le {v : ℕ} (hv : ir.values.length ≤ v) : ∀ n, ir.nodeReads n v = []
  | 0 => rfl
  | n + 1 => by rw [nodeReads_succ, nodeReadsStep, value_eq_default hv]; rfl

theorem readsStep_congr (hwf : ir.WellFormed) :
    MemoDeps ir.readsStep ir.values ir.valueDeps := by
  refine ⟨fun v hv => hwf.valueDeps_lt hv, fun v hv r r' h => ?_⟩
  rw [← value_eq_getD]
  unfold valueDeps at h
  unfold readsStep
  rcases hk : (ir.value v).kind with _ | ⟨_ | ⟨_, args⟩ | e⟩ | _ | _ | _ | ⟨w, sel⟩ | _ | _ <;>
    (rw [hk] at h; try simp only)
  · rw [List.flatMap_congr h]
  · have he := hwf.pubExpr_refs hv hk
    rw [List.flatMap_congr fun u hu => h u ((mem_nodesOf hwf.refsOrdered he u).1 hu)]
  · exact h w (List.mem_singleton_self _)

/-- **The reads table holds what each value reads** (`nodeReads` at the program's fuel). -/
theorem mem_readsT (hwf : ir.WellFormed) (v : ℕ) (x : Read) :
    x ∈ ir.nodeReads ir.fuel v ↔ x ∈ ir.readsT.getD v [] := by
  by_cases hv : v < ir.values.length
  · refine iter_rel_memo (R := fun l l' => ∀ x, x ∈ l ↔ x ∈ l') nodeReads_succ
      (fun v hv r r' h x => ?_) (readsStep_congr hwf) ir.fuel v (by simp [fuel]; omega) hv x
    rw [← value_eq_getD]
    change x ∈ ir.nodeReadsStep r v ↔ x ∈ ir.readsStep r' v (ir.value v)
    unfold valueDeps at h
    unfold nodeReadsStep readsStep
    rcases hk : (ir.value v).kind with _ | ⟨_ | ⟨_, args⟩ | e⟩ | _ | _ | _ | ⟨w, sel⟩ | _ | _ <;>
      rw [hk] at h <;> simp only [mem_insertAll, List.not_mem_nil, false_or, List.mem_flatMap]
    · exact exists_congr fun u => and_congr_right fun hu => h u hu x
    · have he := hwf.pubExpr_refs hv hk
      simp only [mem_nodesOf hwf.refsOrdered he]
      exact exists_congr fun u => and_congr_right fun hu => h u hu x
    · exact h w (List.mem_singleton_self _) x
  · rw [nodeReads_of_le (by omega), readsT, memo_getD_of_le (by omega)]

theorem nodeDegAt_succ (c n v : ℕ) :
    ir.nodeDegAt c (n + 1) v = ir.nodeDegAtStep c (ir.nodeDegAt c n) v := by
  funext i
  simp only [nodeDegAt, nodeDegAtStep]
  rcases (ir.value v).kind with _ | ⟨_ | _ | _⟩ | _ | _ | _ | _ | _ | _ | _ <;> rfl

/-- **The runs table is the recursion** at every fuel above the entry. -/
theorem refDegVT_getD (ho : ir.RefsOrdered) (nv : ℕ → RunVec) {n k : ℕ} (hkn : k < n)
    (hk : k < ir.exprs.length) : ir.refDegVIter nv n k = (ir.refDegVT nv).getD k default := by
  unfold refDegVT
  exact iter_rel_memo (R := Eq) (G := fun r k => Expr.degV ir nv r (ir.lenT.getD · 0) (ir.expr k))
    (F := fun rv _ e => Expr.degV ir nv rv (ir.lenT.getD · 0) e)
    (fun _ _ => rfl)
    (fun _ _ _ _ h => by rw [← expr_eq_getD]; exact Expr.degV_congr _ (fun _ _ => rfl) h)
    (memoDeps_exprs (F := fun rv _ e => Expr.degV ir nv rv (ir.lenT.getD · 0) e) ho
      fun _ _ _ e h => Expr.degV_congr e (fun _ _ => rfl) h) n k hkn hk

/-- **The recursion depends only on the values the shared expression reads.** -/
theorem refDegVIter_congr {nv nv' : ℕ → RunVec} :
    ∀ n k, (∀ v ∈ ir.refClosure Expr.directNodes n k, nv v = nv' v) →
      ir.refDegVIter nv n k = ir.refDegVIter nv' n k
  | 0, _, _ => rfl
  | n + 1, k, h =>
    Expr.degV_congr _ (fun v hv => h v (List.mem_append_left _ hv)) fun k' hk' =>
      refDegVIter_congr n k' fun v hv => h v (refClosure_mono_ref hk' hv)

/-- **An expression's runs through the table depend only on the values it reads.** -/
theorem degVM_congr (ho : ir.RefsOrdered) {nv nv' : ℕ → RunVec} {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) (h : ∀ v ∈ ir.exprNodes e, nv v = nv' v) :
    ir.degVM nv e = ir.degVM nv' e := by
  unfold degVM
  refine Expr.degV_congr e (fun v hv => h v (List.mem_append_left _ hv)) fun k hk => ?_
  rw [← refDegVT_getD ho nv (he k hk) (he k hk), ← refDegVT_getD ho nv' (he k hk) (he k hk)]
  exact refDegVIter_congr _ k fun v hv =>
    h v (List.mem_append_right _ (List.mem_flatMap.2 ⟨k, hk, hv⟩))

/-- **The runs table holds the per-coordinate degrees** (`refDegAt`) at every fuel above the
entry. -/
theorem refDegVT_get (ho : ir.RefsOrdered) (nv : ℕ → RunVec) {n k : ℕ} (hkn : k < n)
    (hk : k < ir.exprs.length) (i : ℕ) :
    ((ir.refDegVT nv).getD k default).get i = ir.refDegAt (fun v => (nv v).get) n k i := by
  unfold refDegVT
  refine iter_rel_memo (R := fun g x => ∀ i, x.get i = g i) (iter := ir.refDegAt fun v => (nv v).get)
    (G := fun r k i => Expr.degAt ir (fun v => (nv v).get) r (ir.refLen ir.exprs.length)
      (ir.expr k) i) (F := fun rv _ e => Expr.degV ir nv rv (ir.lenT.getD · 0) e)
    (fun _ _ => rfl) (fun j hj r r' h i => ?_)
    (memoDeps_exprs (F := fun rv _ e => Expr.degV ir nv rv (ir.lenT.getD · 0) e) ho
      fun _ _ _ e h => Expr.degV_congr e (fun _ _ => rfl) h) n k hkn hk i
  rw [← expr_eq_getD]
  change (Expr.degV ir nv r' (ir.lenT.getD · 0) (ir.expr j)).get i = _
  rw [Expr.degV_get]
  exact congrFun (Expr.degAt_congr _ (fun _ _ => rfl) (fun k hk => funext (h k hk))
    fun k hk => (lenT_getD ho (by have := ho j hj k hk; omega) (by have := ho j hj k hk; omega)).symm) i

/-- **An expression's runs through the table are its per-coordinate degrees.** -/
theorem degVM_get (ho : ir.RefsOrdered) (nv : ℕ → RunVec) {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) (i : ℕ) :
    (ir.degVM nv e).get i = ir.degAtOf (fun v => (nv v).get) e i := by
  unfold degVM degAtOf
  rw [Expr.degV_get]
  exact congrFun (Expr.degAt_congr e (fun _ _ => rfl)
    (fun k hk => funext fun i => refDegVT_get ho nv (he k hk) (he k hk) i)
    fun k hk => (lenT_getD ho (he k hk) (he k hk)).symm) i

/-- **A shared expression's per-coordinate degrees depend only on those of the values it
reads.** -/
theorem refDegAt_congr {nd nd' : ℕ → ℕ → ℕ} :
    ∀ n k, (∀ v ∈ ir.refClosure Expr.directNodes n k, nd v = nd' v) →
      ir.refDegAt nd n k = ir.refDegAt nd' n k
  | 0, _, _ => rfl
  | n + 1, k, h => by
    funext i
    simp only [refDegAt]
    exact congrFun (Expr.degAt_congr _ (fun v hv => h v (List.mem_append_left _ hv))
      (fun k' hk' => refDegAt_congr n k' fun v hv => h v (refClosure_mono_ref hk' hv))
      fun _ _ => rfl) i

/-- **An expression's per-coordinate degrees depend only on those of the values it reads.** -/
theorem degAtOf_congr {nd nd' : ℕ → ℕ → ℕ} {e : Expr} (h : ∀ v ∈ ir.exprNodes e, nd v = nd' v) :
    ir.degAtOf nd e = ir.degAtOf nd' e := by
  funext i
  exact congrFun (Expr.degAt_congr e (fun v hv => h v (List.mem_append_left _ hv))
    (fun k hk => refDegAt_congr _ k fun v hv =>
      h v (List.mem_append_right _ (List.mem_flatMap.2 ⟨k, hk, hv⟩)))
    fun _ _ => rfl) i

theorem valDegStep_congr (hwf : ir.WellFormed) (c : ℕ) :
    MemoDeps (ir.valDegStep c) ir.values ir.valueDeps := by
  refine ⟨fun v hv => hwf.valueDeps_lt hv, fun v hv r r' h => ?_⟩
  rw [← value_eq_getD]
  unfold valueDeps at h
  unfold valDegStep
  rcases hk : (ir.value v).kind with _ | ⟨_ | ⟨_, args⟩ | e⟩ | _ | _ | _ | ⟨w, sel⟩ | _ | _ <;>
    (rw [hk] at h; try simp only)
  exact degVM_congr hwf.refsOrdered (hwf.pubExpr_refs hv hk) h

/-- **The value runs table holds the per-coordinate degrees** (`nodeDegAt c` at the program's
fuel). -/
theorem valDegM_get (hwf : ir.WellFormed) (c : ℕ) {v : ℕ} (hv : v < ir.values.length) (i : ℕ) :
    (ir.valDegM c v).get i = ir.nodeDegAt c ir.fuel v i := by
  refine iter_rel_memo (R := fun g x => ∀ i, x.get i = g i) (nodeDegAt_succ c)
    (fun v hv r r' h i => ?_) (valDegStep_congr hwf c) ir.fuel v (by simp [fuel]; omega) hv i
  rw [← value_eq_getD]
  change (ir.valDegStep c r' v (ir.value v)).get i = ir.nodeDegAtStep c r v i
  unfold valueDeps at h
  unfold valDegStep nodeDegAtStep
  rcases hk : (ir.value v).kind with _ | ⟨_ | ⟨_, args⟩ | e⟩ | _ | _ | _ | ⟨w, sel⟩ | _ | _ <;>
    (rw [hk] at h; try simp only [RunVec.get_const])
  rw [degVM_get hwf.refsOrdered _ (hwf.pubExpr_refs hv hk)]
  exact congrFun (degAtOf_congr fun u hu => funext (h u hu)) i

end ValueTables

/-! ## The checkers -/

/-- **`LensOk b`**, through the table. -/
def lensOkB : PredBody → Bool
  | .equal _ e e' _ => ir.lenOf e == ir.lenOf e'
  | .mem _ _ _ _ => true
  | .mod _ _ e e' _ => ir.lenOf e == ir.lenOf e'
  | .cross _ x _ y _ _ => ir.lenOf x == ir.lenOf y

/-- **`PredOk b`**, through the tables. -/
def predOkB (b : PredBody) : Bool :=
  b.exprs.all (fun de => de.1 < ir.domains.length && ir.exprOkB (ir.domainField de.1) de.2) &&
    ir.lensOkB b

/-- **`WellFormed`**, in one pass over each table. -/
def wellFormedB : Bool :=
  ir.refsOrderedB &&
    decide (∀ d ∈ ir.domains, d.field < ir.fields.length) &&
    allIdx (fun v x => x.domain < ir.domains.length && ir.kindOkB v x.kind) ir.values 0 &&
    allIdx (fun _ e => ir.shapeOkV (ir.lenT.getD · 0) e) ir.exprs 0 &&
    ir.predicates.all (fun p => ir.predOkB p.body) &&
    decide (∀ c ∈ ir.challenges, ir.ChallengeOk c) &&
    allIdx (fun _ x => ir.fieldOkV x) ir.values 0

/-- **`ReadsSound`**, through the tables. -/
def readsB : Bool :=
  ir.predicates.all fun p =>
    (ir.predNodesM p.body).all fun v => (ir.readsT.getD v []).all fun rd => p.reads.contains rd

/-- **`exprDeg c b`**, through the tables. -/
def exprDegM (c : ℕ) (b : PredBody) : ℕ :=
  (b.exprs.map fun de => (ir.degVM (ir.valDegM c) de.2).maxUpTo (ir.lenOf de.2)).foldr max 0

/-- Whether a kind is a public expression. -/
def _root_.GordieHowe.RealizedProgram.Kind.isPubExpr : Kind → Bool
  | .pub (.expr _) => true
  | _ => false

/-- **`DegreesSound`**, through the tables. -/
def degreesB : Bool :=
  ir.predicates.all (fun p =>
      (List.range ir.challenges.length).all fun c => ir.exprDegM c p.body ≤ p.deg c) &&
    allIdx (fun v x => !x.kind.isPubExpr ||
      (List.range ir.challenges.length).all fun c =>
        (ir.valDegM c v).maxUpTo x.size ≤ (x.degree.lookup c).getD 0) ir.values 0

/-- **`DegreesSound` at challenge `c`**: the predicates' and the public expressions' degrees in
`c`, so that the challenges are checked one at a time (`degreesB_iff_at`, `degrees_of_at`). -/
def degreesAtB (c : ℕ) : Bool :=
  ir.predicates.all (fun p => ir.exprDegM c p.body ≤ p.deg c) &&
    allIdx (fun v x => !x.kind.isPubExpr ||
      (ir.valDegM c v).maxUpTo x.size ≤ (x.degree.lookup c).getD 0) ir.values 0

theorem cellNdT_eq : ir.cellNdT = ir.cellNd := by
  funext v
  rw [cellNdT, cellNd, valueT_eq, isCommitted_eq, isLateNode]

theorem inPartsB_iff {b : ℕ} (hb : b < ir.batches.length) (pid : ℕ) :
    ir.inPartsB b pid = true ↔ pid ∈ (ir.batch b).parts := by
  rw [inPartsB, batchPartsT, toTrie_getD (by simpa using hb), List.getD_eq_getElem?_getD,
    List.getElem?_map, batch, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]
  exact natSet_isSome _ pid

theorem isCircuitInputT_iff (C : Circuit) (v : ℕ) (k : Kind) :
    isCircuitInputT (circuitSets C) v k = true ↔ IsCircuitInputOf C.inputs v k := by
  cases k <;> simp only [isCircuitInputT, IsCircuitInputOf, circuitSets, any_isCommittedOf_iff,
    any_isPubOf_iff, any_isPadOf_iff, any_isViewOf_iff, Bool.and_eq_true]

/-- **`BatchAdmits pid d b e e'`**, through the tables. -/
def batchAdmitsB (pid d b : ℕ) (e e' : Expr) : Bool :=
  let B := ir.batch b
  let p := (ir.field (ir.domainField d)).characteristic
  decide (b < ir.batches.length ∧ B.domain = d) && ir.inPartsB b pid &&
    ir.closAll Expr.directNodes ir.isBatchNodeT e &&
    ir.closAll Expr.directNodes ir.isBatchNodeT e' &&
    decide (1 ≤ B.degree) && decide (ir.degM ir.cellNdT e ≤ B.degree) &&
    decide (ir.degM ir.cellNdT e' ≤ B.degree) && ir.zeroM e && ir.zeroM e' &&
    decide (B.skipDomain = skipDomainName p ∧ SkipFits B.degree B.width p) &&
    decide (ir.lenOf e ≤ B.operands.lane * B.instances) &&
    decide (B.operands.lane * B.instances ≤ 2 ^ B.rounds * B.width)

/-- **`GkrAdmits pid d c e e'`**, through the tables. -/
def gkrAdmitsB (pid d c : ℕ) (e e' : Expr) : Bool :=
  decide (c < ir.circuits.length ∧ (ir.circuit c).domain = d) &&
    natMem (ir.circuitT.getD c default).preds pid &&
    ir.closAll Expr.directNodes
      (fun v => isCircuitInputT (ir.circuitT.getD c default) v (ir.valueT v).kind) e &&
    ir.closAll Expr.directNodes
      (fun v => isCircuitInputT (ir.circuitT.getD c default) v (ir.valueT v).kind) e'

/-- **`TargetAdmits pid d e e' t`**, through the tables. -/
def targetAdmitsB (pid d : ℕ) (e e' : Expr) : Target → Bool
  | .affine => decide (ir.degM ir.cellNdT e ≤ 1) && decide (ir.degM ir.cellNdT e' ≤ 1)
  | .quadratic => ir.isQuadraticT e e'
  | .batch b => ir.batchAdmitsB pid d b e e'
  | .gkr c => ir.gkrAdmitsB pid d c e e'
  | .realized q => decide (ir.RealizedAdmits d e e' q)

/-- **`BodyAdmitted pid b`**, through the tables. -/
def bodyAdmittedB (pid : ℕ) : PredBody → Bool
  | .equal d e e' t => ir.targetAdmitsB pid d e e' t
  | .mem _ _ _ _ => true
  | .mod d q e e' real =>
    (q != 0 || real.target.isSome) &&
      match real.target with
      | some t => ir.targetAdmitsB pid d e e' t
      | none => true
  | .cross _ _ _ _ _ _ => true

/-- **`TargetsAdmit`**, in one pass over the predicates and the circuits. -/
def targetsB : Bool :=
  allIdx (fun pid p => ir.bodyAdmittedB pid p.body) ir.predicates 0 &&
    allIdx (fun c C => C.predicates.all fun pid =>
      decide (pid < ir.predicates.length ∧
        PredBody.target (ir.predT.getD pid default).body = some (.gkr c))) ir.circuits 0 &&
    decide (∀ c ∈ ir.circuits, CircuitLaidOut c)

/-! ## The checkers are the validity items -/

section Checkers

variable {ir}

theorem refs_all_iff {e : Expr} :
    e.refs.all (· < ir.exprs.length) = true ↔ ∀ k ∈ e.refs, k < ir.exprs.length := by
  simp

theorem exprOkB_iff (ho : ir.RefsOrdered) (f : ℕ) (e : Expr) :
    ir.exprOkB f e = true ↔ ir.ExprOk f e := by
  rw [exprOk_iff]
  by_cases he : ∀ k ∈ e.refs, k < ir.exprs.length
  · simp only [exprOkB, refs_all_iff.2 he, Bool.true_and, Bool.and_eq_true, closAll_iff ho _ _ he,
      shapeOkV_eq, shapeOkWith_lenT ho he, decide_eq_true_eq, beq_iff_eq, exprNodes, valueFieldT_eq,
      isPublicT_eq]
    tauto
  · simp only [exprOkB, Bool.and_eq_true, refs_all_iff]
    tauto

theorem kindOkB_iff (ho : ir.RefsOrdered) (v : ℕ) (k : Kind) :
    ir.kindOkB v k = true ↔ ir.KindOk v k := by
  rcases k with _ | ⟨_ | _ | e⟩ | _ | c | _ | ⟨w, sel⟩ | ⟨u, _⟩ | u | e <;>
    simp only [kindOkB, decide_eq_true_eq]
  case pub.expr =>
    simp only [KindOk, PubDefOk, Bool.and_eq_true, exprOkB_iff ho, valueFieldT_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun u hu => by simpa using (closAll_iff ho _ _ h1.refs).1 h2 u hu⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (closAll_iff ho _ _ h1.refs).2 fun u hu => by simpa using h2 u hu⟩
  case challenge => simp only [KindOk, Bool.and_eq_true, decide_eq_true_eq, valueFieldT_eq]
  case bits =>
    simp only [KindOk, Bool.and_eq_true, decide_eq_true_eq, valueT_eq, IndexMap.inRangeNat_eq,
      and_assoc]
  case padCopy => simp only [KindOk, valueT_eq, isLateNode]
  case message =>
    simp only [KindOk, Bool.and_eq_true, decide_eq_true_eq, valueT_eq, valueFieldT_eq, isLateNode,
      and_assoc]
  case bound =>
    simp only [KindOk, Bool.and_eq_true, exprOkB_iff ho, valueFieldT_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun u hu => by simpa using (closAll_iff ho _ _ h1.refs).1 h2 u hu⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (closAll_iff ho _ _ h1.refs).2 fun u hu => by simpa using h2 u hu⟩

/-- The shared expressions of a predicate body's expressions exist. -/
def BodyRefsOk (b : PredBody) : Prop := ∀ de ∈ b.exprs, ∀ k ∈ de.2.refs, k < ir.exprs.length

theorem lensOkB_iff (ho : ir.RefsOrdered) {b : PredBody} (hb : ir.BodyRefsOk b) :
    ir.lensOkB b = true ↔ ir.LensOk b := by
  cases b <;> simp only [lensOkB, LensOk, beq_iff_eq]
  · rename_i d e e' t
    rw [lenOf_eq ho (hb (d, e) (by simp [PredBody.exprs])),
      lenOf_eq ho (hb (d, e') (by simp [PredBody.exprs]))]
  · rename_i d q e e' real
    rw [lenOf_eq ho (hb (d, e) (by simp [PredBody.exprs])),
      lenOf_eq ho (hb (d, e') (by simp [PredBody.exprs]))]
  · rename_i dx x dy y k real
    rw [lenOf_eq ho (hb (dx, x) (by simp [PredBody.exprs])),
      lenOf_eq ho (hb (dy, y) (by simp [PredBody.exprs]))]

theorem PredOk.bodyRefsOk {b : PredBody} (h : ir.PredOk b) : ir.BodyRefsOk b :=
  fun de hde => (h.1 de hde).2.refs

theorem predOkB_iff (ho : ir.RefsOrdered) (b : PredBody) : ir.predOkB b = true ↔ ir.PredOk b := by
  simp only [predOkB, PredOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, exprOkB_iff ho]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (lensOkB_iff ho fun de hde => (h1 de hde).2.refs).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (lensOkB_iff ho fun de hde => (h1 de hde).2.refs).2 h2⟩

theorem exprsShape_iff (ho : ir.RefsOrdered) :
    allIdx (fun _ e => ir.shapeOkV (ir.lenT.getD · 0) e) ir.exprs 0 = true ↔
      ∀ k < ir.exprs.length, ir.exprShapeOk (ir.expr k) = true := by
  rw [allIdx_iff]
  refine forall₂_congr fun k hk => ?_
  rw [shapeOkV_eq, ← shapeOkWith_lenT ho fun k' hk' => by have := ho k hk k' hk'; omega,
    expr_eq_getD]

/-- **`wellFormedB` with the member checks is `WellFormed`.** The member checks are decided at the
structure records' pointers (`RealizedProgram.checksOk_of_memberValuesB`), not here. -/
theorem wellFormedB_iff :
    ir.wellFormedB = true ∧ (∀ m ∈ ir.statement.checks, ir.CheckOk m) ↔ ir.WellFormed := by
  rw [wellFormed_iff]
  by_cases ho : ir.RefsOrdered
  · simp only [wellFormedB, (refsOrderedB_iff ir).2 ho, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq, allIdx_iff, Nat.zero_add, exprsShape_iff ho, List.all_eq_true,
      predOkB_iff ho]
    have hv : ∀ v < ir.values.length, ((ir.values.getD v default).domain < ir.domains.length ∧
        ir.kindOkB v (ir.values.getD v default).kind = true) ↔ ir.ValueOk v := fun v _ => by
      rw [← value_eq_getD, kindOkB_iff ho]
      rfl
    have hf : ∀ v, ir.fieldOkV (ir.values.getD v default) = true ↔ ir.FieldOk v :=
      fun v => by rw [← value_eq_getD]; exact ir.fieldOkV_iff v
    simp only [ExprsOk, hf]
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h7⟩, h6⟩
      exact ⟨h1, fun v hv' => (hv v hv').1 (h2 v hv'), fun k hk => ⟨ho k hk, h3 k hk⟩, h4, h5, h6,
        h7⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
      exact ⟨⟨⟨⟨⟨⟨h1, fun v hv' => (hv v hv').2 (h2 v hv')⟩, fun k hk => (h3 k hk).2⟩, h4⟩, h5⟩,
        h7⟩, h6⟩
  · have hb : ir.refsOrderedB = false :=
      Bool.eq_false_iff.2 fun h => ho ((refsOrderedB_iff ir).1 h)
    simp only [wellFormedB, hb, Bool.false_and, Bool.false_eq_true, false_and, false_iff]
    exact fun h => ho fun k hk => (h.2.2.1 k hk).1

instance : Decidable ir.WellFormed := decidable_of_iff _ ir.wellFormedB_iff

theorem WellFormed.bodyRefsOk (hwf : ir.WellFormed) {p : Predicate} (hp : p ∈ ir.predicates) :
    ir.BodyRefsOk p.body :=
  (hwf.predicates p hp).bodyRefsOk

theorem mem_predNodesM (ho : ir.RefsOrdered) {b : PredBody} (hb : ir.BodyRefsOk b) (v : ℕ) :
    v ∈ ir.predNodesM b ↔ v ∈ ir.predNodes b := by
  simp only [predNodesM, predNodes, List.mem_append, List.mem_flatMap]
  exact or_congr (exists_congr fun de => and_congr_right fun hde => mem_nodesOf ho (hb de hde) v)
    Iff.rfl

/-- **`readsB` is `ReadsSound`** for a well-formed program. -/
theorem readsB_iff (hwf : ir.WellFormed) : ir.readsB = true ↔ ir.ReadsSound := by
  simp only [readsB, ReadsSound, List.all_eq_true, List.contains_iff_mem, predReads,
    List.mem_flatMap]
  refine forall₂_congr fun p hp => ?_
  constructor
  · rintro h rd ⟨v, hv, hrd⟩
    exact h v ((mem_predNodesM hwf.refsOrdered (hwf.bodyRefsOk hp) v).2 hv) rd
      ((mem_readsT hwf v rd).1 hrd)
  · intro h v hv rd hrd
    exact h rd ⟨v, (mem_predNodesM hwf.refsOrdered (hwf.bodyRefsOk hp) v).1 hv,
      (mem_readsT hwf v rd).2 hrd⟩

theorem exprDegM_eq (hwf : ir.WellFormed) {p : Predicate} (hp : p ∈ ir.predicates) (c : ℕ) :
    ir.exprDegM c p.body = ir.exprDeg c p.body := by
  simp only [exprDegM, exprDeg]
  congr 1
  refine List.map_congr_left fun de hde => ?_
  have he := ((hwf.predicates p hp).1 de hde).2
  rw [RunVec.maxUpTo_eq, lenOf_eq hwf.refsOrdered he.refs]
  refine maxBelow_congr fun i _ => ?_
  rw [degVM_get hwf.refsOrdered _ he.refs]
  exact congrFun (degAtOf_congr fun v hv => funext (valDegM_get hwf c (he.range v hv))) i

theorem isPubExpr_eq (v : ℕ) : ir.isPubExpr v = (ir.value v).kind.isPubExpr := by
  unfold isPubExpr
  rcases (ir.value v).kind with _ | ⟨_ | _ | _⟩ | _ | _ | _ | _ | _ | _ <;> rfl

/-- **`degreesB` is `DegreesSound`** for a well-formed program. -/
theorem degreesB_iff (hwf : ir.WellFormed) : ir.degreesB = true ↔ ir.DegreesSound := by
  constructor
  · intro h
    simp only [degreesB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
      allIdx_iff, Nat.zero_add, Bool.or_eq_true, Bool.not_eq_true'] at h
    refine ⟨fun p hp c hc => ?_, fun v hv hpub c hc => ?_⟩
    · rw [← exprDegM_eq hwf hp]
      exact h.1 p hp c hc
    · rcases h.2 v hv with h' | h'
      · rw [isPubExpr_eq] at hpub
        exact absurd hpub (by simpa [value_eq_getD] using h')
      · have := h' c hc
        rw [RunVec.maxUpTo_eq] at this
        rw [show maxBelow (ir.value v).size (ir.nodeDegAt c ir.fuel v) =
          maxBelow (ir.value v).size (ir.valDegM c v).get from
            maxBelow_congr fun i _ => (valDegM_get hwf c hv i).symm]
        simpa [value_eq_getD] using this
  · intro h
    simp only [degreesB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
      allIdx_iff, Nat.zero_add, Bool.or_eq_true, Bool.not_eq_true']
    refine ⟨fun p hp c hc => ?_, fun v hv => ?_⟩
    · rw [exprDegM_eq hwf hp]
      exact h.predicates p hp c hc
    · by_cases hpub : ir.isPubExpr v = true
      · refine .inr fun c hc => ?_
        rw [RunVec.maxUpTo_eq]
        have := h.values v hv hpub c hc
        rw [show maxBelow (ir.value v).size (ir.nodeDegAt c ir.fuel v) =
          maxBelow (ir.value v).size (ir.valDegM c v).get from
            maxBelow_congr fun i _ => (valDegM_get hwf c hv i).symm] at this
        simpa [value_eq_getD] using this
      · refine .inl ?_
        rw [isPubExpr_eq] at hpub
        simpa [value_eq_getD] using hpub

/-- **`degreesB` is `degreesAtB` at every challenge.** -/
theorem degreesB_iff_at :
    ir.degreesB = true ↔ ∀ c < ir.challenges.length, ir.degreesAtB c = true := by
  simp only [degreesB, degreesAtB, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, allIdx_iff, Nat.zero_add, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩ c hc
    refine ⟨fun p hp => h1 p hp c hc, fun v hv => ?_⟩
    rcases h2 v hv with h | h
    · exact .inl h
    · exact .inr (h c hc)
  · intro h
    refine ⟨fun p hp c hc => (h c hc).1 p hp, fun v hv => ?_⟩
    by_cases hk : (ir.values.getD v default).kind.isPubExpr = false
    · exact .inl hk
    · exact .inr fun c hc => ((h c hc).2 v hv).resolve_left hk

/-- **A property below `0`.** -/
theorem forall_lt_zero (P : ℕ → Prop) : ∀ c < 0, P c := fun c hc => absurd hc (Nat.not_lt_zero c)

/-- **A property below `n + 1`**, from the property below `n` and at `n`: a proof module states
the property at each `n` as a literal, so the kernel compares it syntactically. -/
theorem forall_lt_succ_of {P : ℕ → Prop} {n : ℕ} (h : ∀ c < n, P c) (hn : P n) :
    ∀ c < n + 1, P c := fun c hc => by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
  · exact h c hc
  · exact hn

/-- **The exported degrees are sound** from their check at each of the `n` challenges. -/
theorem degrees_of_at (hwf : ir.WellFormed) {n : ℕ} (hn : ir.challenges.length = n)
    (h : ∀ c < n, ir.degreesAtB c = true) : ir.DegreesSound :=
  (degreesB_iff hwf).1 ((degreesB_iff_at).2 fun c hc => h c (hn ▸ hc))

theorem predicate_mem {pid : ℕ} (h : pid < ir.predicates.length) :
    ir.predicate pid ∈ ir.predicates := by
  rw [predicate_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem cellDeg_eq (e : Expr) : ir.cellDeg e = ir.degOf ir.cellNd e := rfl

theorem closAll_append_iff (ho : ir.RefsOrdered) (p : ℕ → Bool) {e e' : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) (he' : ∀ k ∈ e'.refs, k < ir.exprs.length) :
    (ir.closAll Expr.directNodes p e = true ∧ ir.closAll Expr.directNodes p e' = true) ↔
      ∀ v ∈ ir.exprNodes e ++ ir.exprNodes e', p v = true := by
  rw [closAll_iff ho _ _ he, closAll_iff ho _ _ he']
  simp only [List.mem_append, exprNodes]
  constructor
  · rintro ⟨h1, h2⟩ v (hv | hv)
    · exact h1 v hv
    · exact h2 v hv
  · intro h
    exact ⟨fun v hv => h v (.inl hv), fun v hv => h v (.inr hv)⟩

theorem targetAdmitsB_iff (ho : ir.RefsOrdered) (pid d : ℕ) {e e' : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) (he' : ∀ k ∈ e'.refs, k < ir.exprs.length)
    (t : Target) : ir.targetAdmitsB pid d e e' t = true ↔ ir.TargetAdmits pid d e e' t := by
  cases t with
  | realized q => simp only [targetAdmitsB, TargetAdmits, decide_eq_true_eq]
  | affine =>
    simp only [targetAdmitsB, TargetAdmits, Bool.and_eq_true, decide_eq_true_eq, cellDeg_eq,
      cellNdT_eq, degM_eq ho _ he, degM_eq ho _ he']
  | quadratic => simp only [targetAdmitsB, TargetAdmits, isQuadraticT_eq]
  | batch b =>
    have hn : ∀ v, ir.isBatchNodeT v = ir.isBatchNode v := ir.isBatchNodeT_eq
    simp only [targetAdmitsB, batchAdmitsB, TargetAdmits, BatchAdmits, Bool.and_eq_true,
      decide_eq_true_eq, cellNdT_eq, degM_eq ho _ he, degM_eq ho _ he', zeroM_eq ho he,
      zeroM_eq ho he', lenOf_eq ho he, show ir.isBatchNodeT = ir.isBatchNode from funext hn,
      ← closAll_append_iff ho _ he he', cellDeg_eq]
    by_cases hb : b < ir.batches.length
    · rw [ir.inPartsB_iff hb pid]
      tauto
    · simp [hb]
  | gkr c =>
    by_cases hc : c < ir.circuits.length
    · have h := closAll_append_iff ho
        (fun v => decide (IsCircuitInputOf (ir.circuit c).inputs v (ir.value v).kind)) he he'
      simp only [decide_eq_true_eq] at h
      have hi : (fun v => isCircuitInputT (ir.circuitT.getD c default) v (ir.valueT v).kind) =
          fun v => decide (IsCircuitInputOf (ir.circuit c).inputs v (ir.value v).kind) := by
        funext v
        rw [ir.circuitT_getD hc, valueT_eq, Bool.eq_iff_iff, isCircuitInputT_iff, decide_eq_true_iff]
      have hp : natMem (ir.circuitT.getD c default).preds pid = true ↔
          pid ∈ (ir.circuit c).predicates := by
        rw [ir.circuitT_getD hc, natMem, circuitSets, natSet_isSome]
      simp only [targetAdmitsB, gkrAdmitsB, TargetAdmits, GkrAdmits, Bool.and_eq_true,
        decide_eq_true_eq, hi, hp, ← h]
      tauto
    · simp [targetAdmitsB, gkrAdmitsB, TargetAdmits, GkrAdmits, hc]

theorem bodyAdmittedB_iff (ho : ir.RefsOrdered) (pid : ℕ) {b : PredBody} (hb : ir.BodyRefsOk b) :
    ir.bodyAdmittedB pid b = true ↔ ir.BodyAdmitted pid b := by
  cases b with
  | equal d e e' t =>
    simp only [BodyRefsOk, PredBody.exprs, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true] at hb
    exact targetAdmitsB_iff ho pid d hb.1 hb.2 t
  | mem => simp [bodyAdmittedB, BodyAdmitted]
  | mod d q e e' real =>
    have hb1 := hb (d, e) (by simp [PredBody.exprs])
    have hb2 := hb (d, e') (by simp [PredBody.exprs])
    simp only [bodyAdmittedB, BodyAdmitted, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
    refine and_congr (by tauto) ?_
    cases real.target with
    | none => simp [OptTargetAdmits]
    | some t => exact targetAdmitsB_iff ho pid d hb1 hb2 t
  | cross => simp [bodyAdmittedB, BodyAdmitted]

/-- **`targetsB` is `TargetsAdmit`** for a well-formed program. -/
theorem targetsB_iff (hwf : ir.WellFormed) : ir.targetsB = true ↔ ir.TargetsAdmit := by
  rw [targetsAdmit_iff]
  simp only [targetsB, Bool.and_eq_true, allIdx_iff, Nat.zero_add, List.all_eq_true,
    decide_eq_true_eq]
  rw [and_assoc]
  refine and_congr (forall₂_congr fun pid hpid => ?_)
    (and_congr (forall₂_congr fun c _ => forall₂_congr fun pid _ => ?_) Iff.rfl)
  · rw [← predicate_eq_getD]
    exact bodyAdmittedB_iff hwf.refsOrdered pid (hwf.bodyRefsOk (predicate_mem hpid))
  · constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [predT, toTrie_getD h1, ← predicate_eq_getD] at h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [predT, toTrie_getD h1, ← predicate_eq_getD]⟩

end Checkers

end

end GordieHowe.RealizedProgram
