-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Lemmas
public import GordieHowe.Language.RealizedProgram.NatTrie

@[expose] public section

/-!
# GordieHowe: the checker of the plan's program

Boolean checks of the items of `GordieHowe.RealizedProgram.ValidAtNodes`, written for kernel reduction and run by
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
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Lists -/

/-- **A predicate holds at every position of a list**, the positions counted from `i`. -/
def allIdx {α : Type} (p : ℕ → α → Bool) : List α → ℕ → Bool
  | [], _ => true
  | x :: xs, i => p i x && allIdx p xs (i + 1)

theorem allIdx_iff {α : Type} [Inhabited α] (p : ℕ → α → Bool) :
    ∀ (l : List α) (i : ℕ), allIdx p l i = true ↔ ∀ j < l.length, p (i + j) (l.getD j default) = true
  | [], i => by simp [allIdx]
  | x :: xs, i => by
    rw [allIdx, Bool.and_eq_true, allIdx_iff p xs (i + 1)]
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

/-- **The elements of `l` added to `acc`**, each once (`List.insert`). -/
def insertAll {α : Type} [DecidableEq α] : List α → List α → List α
  | acc, [] => acc
  | acc, x :: xs => insertAll (acc.insert x) xs

theorem mem_insertAll {α : Type} [DecidableEq α] {x : α} :
    ∀ (acc l : List α), x ∈ insertAll acc l ↔ x ∈ acc ∨ x ∈ l
  | acc, [] => by simp [insertAll]
  | acc, y :: ys => by
    rw [insertAll, mem_insertAll, List.mem_insert_iff, List.mem_cons]
    tauto

/-! ## Tables computed in order -/

/-- **A table of a list's entries, each computed from the earlier ones**: entry `j` (the list's
element `x`) is `F r j x`, `r` reading the entries already set (`d` when unset). -/
def memoAux {γ β : Type} (F : (ℕ → β) → ℕ → γ → β) (d : β) :
    List γ → ℕ → NatTrie β → NatTrie β
  | [], _, t => t
  | x :: xs, j, t => memoAux F d xs (j + 1) (t.set j (F (t.getD · d) j x))

/-- **The table of a list's entries** (`memoAux` from the empty table). -/
def memo {γ β : Type} (F : (ℕ → β) → ℕ → γ → β) (d : β) (L : List γ) : NatTrie β :=
  memoAux F d L 0 .nil

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
  memoAux_inv hF L 0 .nil (by simp) (fun _ h => absurd h (Nat.not_lt_zero _)) j hj

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
  simp only [NatTrie.getD, memo,
    memoAux_get?_of_le L 0 .nil (fun _ _ => NatTrie.get?_nil _) j (by simpa using hj),
    Option.getD_none]

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

/-- **A list as a `NatTrie`** (`memo` of the elements). -/
def toTrie {γ : Type} [Inhabited γ] (L : List γ) : NatTrie γ := memo (fun _ _ x => x) default L

theorem toTrie_getD {γ : Type} [Inhabited γ] {L : List γ} {j : ℕ} (hj : j < L.length) :
    (toTrie L).getD j default = L.getD j default :=
  memo_getD (D := fun _ => []) ⟨fun _ _ _ h => absurd h List.not_mem_nil,
    fun _ _ _ _ _ => rfl⟩ hj

/-- **A list as a `NatTrie` reads as the list at every index**, past its end too. -/
theorem toTrie_getD_eq {γ : Type} [Inhabited γ] (L : List γ) (j : ℕ) :
    (toTrie L).getD j default = L.getD j default := by
  by_cases hj : j < L.length
  · exact toTrie_getD hj
  · rw [toTrie, memo_getD_of_le (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega), Option.getD_none]

/-! ## The values as a table

A condition on value `v` that reads another value `u` reads it through `valueT` (`O(log u)` steps in
a `NatTrie`), not through `RealizedProgram.value` (a list lookup of `u` steps): a check over all
values is then near-linear, not quadratic. The per-value functions below are the definitions of
`GordieHowe/Language/RealizedProgram/Valid.lean` on a value (`Value.isCommittedB`, `fieldOfV`, …) or
through the table (`valueFieldT`, `isPublicT`), each with its equation. -/

/-- **The keys set by a fold of `NatTrie.set`** are the list's and the initial table's. -/
theorem foldl_set_isSome {α : Type} (key : α → ℕ) :
    ∀ (L : List α) (t : NatTrie Unit) (v : ℕ),
      ((L.foldl (fun t m => t.set (key m) ()) t).get? v).isSome = true ↔
        v ∈ L.map key ∨ (t.get? v).isSome = true
  | [], t, v => by simp
  | m :: L, t, v => by
    rw [List.foldl_cons, foldl_set_isSome key L _ v, NatTrie.get?_set]
    by_cases h : v = key m <;> simp [h]

/-- **A list of naturals as a set**: a `NatTrie` with a key at each element. -/
def natSet (L : List ℕ) : NatTrie Unit := L.foldl (fun t m => t.set m ()) .nil

theorem natSet_isSome (L : List ℕ) (v : ℕ) : ((natSet L).get? v).isSome = true ↔ v ∈ L := by
  have h := foldl_set_isSome id L .nil v
  simp only [NatTrie.get?_nil, Option.isSome_none, Bool.false_eq_true, or_false, List.map_id] at h
  exact h

section ValueTable

variable (ir : RealizedProgram)

/-- **The values as a `NatTrie`.** -/
def valT : NatTrie Value := toTrie ir.values

/-- **Value `v`, through the table.** -/
def valueT (v : ℕ) : Value := ir.valT.getD v default

theorem valueT_eq (v : ℕ) : ir.valueT v = ir.value v := toTrie_getD_eq ir.values v

/-- **A check of every value, in one pass**, as a statement on `RealizedProgram.value`. -/
theorem allIdx_values_iff (p : ℕ → Value → Bool) :
    allIdx p ir.values 0 = true ↔ ∀ v < ir.values.length, p v (ir.value v) = true := by
  rw [allIdx_iff]
  simp only [Nat.zero_add]
  rfl

/-- Whether a value is committed in phase `0` (`RealizedProgram.isCommitted`). -/
def _root_.GordieHowe.RealizedProgram.Value.isCommittedB (x : Value) : Bool :=
  match x.kind with
  | .priv => true
  | .bits _ _ => true
  | .padCopy _ _ => true
  | .bound _ => true
  | _ => false

theorem isCommitted_eq (v : ℕ) : ir.isCommitted v = (ir.value v).isCommittedB := rfl

/-- Whether a value is pad-realized (`RealizedProgram.isPadRealized`). -/
def _root_.GordieHowe.RealizedProgram.Value.isPadRealizedB (x : Value) : Bool :=
  match x.realization with
  | .pad _ => true
  | .commitment _ => false

theorem isPadRealized_eq (v : ℕ) : ir.isPadRealized v = (ir.value v).isPadRealizedB := rfl

/-- **A value is a late value node of a phase of the program** (`RealizedProgram.IsLate`). -/
def isLateV (x : Value) : Bool := x.kind.isLate && decide (1 ≤ x.phase) && decide (x.phase ≤ ir.phases)

theorem isLateV_iff (v : ℕ) : ir.isLateV (ir.value v) = true ↔ ir.IsLate v := by
  simp [isLateV, IsLate, and_assoc]

/-- The field of a value (`RealizedProgram.valueField`). -/
def fieldOfV (x : Value) : ℕ :=
  match x.kind.allowsField, x.field with
  | true, some f => f
  | _, _ => ir.domainField x.domain

theorem valueField_eq (v : ℕ) : ir.valueField v = ir.fieldOfV (ir.value v) := rfl

/-- The field of value `v`, through the table. -/
def valueFieldT (v : ℕ) : ℕ := ir.fieldOfV (ir.valueT v)

theorem valueFieldT_eq (v : ℕ) : ir.valueFieldT v = ir.valueField v := by
  rw [valueFieldT, valueT_eq, valueField_eq]

/-- Whether value `v` is public (`RealizedProgram.isPublic`), through the table. -/
def isPublicT (v : ℕ) : Bool := !(ir.valueT v).isCommittedB && !(ir.valueT v).kind.isLate

theorem isPublicT_eq (v : ℕ) : ir.isPublicT v = ir.isPublic v := by
  rw [isPublicT, valueT_eq, isPublic, isCommitted_eq, isLateNode]

/-- Whether value `v` is an operand a batch may read (`RealizedProgram.isBatchNode`), through the
table. -/
def isBatchNodeT (v : ℕ) : Bool :=
  match (ir.valueT v).kind with
  | .priv => (ir.valueT v).phase == 0
  | .bits _ _ => true
  | .padCopy _ _ => true
  | .constant _ => true
  | .pub .input => true
  | .pub (.opaque _ _) => true
  | _ => false

theorem isBatchNodeT_eq (v : ℕ) : ir.isBatchNodeT v = ir.isBatchNode v := by
  rw [isBatchNodeT, valueT_eq]
  rfl

/-- Whether value `v` is a cell of the quadratic test (`RealizedProgram.isQuadCell`), through the
table. -/
def isQuadCellT (v : ℕ) : Bool :=
  match (ir.valueT v).kind with
  | .priv => (ir.valueT v).phase == 0 && (ir.valueT v).type == .field
  | _ => false

theorem isQuadCellT_eq (v : ℕ) : ir.isQuadCellT v = ir.isQuadCell v := by
  rw [isQuadCellT, valueT_eq]
  rfl

/-- **The quadratic form** (`RealizedProgram.isQuadratic`), through the table. -/
def isQuadraticT : Expr → Expr → Bool
  | .mul (.leaf a) (.leaf b), .leaf c => ir.isQuadCellT a && ir.isQuadCellT b && ir.isQuadCellT c
  | _, _ => false

theorem isQuadraticT_eq (e e' : Expr) : ir.isQuadraticT e e' = ir.isQuadratic e e' := by
  unfold isQuadraticT isQuadratic
  split <;> simp only [isQuadCellT_eq]

/-- **A value's field is well formed** (`RealizedProgram.FieldOk`), on the value. -/
def fieldOkV (x : Value) : Bool :=
  match x.field with
  | none => true
  | some f => decide (f < ir.fields.length) && x.kind.allowsField && decide (x.type = .field)

theorem fieldOkV_iff (v : ℕ) : ir.fieldOkV (ir.value v) = true ↔ ir.FieldOk v := by
  unfold fieldOkV FieldOk
  cases (ir.value v).field <;> simp [and_assoc]

end ValueTable

/-! ## Lengths through the value table -/

section LenV

variable (ir : RealizedProgram)

/-- `NamedOp.cols`, the values through the table. -/
def colsV : NamedOp → ℕ
  | .negacyclicConv h _ => (ir.valueT h).size
  | .polyMatVec a K L _ => L * ((ir.valueT a).size / (K * L))
  | .polyBroadcast t K _ => (ir.valueT t).size / K
  | .ntt n _ _ => n
  | .inverseNtt n _ => n
  | .nttTranspose n _ => n
  | .rowDot _ _ W => W
  | .macConv _ w nch _ => nch * w
  | .acyclicConv _ lx => lx
  | .diagonal d => (ir.valueT d).size
  | .scale _ => 1
  | .constDiagonal d => (ir.valueT d).size
  | .sum w => w
  | .fromDigits k _ => k
  | .batched b op => b * colsV op

/-- `NamedOp.rows`, the values through the table. -/
def rowsV : NamedOp → ℕ
  | .negacyclicConv h _ => (ir.valueT h).size
  | .polyMatVec a K L _ => K * ((ir.valueT a).size / (K * L))
  | .polyBroadcast t _ _ => (ir.valueT t).size
  | .ntt n _ _ => n
  | .inverseNtt n _ => n
  | .nttTranspose n _ => n
  | .rowDot _ R _ => R
  | .macConv _ w _ _ => w
  | .acyclicConv h lx => lx + (ir.valueT h).size - 1
  | .diagonal d => (ir.valueT d).size
  | .scale _ => 1
  | .constDiagonal d => (ir.valueT d).size
  | .sum _ => 1
  | .fromDigits _ _ => 1
  | .batched b op => b * rowsV op

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

/-- **`Expr.len`, the values through the table.** -/
def lenV (rl : ℕ → ℕ) : Expr → ℕ
  | .leaf v => (ir.valueT v).size
  | .add e _ => lenV rl e
  | .sub e _ => lenV rl e
  | .scale _ e => lenV rl e
  | .mul e _ => lenV rl e
  | .reindex idx _ => idx.size
  | .concat e e' => lenV rl e + lenV rl e'
  | .linear rows _ => rows.length
  | .prod n e => lenV rl e / n
  | .mux _ t _ => lenV rl t
  | .apply op e => lenV rl e / ir.colsV op * ir.rowsV op
  | .ref k => rl k
  | .logic _ w args => (lenListV rl args).headD 0 / w

/-- `Expr.lenList`, the values through the table. -/
def lenListV (rl : ℕ → ℕ) : List Expr → List ℕ
  | [] => []
  | e :: es => lenV rl e :: lenListV rl es

end

mutual

theorem lenV_eq (rl : ℕ → ℕ) : ∀ e : Expr, ir.lenV rl e = Expr.len ir rl e
  | .leaf v => by rw [lenV, Expr.len, valueT_eq]
  | .add e _ | .sub e _ | .scale _ e | .mul e _ | .mux _ e _ => by
    simp only [lenV, Expr.len, lenV_eq rl e]
  | .prod _ e => by simp only [lenV, Expr.len, lenV_eq rl e]
  | .reindex _ _ | .linear _ _ | .ref _ => rfl
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

/-- **A run's entries are naturals below `n`**, in natural arithmetic: for a step `-(m + 1)` the
last entry `s − (m + 1)(c − 1)` is at least `0` and below the first. -/
def runInRange (n : ℕ) : ℕ × ℤ × ℕ → Bool
  | (s, .ofNat d, c) => c == 0 || (decide (s < n) && decide (s + d * (c - 1) < n))
  | (s, .negSucc m, c) => c == 0 || (decide ((m + 1) * (c - 1) ≤ s) && decide (s < n))

/-- **A run's last entry is a natural**: for a step `-(m + 1)`, `(m + 1)(c − 1) ≤ s`. -/
def runLowOk : ℕ × ℤ × ℕ → Bool
  | (_, .ofNat _, _) => true
  | (s, .negSucc m, c) => c == 0 || decide ((m + 1) * (c - 1) ≤ s)

/-- **One more than a run's largest entry** (`0` for an empty run). -/
def runBound : ℕ × ℤ × ℕ → ℕ
  | (s, .ofNat d, c) => if c = 0 then 0 else s + d * (c - 1) + 1
  | (s, .negSucc _, c) => if c = 0 then 0 else s + 1

/-- **The larger of `a` and the bound of the runs `m`**, by a left fold of `Nat.ble` tests: the
kernel evaluates a `foldr max` over a long list far slower (an index map of 32 832 runs: over 150 s
against about 20 s). -/
def boundAux : ℕ → IndexMap → ℕ
  | a, [] => a
  | a, r :: rs => boundAux (if Nat.ble a (runBound r) then runBound r else a) rs

/-- **One more than an index map's largest entry.** -/
def bound (m : IndexMap) : ℕ := boundAux 0 m

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

/-- **`IndexMap.inRange`, in natural arithmetic** (`inRangeNat_eq`), the bound `n` read once: the
per-map facts (`runLowOk` on every run and `bound`) do not depend on `n`, so the kernel computes
them once per index map, and each use compares one number. -/
def inRangeNat (m : IndexMap) (n : ℕ) : Bool := m.all runLowOk && decide (m.bound ≤ n)

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
  simp only [inRangeNat, bound, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    boundAux_le_iff, runInRange_eq_bound, Nat.zero_le, true_and]
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

/-- **`shapeOkWith`, the lengths through the value table** (`lenV`, `shapeOkV_eq`). -/
def shapeOkV (rl : ℕ → ℕ) : Expr → Bool
  | .leaf _ => true
  | .add e e' => shapeOkV rl e && shapeOkV rl e' && ir.lenV rl e == ir.lenV rl e'
  | .sub e e' => shapeOkV rl e && shapeOkV rl e' && ir.lenV rl e == ir.lenV rl e'
  | .scale _ e => shapeOkV rl e
  | .mul e e' => shapeOkV rl e && shapeOkV rl e' && ir.lenV rl e == ir.lenV rl e'
  | .reindex idx e => shapeOkV rl e && idx.inRangeNat (ir.lenV rl e)
  | .concat e e' => shapeOkV rl e && shapeOkV rl e'
  | .linear rows e => shapeOkV rl e && rows.all (·.all (·.1 < ir.lenV rl e))
  | .prod n e => shapeOkV rl e && 0 < n && ir.lenV rl e % n == 0
  | .mux b t e =>
      shapeOkV rl b && shapeOkV rl t && shapeOkV rl e &&
        ir.lenV rl b == ir.lenV rl t && ir.lenV rl t == ir.lenV rl e
  | .apply op e =>
      shapeOkV rl e && (0 < ir.colsV op && 0 < ir.rowsV op) && ir.lenV rl e % ir.colsV op == 0
  | .ref _ => true
  | .logic op w args => shapeOkVList rl args && logicShapeOk op w (ir.lenListV rl args)

/-- `shapeOkV` on a list of expressions. -/
def shapeOkVList (rl : ℕ → ℕ) : List Expr → Bool
  | [] => true
  | e :: es => shapeOkV rl e && shapeOkVList rl es

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

/-- `RefsOrdered`, checked in one pass. -/
def refsOrderedB : Bool := allIdx (fun k e => e.refs.all (· < k)) ir.exprs 0

theorem refsOrderedB_iff : ir.refsOrderedB = true ↔ ir.RefsOrdered := by
  simp only [refsOrderedB, allIdx_iff, Nat.zero_add, List.all_eq_true, decide_eq_true_eq,
    RefsOrdered, expr]

/-- **A deduplicated closure step**: the elements `g` gives the entry, and those of the entries
it reads. -/
def closureStep {α : Type} [DecidableEq α] (g : Expr → List α) (r : ℕ → List α) (_ : ℕ)
    (e : Expr) : List α :=
  insertAll (insertAll [] (g e)) (e.refs.flatMap r)

/-- **The table of a closure**: for each shared expression, the elements `g` gives it and the
entries it reads, each once. -/
def closureT {α : Type} [DecidableEq α] (g : Expr → List α) : NatTrie (List α) :=
  memo (closureStep g) [] ir.exprs

/-- **The table of the shared expressions' lengths.** -/
def lenT : NatTrie ℕ := memo (fun rl _ e => ir.lenV rl e) 0 ir.exprs

/-- **The table of the shared expressions' degrees**, the values having degrees `nd`. -/
def degT (nd : ℕ → ℕ) : NatTrie ℕ := memo (fun rd _ e => e.deg nd rd) 0 ir.exprs

/-- **The table of the shared expressions' vanishing at zero.** -/
def zeroT : NatTrie Bool := memo (fun rz _ e => e.zeroAtZero rz) false ir.exprs

/-- An expression's length, through the table. -/
def lenOf (e : Expr) : ℕ := ir.lenV (ir.lenT.getD · 0) e

/-- An expression's degree, the values having degrees `nd`, through the table. -/
def degM (nd : ℕ → ℕ) (e : Expr) : ℕ := e.deg nd ((ir.degT nd).getD · 0)

/-- An expression's vanishing at zero, through the table. -/
def zeroM (e : Expr) : Bool := e.zeroAtZero (ir.zeroT.getD · false)

/-- **Every element of a closure satisfies `p`**, through the table `closureT g`. -/
def closAll {α : Type} [DecidableEq α] (g : Expr → List α) (p : α → Bool) (e : Expr) : Bool :=
  (g e).all p && e.refs.all fun k => ((ir.closureT g).getD k []).all p

/-- **The values an expression reads**, through the table (with repetitions). -/
def nodesOf (e : Expr) : List ℕ :=
  e.directNodes ++ e.refs.flatMap fun k => (ir.closureT Expr.directNodes).getD k []

/-! ## The values' tables -/

/-- **The step of `readsT`**: what value `v` reads, from what the values it reads read (`r`). -/
def readsStep (r : ℕ → List Read) (v : ℕ) (x : Value) : List Read :=
  match x.kind with
  | .pub (.expr e) => insertAll [] ((ir.nodesOf e).flatMap r)
  | .pub (.opaque _ args) => insertAll [] (args.flatMap r)
  | .challenge c => [.chal c]
  | .late => [.late v]
  | .bits w _ => r w
  | .message u => [.late u]
  | _ => []

/-- **The table of what each value reads from the run** (`nodeReads`). -/
def readsT : NatTrie (List Read) := memo ir.readsStep [] ir.values

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

/-- **The predicates as a `NatTrie`.** -/
def predT : NatTrie Predicate := toTrie ir.predicates

/-- **Predicate `p`, through the table** (`O(log p)` steps where `RealizedProgram.predicate`, a
list lookup, takes `p`). -/
def predicateT (p : ℕ) : Predicate := ir.predT.getD p default

theorem predicateT_eq (p : ℕ) : ir.predicateT p = ir.predicate p := toTrie_getD_eq _ p

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
  ⟨ho, fun j _ r r' h => hF r r' j _ h⟩

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

/-- **The values an expression reads**, through the table. -/
theorem mem_nodesOf (ho : ir.RefsOrdered) {e : Expr} (he : ∀ k ∈ e.refs, k < ir.exprs.length)
    (v : ℕ) : v ∈ ir.nodesOf e ↔ v ∈ ir.exprNodes e := by
  rw [exprNodes, mem_closure_iff ho _ he]
  simp only [nodesOf, List.mem_append, List.mem_flatMap]

/-- **The length table holds the lengths** (`refLen`) at every fuel above the entry. -/
theorem lenT_getD (ho : ir.RefsOrdered) {n k : ℕ} (hkn : k < n) (hk : k < ir.exprs.length) :
    ir.refLen n k = ir.lenT.getD k 0 :=
  iter_rel_memo (R := Eq) (G := fun r k => Expr.len ir r (ir.expr k)) (fun _ _ => rfl)
    (fun _ _ _ _ h => by rw [lenV_eq]; exact Expr.len_congr ir _ h)
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
    (fun _ _ _ _ h => Expr.deg_congr _ (fun _ _ => rfl) h)
    (memoDeps_exprs ho fun _ _ _ e h => Expr.deg_congr e (fun _ _ => rfl) h) n k hkn hk

/-- **An expression's degree**, through the table. -/
theorem degM_eq (ho : ir.RefsOrdered) (nd : ℕ → ℕ) {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) : ir.degM nd e = ir.degOf nd e :=
  Expr.deg_congr e (fun _ _ => rfl) fun k hk => (degT_getD ho nd (he k hk) (he k hk)).symm

/-- **The vanishing table holds the vanishing** (`refZero`) at every fuel above the entry. -/
theorem zeroT_getD (ho : ir.RefsOrdered) {n k : ℕ} (hkn : k < n) (hk : k < ir.exprs.length) :
    ir.refZero n k = ir.zeroT.getD k false :=
  iter_rel_memo (R := Eq) (G := fun r k => (ir.expr k).zeroAtZero r) (fun _ _ => rfl)
    (fun _ _ _ _ h => Expr.zeroAtZero_congr _ h)
    (memoDeps_exprs ho fun _ _ _ e h => Expr.zeroAtZero_congr e h) n k hkn hk

/-- **An expression's vanishing at zero**, through the table. -/
theorem zeroM_eq (ho : ir.RefsOrdered) {e : Expr} (he : ∀ k ∈ e.refs, k < ir.exprs.length) :
    ir.zeroM e = ir.zeroOf e :=
  Expr.zeroAtZero_congr e fun k hk => (zeroT_getD ho (he k hk) (he k hk)).symm

end Tables

/-- **The values the definition of value `v` reads**: a public expression's values, an opaque
function's arguments, a bit view's words. -/
def valueDeps (v : ℕ) : List ℕ :=
  match (ir.value v).kind with
  | .pub (.expr e) => ir.exprNodes e
  | .pub (.opaque _ args) => args
  | .bits w _ => [w]
  | _ => []

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

theorem value_eq_default {v : ℕ} (hv : ir.values.length ≤ v) : ir.value v = default := by
  rw [value, List.getD_eq_getElem?_getD, List.getElem?_eq_none hv]
  rfl

theorem nodeReads_of_le {v : ℕ} (hv : ir.values.length ≤ v) : ∀ n, ir.nodeReads n v = []
  | 0 => rfl
  | n + 1 => by rw [nodeReads_succ, nodeReadsStep, value_eq_default hv]; rfl

theorem readsStep_congr (hwf : ir.WellFormed) :
    MemoDeps ir.readsStep ir.values ir.valueDeps := by
  refine ⟨fun v hv => hwf.valueDeps_lt hv, fun v hv r r' h => ?_⟩
  change ir.readsStep r v (ir.value v) = ir.readsStep r' v (ir.value v)
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
    (fun _ _ => rfl) (fun _ _ _ _ h => Expr.degV_congr _ (fun _ _ => rfl) h)
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
  change ir.valDegStep c r v (ir.value v) = ir.valDegStep c r' v (ir.value v)
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
  change (ir.valDegStep c r' v (ir.value v)).get i = ir.nodeDegAtStep c r v i
  unfold valueDeps at h
  unfold valDegStep nodeDegAtStep
  rcases hk : (ir.value v).kind with _ | ⟨_ | ⟨_, args⟩ | e⟩ | _ | _ | _ | ⟨w, sel⟩ | _ | _ <;>
    (rw [hk] at h; try simp only [RunVec.get_const])
  rw [degVM_get hwf.refsOrdered _ (hwf.pubExpr_refs hv hk)]
  exact congrFun (degAtOf_congr fun u hu => funext (h u hu)) i

end ValueTables

/-! ## The checkers -/

/-- **`ExprOk f e`**, through the tables. -/
def exprOkB (f : ℕ) (e : Expr) : Bool :=
  e.refs.all (· < ir.exprs.length) &&
    ir.closAll Expr.directNodes (· < ir.values.length) e &&
    ir.closAll Expr.fieldNodes (fun v => ir.valueFieldT v == f) e &&
    ir.closAll Expr.coefNodes ir.isPublicT e &&
    ir.shapeOkV (ir.lenT.getD · 0) e

/-- **`KindOk v k`**, through the tables: the values it reads through `valueT`, a public or bound
expression through the shared expressions' tables. -/
def kindOkB (v : ℕ) : Kind → Bool
  | .pub (.expr e) =>
    ir.exprOkB (ir.valueFieldT v) e && ir.closAll Expr.directNodes (· < v) e
  | .challenge c => decide (c < ir.challenges.length) && decide (ir.chalField c = ir.valueFieldT v)
  | .bits w sel =>
    decide (w < v) && decide (0 < sel.size) && sel.inRangeNat (ir.valueT w).size &&
      decide ((ir.valueT v).size % sel.size = 0)
  | .padCopy u _ => (ir.valueT u).kind.isLate
  | .message u =>
    decide (u < v) && (ir.valueT u).kind.isLate && decide (ir.valueFieldT u = ir.valueFieldT v)
  | .bound e =>
    ir.exprOkB (ir.valueFieldT v) e && ir.closAll Expr.directNodes (· < ir.values.length) e
  | k => decide (ir.KindOk v k)

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
    decide (∀ m ∈ ir.statement.checks, ir.CheckOk m) &&
    allIdx (fun _ x => ir.fieldOkV x) ir.values 0

/-- **The values a predicate reads**, through the table (with repetitions). -/
def predNodesM (b : PredBody) : List ℕ := b.exprs.flatMap (ir.nodesOf ·.2) ++ ir.tableCols b

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

/-- The degree in the committed cells (`cellDeg`'s value degrees). -/
def cellNd (v : ℕ) : ℕ := if ir.isCommitted v || ir.isLateNode v then 1 else 0

/-- `cellNd`, through the table. -/
def cellNdT (v : ℕ) : ℕ := if (ir.valueT v).isCommittedB || (ir.valueT v).kind.isLate then 1 else 0

theorem cellNdT_eq : ir.cellNdT = ir.cellNd := by
  funext v
  rw [cellNdT, cellNd, valueT_eq, isCommitted_eq, isLateNode]

/-- **The parts of each batch**, each as a set (`natSet`), by batch. -/
def batchPartsT : NatTrie (NatTrie Unit) := toTrie (ir.batches.map fun B => natSet B.parts)

/-- **Predicate `pid` is a part of batch `b`**, through the table. -/
def inPartsB (b pid : ℕ) : Bool := ((ir.batchPartsT.getD b default).get? pid).isSome

theorem inPartsB_iff {b : ℕ} (hb : b < ir.batches.length) (pid : ℕ) :
    ir.inPartsB b pid = true ↔ pid ∈ (ir.batch b).parts := by
  rw [inPartsB, batchPartsT, toTrie_getD (by simpa using hb), List.getD_eq_getElem?_getD,
    List.getElem?_map, batch, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]
  exact natSet_isSome _ pid

/-- **The values of a circuit's input blocks by kind, and its predicates**, each as a set
(`natSet`). -/
structure CircuitSets where
  /-- The values of the committed blocks. -/
  committed : NatTrie Unit
  /-- The values of the public blocks. -/
  pub : NatTrie Unit
  /-- The late values of the pad blocks. -/
  pad : NatTrie Unit
  /-- The values of the view blocks. -/
  view : NatTrie Unit
  /-- The predicates. -/
  preds : NatTrie Unit
  deriving Inhabited

/-- The value of a committed block. -/
def _root_.GordieHowe.RealizedProgram.InputBlock.committedOf? : InputBlock → Option ℕ
  | .committed u _ _ => some u
  | _ => none

/-- The value of a public block. -/
def _root_.GordieHowe.RealizedProgram.InputBlock.pubOf? : InputBlock → Option ℕ
  | .pub u _ _ => some u
  | _ => none

/-- The late value of a pad block. -/
def _root_.GordieHowe.RealizedProgram.InputBlock.padOf? : InputBlock → Option ℕ
  | .pad u _ _ => some u
  | _ => none

/-- The value of a view block. -/
def _root_.GordieHowe.RealizedProgram.InputBlock.viewOf? : InputBlock → Option ℕ
  | .view u _ _ => some u
  | _ => none

/-- **A circuit's sets.** -/
def circuitSets (C : Circuit) : CircuitSets :=
  ⟨natSet (C.inputs.filterMap InputBlock.committedOf?), natSet (C.inputs.filterMap InputBlock.pubOf?),
    natSet (C.inputs.filterMap InputBlock.padOf?), natSet (C.inputs.filterMap InputBlock.viewOf?),
    natSet C.predicates⟩

/-- Whether key `v` is in the set `t`. -/
def natMem (t : NatTrie Unit) (v : ℕ) : Bool := (t.get? v).isSome

theorem any_isCommittedOf_iff (ins : List InputBlock) (v : ℕ) :
    ins.any (·.isCommittedOf v) = true ↔ natMem (natSet (ins.filterMap InputBlock.committedOf?)) v = true := by
  rw [natMem, natSet_isSome]
  simp only [List.any_eq_true, List.mem_filterMap]
  refine exists_congr fun b => and_congr_right fun _ => ?_
  cases b <;> simp [InputBlock.isCommittedOf, InputBlock.committedOf?]

theorem any_isPubOf_iff (ins : List InputBlock) (v : ℕ) :
    ins.any (·.isPubOf v) = true ↔ natMem (natSet (ins.filterMap InputBlock.pubOf?)) v = true := by
  rw [natMem, natSet_isSome]
  simp only [List.any_eq_true, List.mem_filterMap]
  refine exists_congr fun b => and_congr_right fun _ => ?_
  cases b <;> simp [InputBlock.isPubOf, InputBlock.pubOf?]

theorem any_isPadOf_iff (ins : List InputBlock) (v : ℕ) :
    ins.any (·.isPadOf v) = true ↔ natMem (natSet (ins.filterMap InputBlock.padOf?)) v = true := by
  rw [natMem, natSet_isSome]
  simp only [List.any_eq_true, List.mem_filterMap]
  refine exists_congr fun b => and_congr_right fun _ => ?_
  cases b <;> simp [InputBlock.isPadOf, InputBlock.padOf?]

theorem any_isViewOf_iff (ins : List InputBlock) (v : ℕ) :
    ins.any (·.isViewOf v) = true ↔ natMem (natSet (ins.filterMap InputBlock.viewOf?)) v = true := by
  rw [natMem, natSet_isSome]
  simp only [List.any_eq_true, List.mem_filterMap]
  refine exists_congr fun b => and_congr_right fun _ => ?_
  cases b <;> simp [InputBlock.isViewOf, InputBlock.viewOf?]

/-- **`IsCircuitInputOf`**, through a circuit's sets. -/
def isCircuitInputT (S : CircuitSets) (v : ℕ) : Kind → Bool
  | .priv => natMem S.committed v
  | .pub _ => natMem S.pub v
  | .constant _ => true
  | .challenge _ => natMem S.pub v
  | .late => natMem S.pub v && natMem S.pad v
  | .bits _ _ => natMem S.view v
  | .padCopy _ _ => natMem S.committed v
  | .message _ => natMem S.pub v
  | .bound _ => true

theorem isCircuitInputT_iff (C : Circuit) (v : ℕ) (k : Kind) :
    isCircuitInputT (circuitSets C) v k = true ↔ IsCircuitInputOf C.inputs v k := by
  cases k <;> simp only [isCircuitInputT, IsCircuitInputOf, circuitSets, any_isCommittedOf_iff,
    any_isPubOf_iff, any_isPadOf_iff, any_isViewOf_iff, Bool.and_eq_true]

/-- **The circuits' sets**, by circuit. -/
def circuitT : NatTrie CircuitSets := toTrie (ir.circuits.map circuitSets)

theorem circuitT_getD {c : ℕ} (hc : c < ir.circuits.length) :
    ir.circuitT.getD c default = circuitSets (ir.circuit c) := by
  rw [circuitT, toTrie_getD (by simpa using hc), List.getD_eq_getElem?_getD, List.getElem?_map,
    circuit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
  rfl

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
  cases b <;> simp only [BodyRefsOk, PredBody.exprs, List.mem_cons, List.mem_map,
    forall_eq_or_imp, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at hb <;>
    simp only [lensOkB, LensOk, beq_iff_eq]
  · rw [lenOf_eq ho hb.1, lenOf_eq ho hb.2]
  · rw [lenOf_eq ho hb.1, lenOf_eq ho hb.2]
  · rw [lenOf_eq ho hb.1, lenOf_eq ho hb.2]

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
  rw [shapeOkV_eq, ← shapeOkWith_lenT ho fun k' hk' => by have := ho k hk k' hk'; omega]
  rfl

/-- **`wellFormedB` is `WellFormed`.** -/
theorem wellFormedB_iff : ir.wellFormedB = true ↔ ir.WellFormed := by
  rw [wellFormed_iff]
  by_cases ho : ir.RefsOrdered
  · simp only [wellFormedB, (refsOrderedB_iff ir).2 ho, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq, allIdx_iff, Nat.zero_add, exprsShape_iff ho, List.all_eq_true,
      predOkB_iff ho]
    have hv : ∀ v < ir.values.length, ((ir.values.getD v default).domain < ir.domains.length ∧
        ir.kindOkB v (ir.values.getD v default).kind = true) ↔ ir.ValueOk v := fun v _ => by
      rw [kindOkB_iff ho]
      rfl
    have hf : ∀ v, ir.fieldOkV (ir.values.getD v default) = true ↔ ir.FieldOk v :=
      fun v => ir.fieldOkV_iff v
    simp only [ExprsOk, hf]
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
      exact ⟨h1, fun v hv' => (hv v hv').1 (h2 v hv'), fun k hk => ⟨ho k hk, h3 k hk⟩, h4, h5, h6,
        h7⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
      exact ⟨⟨⟨⟨⟨⟨h1, fun v hv' => (hv v hv').2 (h2 v hv')⟩, fun k hk => (h3 k hk).2⟩, h4⟩, h5⟩,
        h6⟩, h7⟩
  · have hb : ir.refsOrderedB = false :=
      Bool.eq_false_iff.2 fun h => ho ((refsOrderedB_iff ir).1 h)
    simp only [wellFormedB, hb, Bool.false_and, Bool.false_eq_true, false_iff]
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
        exact absurd hpub (by simpa [value] using h')
      · have := h' c hc
        rw [RunVec.maxUpTo_eq] at this
        rw [show maxBelow (ir.value v).size (ir.nodeDegAt c ir.fuel v) =
          maxBelow (ir.value v).size (ir.valDegM c v).get from
            maxBelow_congr fun i _ => (valDegM_get hwf c hv i).symm]
        simpa [value] using this
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
        simpa [value] using this
      · refine .inl ?_
        rw [isPubExpr_eq] at hpub
        simpa [value] using hpub

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
  rw [predicate, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
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
    simp only [BodyRefsOk, PredBody.exprs, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true] at hb
    simp only [bodyAdmittedB, BodyAdmitted, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
    refine and_congr (by tauto) ?_
    cases real.target with
    | none => simp [OptTargetAdmits]
    | some t => exact targetAdmitsB_iff ho pid d hb.1 hb.2 t
  | cross => simp [bodyAdmittedB, BodyAdmitted]

/-- **`targetsB` is `TargetsAdmit`** for a well-formed program. -/
theorem targetsB_iff (hwf : ir.WellFormed) : ir.targetsB = true ↔ ir.TargetsAdmit := by
  rw [targetsAdmit_iff]
  simp only [targetsB, Bool.and_eq_true, allIdx_iff, Nat.zero_add, List.all_eq_true,
    decide_eq_true_eq]
  rw [and_assoc]
  refine and_congr (forall₂_congr fun pid hpid => ?_)
    (and_congr (forall₂_congr fun c _ => forall₂_congr fun pid _ => ?_) Iff.rfl)
  · exact bodyAdmittedB_iff hwf.refsOrdered pid (hwf.bodyRefsOk (predicate_mem hpid))
  · constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [predT, toTrie_getD h1] at h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [predT, toTrie_getD h1]⟩

end Checkers

end

end GordieHowe.RealizedProgram
