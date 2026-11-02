-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Valid

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Check`

The definitions of `GordieHowe.Language.RealizedProgram.Check` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/Check.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **A predicate holds at every position of a list**, the positions counted from `i`
(`allIdx_nil`, `allIdx_cons`), by the recursor: each step matches on the position (`Nat.casesOn`),
so the kernel keeps it a literal, and costs one `List.rec` step where a structural definition costs
a `brecOn` step. Compiled code runs `allIdxC` (`allIdx_csimp`). -/
noncomputable def allIdx {α : Type} (p : ℕ → α → Bool) (l : List α) (i : ℕ) : Bool :=
  @List.rec α (fun _ => ℕ → Bool) (fun _ => true)
    (fun x _ ih i => p i x && @Nat.casesOn (fun _ => Bool) i (ih 1) fun k => ih (k + 2)) l i

theorem allIdx_cons {α : Type} (p : ℕ → α → Bool) (x : α) (xs : List α) (i : ℕ) :
    allIdx p (x :: xs) i = (p i x && allIdx p xs (i + 1)) := by
  cases i <;> rfl

/-- **A predicate holds at every position of a list**, by structural recursion: the code compiled
for `allIdx`. -/
def allIdxC {α : Type} (p : ℕ → α → Bool) : List α → ℕ → Bool
  | [], _ => true
  | x :: xs, i => p i x && allIdxC p xs (i + 1)

@[csimp] theorem allIdx_csimp : @allIdx = @allIdxC := by
  funext α p l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    funext i
    rw [allIdx_cons, allIdxC, ih]

/-- **`l.all f`**, by the recursor (`allK_eq`): one `List.rec` step per element, where `List.all`
costs a `brecOn` step. Compiled code runs `List.all` (`allK_csimp`). -/
noncomputable def allK {α : Type} (f : α → Bool) (l : List α) : Bool :=
  @List.rec α (fun _ => Bool) true (fun x _ ih => f x && ih) l

/-- **`l.all f`**: the code compiled for `allK`. -/
def allC {α : Type} (f : α → Bool) (l : List α) : Bool := l.all f

theorem allK_eq {α : Type} (f : α → Bool) : ∀ l : List α, allK f l = l.all f
  | [] => rfl
  | x :: xs => by
    change (f x && allK f xs) = _
    rw [allK_eq f xs, List.all_cons]

@[csimp] theorem allK_csimp : @allK = @allC := by
  funext α f l
  exact allK_eq f l

/-- **The positions of a list whose entries fail `f`**, as a bit set, the positions counted from
`i`: bit `i + j` set when `f (i + j)` fails at entry `j` (`testBit_failBits`). One `Nat` operation
per entry, by the recursor, the position matched on at each step (`Nat.casesOn`) so the kernel
keeps it a literal; a test of a position is then one `Nat.testBit` (`bitTest`), where a lookup in a
`NatTrie` costs several steps per level. Compiled code runs `failBitsC` (`failBits_csimp`). -/
noncomputable def failBits {α : Type} (f : ℕ → α → Bool) (l : List α) (i : ℕ) : ℕ :=
  @List.rec α (fun _ => ℕ → ℕ) (fun _ => 0)
    (fun x _ ih i => Nat.lor (cond (f i x) 0 (2 ^ i))
      (@Nat.casesOn (fun _ => ℕ) i (ih 1) fun k => ih (k + 2))) l i

theorem failBits_cons {α : Type} (f : ℕ → α → Bool) (x : α) (xs : List α) (i : ℕ) :
    failBits f (x :: xs) i = Nat.lor (cond (f i x) 0 (2 ^ i)) (failBits f xs (i + 1)) := by
  cases i <;> rfl

/-- **`failBits`, by structural recursion**: the code compiled for `failBits`. -/
def failBitsC {α : Type} (f : ℕ → α → Bool) : List α → ℕ → ℕ
  | [], _ => 0
  | x :: xs, i => Nat.lor (cond (f i x) 0 (2 ^ i)) (failBitsC f xs (i + 1))

@[csimp] theorem failBits_csimp : @failBits = @failBitsC := by
  funext α f l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    funext i
    rw [failBits_cons, failBitsC, ih]

/-- **`f` at position `v` of a list, through the bit set of its failing positions** (`bitTest_eq`):
for `v` below the length `n`, the bit of `v` clear in `bits`; past the end, `dflt`. -/
def bitTest (bits n : ℕ) (dflt : Bool) (v : ℕ) : Bool :=
  if v < n then !bits.testBit v else dflt

/-- **`allNatIn`, by `List.range'`**: the code compiled for it. -/
def allNatInC (P : ℕ → Bool) (i j : ℕ) : Bool := (List.range' i (j - i)).all P

/-- **The elements of `l` added to `acc`**, each once (`List.insert`). -/
def insertAll {α : Type} [DecidableEq α] : List α → List α → List α
  | acc, [] => acc
  | acc, x :: xs => insertAll (acc.insert x) xs

/-- **A table of a list's entries, each computed from the earlier ones**: entry `j` (the list's
element `x`) is `F r j x`, `r` reading the entries already set (`d` when unset). -/
def memoAux {γ β : Type} (F : (ℕ → β) → ℕ → γ → β) (d : β) :
    List γ → ℕ → NatTrie β → NatTrie β
  | [], _, t => t
  | x :: xs, j, t => memoAux F d xs (j + 1) (t.set j (F (t.getD · d) j x))

/-- **`memoAux` with the entries also listed**: the table, and after `acc` (in reverse) the entries
in the order they are set. Each entry is one term in both, so the kernel computes it once. -/
def memoAuxL {γ β : Type} (F : (ℕ → β) → ℕ → γ → β) (d : β) :
    List γ → ℕ → NatTrie β → List β → NatTrie β × List β
  | [], _, t, acc => (t, acc.reverse)
  | x :: xs, j, t, acc =>
    memoAuxL F d xs (j + 1) (t.set j (F (t.getD · d) j x)) (F (t.getD · d) j x :: acc)

/-- **The table of a list's entries** (`memoAux` from the empty table, `memo_eq`), computed with
their list (`memoList`). -/
def memo {γ β : Type} (F : (ℕ → β) → ℕ → γ → β) (d : β) (L : List γ) : NatTrie β :=
  (memoAuxL F d L 0 .nil []).1

/-- **The entries of `memo`, in order** (`getD_memoList`): a pass over a list zipped with them reads
each entry without a lookup in the table. -/
def memoList {γ β : Type} (F : (ℕ → β) → ℕ → γ → β) (d : β) (L : List γ) : List β :=
  (memoAuxL F d L 0 .nil []).2

/-- **A list as a `NatTrie`** (`NatTrie.ofSeq`): entry `j` at key `j`. -/
def toTrie {γ : Type} [Inhabited γ] (L : List γ) : NatTrie γ := NatTrie.ofSeq L

theorem toTrie_getD {γ : Type} [Inhabited γ] {L : List γ} {j : ℕ} (_ : j < L.length) :
    (toTrie L).getD j default = L.getD j default :=
  NatTrie.getD_ofSeq L j default

/-- **A list as a `NatTrie` reads as the list at every index**, past its end too. -/
theorem toTrie_getD_eq {γ : Type} [Inhabited γ] (L : List γ) (j : ℕ) :
    (toTrie L).getD j default = L.getD j default :=
  NatTrie.getD_ofSeq L j default

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

theorem valueT_eq (v : ℕ) : ir.valueT v = ir.value v :=
  (toTrie_getD_eq ir.values v).trans (ir.value_eq_getD v).symm

/-- Compiled code reads value `v` by a walk of the values (`valueC`), as for `value`: the table
is a closed term only for the kernel, and compiled code would build it at every call. -/
@[csimp] theorem valueT_csimp : @valueT = @valueC := by
  funext ir v
  rw [valueT_eq, value_eq_getD]
  rfl

/-- Whether a value is committed in phase `0` (`RealizedProgram.isCommitted`). -/
def _root_.GordieHowe.RealizedProgram.Value.isCommittedB (x : Value) : Bool :=
  match x.kind with
  | .priv => true
  | .bits _ _ => true
  | .padCopy _ _ => true
  | .bound _ => true
  | _ => false

/-- **A value is a late value node of a phase of the program** (`RealizedProgram.IsLate`). -/
def isLateV (x : Value) : Bool := x.kind.isLate && decide (1 ≤ x.phase) && decide (x.phase ≤ ir.phases)

/-- The field of a value (`RealizedProgram.valueField`). -/
def fieldOfV (x : Value) : ℕ :=
  match x.kind.allowsField, x.field with
  | true, some f => f
  | _, _ => ir.domainField x.domain

/-- The field of value `v`, through the table. -/
def valueFieldT (v : ℕ) : ℕ := ir.fieldOfV (ir.valueT v)

/-- Whether value `v` is public (`RealizedProgram.isPublic`), through the table. -/
def isPublicT (v : ℕ) : Bool := !(ir.valueT v).isCommittedB && !(ir.valueT v).kind.isLate

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

/-- Whether value `v` is a cell of the quadratic test (`RealizedProgram.isQuadCell`), through the
table. -/
def isQuadCellT (v : ℕ) : Bool :=
  match (ir.valueT v).kind with
  | .priv => (ir.valueT v).phase == 0 && (ir.valueT v).type == .field
  | _ => false

/-- **The quadratic form** (`RealizedProgram.isQuadratic`), through the table. -/
def isQuadraticT : Expr → Expr → Bool
  | .mul (.leaf a) (.leaf b), .leaf c => ir.isQuadCellT a && ir.isQuadCellT b && ir.isQuadCellT c
  | _, _ => false

/-- **A value's field is well formed** (`RealizedProgram.FieldOk`), on the value. -/
def fieldOkV (x : Value) : Bool :=
  match x.field with
  | none => true
  | some f => decide (f < ir.fields.length) && x.kind.allowsField && decide (x.type = .field)

end ValueTable

/-- **`size a m`'s fold, its accumulator evaluated at each run** (`IndexMap.sizeAuxK_eq`), by the
recursors: `size` is a `map` and a `foldr` the kernel evaluates with a `brecOn` step per run and a
pending addition per run; here each step's `Nat.casesOn` on the accumulator makes the kernel
evaluate it to a literal. Compiled code runs `IndexMap.size` (`IndexMap.sizeK_csimp`). -/
noncomputable def IndexMap.sizeAuxK (m : IndexMap) : ℕ → ℕ :=
  @List.rec _ (fun _ => ℕ → ℕ) (fun a => a)
    (fun r _ ih a => @Nat.casesOn (fun _ => ℕ) a (ih r.2.2) fun k => ih (k + 1 + r.2.2)) m

theorem IndexMap.sizeAuxK_eq : ∀ (m : IndexMap) (a : ℕ), IndexMap.sizeAuxK m a = a + m.size
  | [], a => by simp [sizeAuxK, size]
  | r :: rs, a => by
    change @Nat.casesOn (fun _ => ℕ) a (IndexMap.sizeAuxK rs r.2.2)
      (fun k => IndexMap.sizeAuxK rs (k + 1 + r.2.2)) = _
    cases a with
    | zero =>
      change IndexMap.sizeAuxK rs r.2.2 = _
      rw [sizeAuxK_eq rs]; simp [size]
    | succ k =>
      change IndexMap.sizeAuxK rs (k + 1 + r.2.2) = _
      rw [sizeAuxK_eq rs]; simp [size]; omega

/-- **An index map's size**, its accumulator evaluated at each run (`IndexMap.sizeK_eq`). -/
noncomputable def IndexMap.sizeK (m : IndexMap) : ℕ := IndexMap.sizeAuxK m 0

theorem IndexMap.sizeK_eq (m : IndexMap) : m.sizeK = m.size := by
  simp [sizeK, sizeAuxK_eq]

@[csimp] theorem IndexMap.sizeK_csimp : @IndexMap.sizeK = @IndexMap.size := by
  funext m
  exact IndexMap.sizeK_eq m

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

mutual

/-- **`Expr.len`, the values through the table.** -/
def lenV (rl : ℕ → ℕ) : Expr → ℕ
  | .leaf v => (ir.valueT v).size
  | .add e _ => lenV rl e
  | .sub e _ => lenV rl e
  | .scale _ e => lenV rl e
  | .mul e _ => lenV rl e
  | .reindex idx _ => idx.sizeK
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

end LenV

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

/-- **`runLowOk`, in `Nat.beq` and `Nat.ble`** (`runLowOkK_eq`). -/
def runLowOkK : ℕ × ℤ × ℕ → Bool
  | (_, .ofNat _, _) => true
  | (s, .negSucc m, c) => Nat.beq c 0 || Nat.ble ((m + 1) * (c - 1)) s

theorem runLowOkK_eq (r : ℕ × ℤ × ℕ) : runLowOkK r = runLowOk r := by
  obtain ⟨s, d, c⟩ := r
  cases d with
  | ofNat _ => rfl
  | negSucc m =>
    apply Bool.eq_iff_iff.2
    simp [runLowOkK, runLowOk, Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq]

/-- **`runBound`, in `Nat.beq` and `cond`** (`runBoundK_eq`). -/
def runBoundK : ℕ × ℤ × ℕ → ℕ
  | (s, .ofNat d, c) => cond (Nat.beq c 0) 0 (s + d * (c - 1) + 1)
  | (s, .negSucc _, c) => cond (Nat.beq c 0) 0 (s + 1)

theorem runBoundK_eq (r : ℕ × ℤ × ℕ) : runBoundK r = runBound r := by
  obtain ⟨s, d, c⟩ := r
  cases d <;> by_cases hc : c = 0 <;> simp [runBoundK, runBound, hc, Nat.beq_eq]

/-- **Every run's `runLowOk`**, by the recursor (`lowOkK_eq`). -/
noncomputable def lowOkK (m : IndexMap) : Bool :=
  @List.rec _ (fun _ => Bool) true (fun r _ ih => runLowOkK r && ih) m

theorem lowOkK_eq (m : IndexMap) : lowOkK m = m.all runLowOk := by
  induction m with
  | nil => rfl
  | cons r rs ih =>
    change (runLowOkK r && lowOkK rs) = _
    rw [ih, runLowOkK_eq, List.all_cons]

/-- **Every run's `runLowOk`**: the code compiled for `lowOkK`. -/
def lowOk (m : IndexMap) : Bool := m.all runLowOk

@[csimp] theorem lowOkK_csimp : @lowOkK = @lowOk := by
  funext m
  exact lowOkK_eq m

/-- **`boundAux a m`, its accumulator evaluated at each run** (`boundAuxK_eq`), by the recursors:
the accumulator is matched on (`Nat.casesOn`) before each step, so the kernel evaluates it to a
literal there. -/
noncomputable def boundAuxK (m : IndexMap) : ℕ → ℕ :=
  @List.rec _ (fun _ => ℕ → ℕ) (fun a => a)
    (fun r _ ih a => @Nat.casesOn (fun _ => ℕ) a (ih (runBoundK r))
      fun k => ih (cond (Nat.ble (k + 1) (runBoundK r)) (runBoundK r) (k + 1))) m

theorem boundAuxK_eq : ∀ (m : IndexMap) (a : ℕ), boundAuxK m a = boundAux a m
  | [], _ => rfl
  | r :: rs, a => by
    change @Nat.casesOn (fun _ => ℕ) a (boundAuxK rs (runBoundK r))
      (fun k => boundAuxK rs (cond (Nat.ble (k + 1) (runBoundK r)) (runBoundK r) (k + 1))) = _
    rw [boundAux, runBoundK_eq]
    cases a with
    | zero => exact boundAuxK_eq rs _
    | succ k =>
      change boundAuxK rs (cond (Nat.ble (k + 1) (runBound r)) (runBound r) (k + 1)) = _
      rw [boundAuxK_eq rs]
      cases Nat.ble (k + 1) (runBound r) <;> rfl

/-- **`bound`, its accumulator evaluated at each run** (`boundK_eq`). -/
noncomputable def boundK (m : IndexMap) : ℕ := boundAuxK m 0

theorem boundK_eq (m : IndexMap) : boundK m = m.bound := boundAuxK_eq m 0

@[csimp] theorem boundK_csimp : @boundK = @bound := by
  funext m
  exact boundK_eq m

/-- **`IndexMap.inRange`, in natural arithmetic** (`inRangeNat_eq`), the bound `n` read once: the
per-map facts (`runLowOk` on every run, `lowOkK`, and `bound`, `boundK`) do not depend on `n`, so the
kernel computes them once per index map, and each use compares one number. -/
def inRangeNat (m : IndexMap) (n : ℕ) : Bool := lowOkK m && Nat.ble (boundK m) n

end IndexMap

section

variable (ir : RealizedProgram)

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

/-- An expression's length, through the table. -/
def lenOf (e : Expr) : ℕ := ir.lenV (ir.lenT.getD · 0) e

/-- **Every element of a closure satisfies `p`**, through the table `closureT g`. -/
def closAll {α : Type} [DecidableEq α] (g : Expr → List α) (p : α → Bool) (e : Expr) : Bool :=
  (g e).all p && e.refs.all fun k => ((ir.closureT g).getD k []).all p

/-- **`closAll` with the table built once**: the code compiled for `closAll` (`closAll_csimp`).
Compiled code evaluates `closureT g` where it is read, once per reference; here it is built at
the first reference (a `Thunk`), and not at all for an expression without one. -/
def closAllC {α : Type} [DecidableEq α] (g : Expr → List α) (p : α → Bool) (e : Expr) : Bool :=
  let T := Thunk.mk fun _ => ir.closureT g
  (g e).all p && e.refs.all fun k => (T.get.getD k []).all p

@[csimp] theorem closAll_csimp : @closAll = @closAllC := rfl

/-- **Every element of each shared expression's closure satisfies `p`**, as a table of flags
(`closFlagT_getD`): entry `k` from `g` of the entry and the flags of the entries it reads, one
`Bool` per entry where `closureT` keeps each closure as a list. -/
def closFlagT {α : Type} (g : Expr → List α) (p : α → Bool) : NatTrie Bool :=
  memo (fun r _ e => (g e).all p && e.refs.all r) false ir.exprs

/-- **The flags of `closFlagT`, in entry order** (`getD_memoList`). -/
def closFlagL {α : Type} (g : Expr → List α) (p : α → Bool) : List Bool :=
  memoList (fun r _ e => (g e).all p && e.refs.all r) false ir.exprs

/-- **The entries whose closure has an element failing `p`**, as a bit set (`failBits` of the
flags). -/
def closFlagBits {α : Type} (g : Expr → List α) (p : α → Bool) : ℕ :=
  failBits (fun _ b => b) (ir.closFlagL g p) 0

/-- **Every element of an expression's closure satisfies `p`** (`closFlag_eq`): `g` of the
expression, then each entry it reads by one `Nat.testBit` of `closFlagBits`, where a lookup in a
`NatTrie` costs a walk down the trie. -/
def closFlag {α : Type} (g : Expr → List α) (p : α → Bool) (e : Expr) : Bool :=
  (g e).all p && e.refs.all (bitTest (ir.closFlagBits g p) (ir.closFlagL g p).length false)

/-- **`closFlag` with the bit set built once**, at the first reference: the code compiled for
`closFlag` (`closFlag_csimp`). -/
def closFlagC {α : Type} (g : Expr → List α) (p : α → Bool) (e : Expr) : Bool :=
  let T := Thunk.mk fun _ => (ir.closFlagBits g p, (ir.closFlagL g p).length)
  (g e).all p && e.refs.all (bitTest T.get.1 T.get.2 false)

@[csimp] theorem closFlag_csimp : @closFlag = @closFlagC := rfl

/-- **The values an expression reads**, through the table (with repetitions). -/
def nodesOf (e : Expr) : List ℕ :=
  e.directNodes ++ e.refs.flatMap fun k => (ir.closureT Expr.directNodes).getD k []

/-- **`nodesOf` with the table built once**, at the first reference: the code compiled for
`nodesOf` (`nodesOf_csimp`). -/
def nodesOfC (e : Expr) : List ℕ :=
  let T := Thunk.mk fun _ => ir.closureT Expr.directNodes
  e.directNodes ++ e.refs.flatMap fun k => T.get.getD k []

@[csimp] theorem nodesOf_csimp : @nodesOf = @nodesOfC := rfl

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

/-- **What each value reads from the run, in value order** (`readsT`'s entries, `getD_readsL`),
for a pass over the values zipped with it. -/
def readsL : List (List Read) := memoList ir.readsStep [] ir.values

/-- **The predicates as a `NatTrie`.** -/
def predT : NatTrie Predicate := toTrie ir.predicates

/-- **Predicate `p`, through the table** (`O(log p)` steps where `RealizedProgram.predicate`, a
list lookup, takes `p`). -/
def predicateT (p : ℕ) : Predicate := ir.predT.getD p default

theorem predicateT_eq (p : ℕ) : ir.predicateT p = ir.predicate p :=
  (toTrie_getD_eq _ p).trans (ir.predicate_eq_getD p).symm

/-- Compiled code reads predicate `p` by a walk of the predicates (`predicateC`), as for
`predicate`. -/
@[csimp] theorem predicateT_csimp : @predicateT = @predicateC := by
  funext ir p
  rw [predicateT_eq, predicate_eq_getD]
  rfl

/-- **`ExprOk f e`**, through the tables. -/
def exprOkB (f : ℕ) (e : Expr) : Bool :=
  e.refs.all (· < ir.exprs.length) &&
    ir.closAll Expr.directNodes (· < ir.values.length) e &&
    ir.closAll Expr.fieldNodes (fun v => ir.valueFieldT v == f) e &&
    ir.closAll Expr.pubNodes ir.isPublicT e &&
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

/-- **The values a predicate reads**, through the table (with repetitions). -/
def predNodesM (b : PredBody) : List ℕ := b.exprs.flatMap (ir.nodesOf ·.2) ++ ir.tableCols b

/-- `cellNd`, through the table. -/
def cellNdT (v : ℕ) : ℕ := if (ir.valueT v).isCommittedB || (ir.valueT v).kind.isLate then 1 else 0

/-- **The parts of each batch**, each as a set (`natSet`), by batch. -/
def batchPartsT : NatTrie (NatTrie Unit) := toTrie (ir.batches.map fun B => natSet B.parts)

/-- **Predicate `pid` is a part of batch `b`**, through the table. -/
def inPartsB (b pid : ℕ) : Bool := ((ir.batchPartsT.getD b default).get? pid).isSome

/-- **`inPartsB`, on batch `b`'s parts**: the code compiled for `inPartsB` (`inPartsB_csimp`).
Compiled code would build `batchPartsT`, a table of every batch's parts, at every call. -/
def inPartsBC (b pid : ℕ) : Bool := (ir.batch b).parts.contains pid

theorem inPartsB_eq (b pid : ℕ) : ir.inPartsB b pid = ir.inPartsBC b pid := by
  have h : (ir.batches.map fun B => natSet B.parts).getD b default =
      natSet (ir.batches.getD b default).parts := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases ir.batches[b]? <;> rfl
  rw [inPartsB, inPartsBC, batchPartsT, toTrie_getD_eq, h, batch, Bool.eq_iff_iff,
    natSet_isSome, List.contains_iff_mem]

@[csimp] theorem inPartsB_csimp : @inPartsB = @inPartsBC := by
  funext ir b pid
  exact ir.inPartsB_eq b pid

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

/-- **`isCircuitInputT` at a circuit's sets, by scans of its input blocks** (`isCircuitInputT_circuitSets`):
compiled code reads a circuit's inputs this way, building no set. -/
def isCircuitInputL (C : Circuit) (v : ℕ) : Kind → Bool
  | .priv => C.inputs.any (·.isCommittedOf v)
  | .pub _ => C.inputs.any (·.isPubOf v)
  | .constant _ => true
  | .challenge _ => C.inputs.any (·.isPubOf v)
  | .late => C.inputs.any (·.isPubOf v) && C.inputs.any (·.isPadOf v)
  | .bits _ _ => C.inputs.any (·.isViewOf v)
  | .padCopy _ _ => C.inputs.any (·.isCommittedOf v)
  | .message _ => C.inputs.any (·.isPubOf v)
  | .bound _ => true

theorem isCircuitInputT_circuitSets (C : Circuit) (v : ℕ) (k : Kind) :
    isCircuitInputT (circuitSets C) v k = isCircuitInputL C v k := by
  have hc := Bool.eq_iff_iff.2 (any_isCommittedOf_iff C.inputs v)
  have hp := Bool.eq_iff_iff.2 (any_isPubOf_iff C.inputs v)
  have hd := Bool.eq_iff_iff.2 (any_isPadOf_iff C.inputs v)
  have hv := Bool.eq_iff_iff.2 (any_isViewOf_iff C.inputs v)
  cases k <;> simp only [isCircuitInputT, isCircuitInputL, circuitSets, hc, hp, hd, hv]

theorem circuitSets_preds (C : Circuit) : (circuitSets C).preds = natSet C.predicates := rfl

/-- **Membership in a list's set is the list's `contains`.** -/
theorem natMem_natSet (L : List ℕ) (v : ℕ) : natMem (natSet L) v = L.contains v := by
  rw [Bool.eq_iff_iff, natMem, natSet_isSome, List.contains_iff_mem]

/-- **The circuits' sets**, by circuit. -/
def circuitT : NatTrie CircuitSets := toTrie (ir.circuits.map circuitSets)

theorem circuitT_getD {c : ℕ} (hc : c < ir.circuits.length) :
    ir.circuitT.getD c default = circuitSets (ir.circuit c) := by
  rw [circuitT, toTrie_getD (by simpa using hc), List.getD_eq_getElem?_getD, List.getElem?_map,
    circuit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
  rfl

end

end GordieHowe.RealizedProgram
