-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Circuit.NttPure

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Circuit.RelTable`

The definitions of `GordieHowe.Language.Realizations.Circuit.RelTable` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Circuit/RelTable.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold GordieHowe.Twin
open GordieHowe.GKR.Rel (Wire TE Place EntryCert Assert)

/-- **The environment of a certificate** at the code arithmetic `ar`. -/
def CircuitData.env (cd : CircuitData) (ar : CodeArith) : TEnv :=
  ⟨cd.consts, ar, cd.neg1, cd.half, cd.char2, cd.dag.inputs⟩

/-- **Which guard of a family record fails** (`RelFamily.lean`). -/
inductive FamReason where
  /-- The entry's kind and its record's family differ, or a table, group or field is not the
  record's. -/
  | kind
  /-- The node of `α`. -/
  | alpha
  /-- The nodes of the needles. -/
  | needles
  /-- The nodes of the histograms. -/
  | hists
  /-- The block of the weights. -/
  | weights
  /-- The fraction tree's spans or size. -/
  | tree
  /-- The node of the MAC's powers. -/
  | powers
  /-- The node of the MAC's tag. -/
  | tag
  /-- The node of the MAC's operand. -/
  | bits
  /-- The MAC's chunks. -/
  | chunks
  /-- The filler block of an alignment entry. -/
  | filler
  /-- The entry's assertion pairs. -/
  | asserts
  deriving Repr, Inhabited

/-- **Why a node, an entry or a circuit's header is rejected.** -/
inductive TReason where
  /-- A node kind the check does not accept (a staged operator outside its rule). -/
  | kind
  /-- A wire or aux list of the wrong length. -/
  | length
  /-- A kid not below the node, or too short. -/
  | kid
  /-- A constant that is not one of the circuit's field. -/
  | constant
  /-- An index map out of range. -/
  | index
  /-- Operator rows reading past the operand. -/
  | rows
  /-- An input block that is not the value's. -/
  | block
  /-- A late value's message or pad block. -/
  | late
  /-- A value read through its definition. -/
  | defined
  /-- A chain's leaves. -/
  | chain
  /-- The entry's root or assertion pairs. -/
  | root
  /-- The entry's meaning. -/
  | meaning
  /-- The blocks of the entries. -/
  | partition
  /-- The circuit's header. -/
  | header
  /-- A family record's guard. -/
  | family (r : FamReason)
  /-- The relational check. -/
  | rel (f : GKR.Rel.Failure)
  deriving Repr, Inhabited

/-- **A failure**: the entry, the node (or item), and the reason. -/
structure CertFailure where
  /-- The entry. -/
  entry : ℕ
  /-- The node or item. -/
  node : ℕ
  /-- The reason. -/
  reason : TReason
  deriving Repr, Inhabited

/-- **A wire as a tree expression.** -/
def teW (W : Wire) : TE := .wire W.c0 W.c1 W.n

/-- **A balanced sum** of tree expressions, `f` levels: the lower half has `⌊n / 2⌋` terms; the
constant `0` for none (and out of fuel). The balanced shape keeps a long sum's normal form shallow. -/
def TE.sumB : ℕ → List TE → TE
  | _, [] => .const 0
  | _, [e] => e
  | 0, _ :: _ :: _ => .const 0
  | f + 1, e :: e' :: es =>
    .add (TE.sumB f ((e :: e' :: es).take ((es.length + 2) / 2)))
      (TE.sumB f ((e :: e' :: es).drop ((es.length + 2) / 2)))

/-- **The sum** of tree expressions (balanced); the constant `0` for none. -/
def TE.sumL (es : List TE) : TE := TE.sumB es.length es

/-- **A row of codes over the coordinates `x`**: the sum of `code · x col`. -/
def rowTE (x : ℕ → TE) (row : List (ℕ × ℕ)) : TE :=
  TE.sumL (row.map fun t => cond (Nat.beq t.2 1) (x t.1) (.scale t.2 (x t.1)))

/-- **Every column of the rows is below `L`.** -/
def rowsInB (L : ℕ) (rows : List (List (ℕ × ℕ))) : Bool :=
  rows.all fun r => r.all fun t => Nat.blt t.1 L

/-- **`n` consecutive slices of width `w`**. -/
def slices {α : Type} (w : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | n + 1, l => l.take w :: slices w n (l.drop w)

/-- **The cuts of a node's coordinates**: its wires against the tree expressions. -/
def zipCuts (ws : List Wire) (es : List TE) : List (Wire × TE) := List.zip ws es

/-- **The codes `es` padded with `0` (or cut) to length `n`**, read by a trie: one pass, where a
per-coordinate `getD` would be quadratic. -/
def padTo (n : ℕ) (es : List ℕ) : List ℕ := (es ++ List.replicate (n - es.length) 0).take n

/-- A test inside the twin. -/
def chk (b : Bool) (r : TReason) : Except TReason Unit := cond b (.ok ()) (.error r)

section Cuts

variable (ir : RealizedProgram) (c : ℕ) (env : TEnv) (E : ETable)

/-- **Cuts**: wires against tree expressions. -/
abbrev Cuts := List (Wire × TE)

/-- **The first `n` tree expressions of kid `a` of node `k`**, with the cuts they need: `a` below
`k`, of length at least `n`; a cut kid gives its wires, an uncut kid its expansion `rec a`
(its one-level form over its own kids, with its aux cuts). -/
def kidTEF (rec : ℕ → Except TReason (List TE × Cuts)) (k a n : ℕ) :
    Except TReason (List TE × Cuts) :=
  cond (Nat.blt a k && Nat.ble n (E.get a).len)
    (cond (E.get a).cut (.ok (takeL n (E.get a).len ((E.get a).wires.map teW), []))
      (do
        let r ← rec a
        .ok (takeL n (E.get a).len r.1, r.2)))
    (.error .kid)

/-- **An operator on the coordinates `xs`** (as tree expressions): a view reads them by its index
map, the printed zero past them a constant `0`; a named operator and a sparse matrix are their rows
of codes, per block of the operator's columns; a staged operator is not accepted here. -/
def opTE : EOp → List TE → Except TReason (List TE)
  | .view idx zero, xs =>
    let L := xs.length
    let T := Trie.ofList xs
    match zero with
    | none =>
      cond (idx.inRange L) (.ok (pickL xs idx)) (.error .index)
    | some z =>
      cond (idx.inRange (L + 1) && zeroConstB ir z && Nat.beq (ir.valueField z) (ir.circField c))
        (.ok (idx.toList.map fun e => cond (Nat.blt e L) (T.get e) (.const 0))) (.error .index)
  | .named op, xs =>
    match emitRows ir env c op with
    | none => .error .kind
    | some rows =>
      let L := xs.length
      let C := NamedOp.cols ir op
      let rs := shiftRows C (L / C) rows
      cond (Nat.blt 0 C && Nat.beq (L % C) 0 && rowsInB L rs)
        (.ok (rs.map (rowTE (Trie.ofList xs).get))) (.error .rows)
  | .sparse rows, xs =>
    match rows.mapM fun r => r.mapM fun t => (coefCode ir c t.2).map fun a => (t.1, a) with
    | none => .error .constant
    | some rs =>
      cond (rowsInB xs.length rs) (.ok (rs.map (rowTE (Trie.ofList xs).get))) (.error .rows)
  | .staged _ _, _ => .error .kind

/-- **The operators of a term, first to last.** -/
def opsTE : List EOp → List TE → Except TReason (List TE)
  | [], xs => .ok xs
  | op :: ops, xs => do
    let ys ← opTE ir c env op xs
    opsTE ops ys

/-- **A term of a `lin` node of length `n`**: its view's tree expressions through its operators,
scaled; `kid a n` reads a kid. -/
def termTE (kid : ℕ → ℕ → Except TReason (List TE × Cuts)) (n : ℕ) (t : ETerm) :
    Except TReason (List TE × Cuts) := do
  let r ← kid t.view (E.get t.view).len
  let ys ← opsTE ir c env t.ops r.1
  chk (Nat.beq ys.length n) .length
  .ok (cond (Nat.beq t.scale 1) ys (ys.map (.scale t.scale)), r.2)

/-- **The terms of a `lin` node**, summed coordinatewise onto `acc`. -/
def termsTE (kid : ℕ → ℕ → Except TReason (List TE × Cuts)) (n : ℕ) :
    List ETerm → List TE → Except TReason (List TE × Cuts)
  | [], acc => .ok (acc, [])
  | t :: ts, acc => do
    let r ← termTE ir c env E kid n t
    let q ← termsTE kid n ts (List.zipWith .add acc r.1)
    .ok (q.1, r.2 ++ q.2)

/-- **A value's definition**: a bound value's expression, a public expression's expression. -/
def valueDef (u : ℕ) : Option Expr :=
  match (ir.value u).kind with
  | .bound e => some e
  | .pub (.expr e) => some e
  | _ => none

/-- **The constant `v`'s codes**, `v` a constant of the circuit's field. -/
def constE (v : ℕ) : Except TReason (List ℕ) :=
  match constCodes? ir c v with
  | some es => .ok es
  | none => .error .constant

/-- **The negation `1 − x` of a Logic bit's wire** (`Logic::lnot`, no call). -/
def lnotW (W : Wire) : Wire :=
  ⟨env.ar.add 1 (cmul env.ar env.neg1 W.c0), cmul env.ar env.neg1 W.c1, W.n⟩

/-- **The negation `1 − x` of a tree expression**: a wire's as a wire (`lnotW`), a constant's as a
constant, any other's as `1 + (−1)·x`. -/
def lnotT : TE → TE
  | .wire c0 c1 n => teW (lnotW env ⟨c0, c1, n⟩)
  | .const k => .const (env.ar.add 1 (cmul env.ar env.neg1 k))
  | e => .add (.const 1) (.scale env.neg1 e)

/-- **Whether input block `b` holds value `u` by `u`'s kind** (as the decoded valuation reads it):
a committed value or a pad copy its committed block, a bit view its view block, any value but a
late one its public block. -/
def kindBlockB (u : ℕ) (b : InputBlock) : Bool :=
  match (ir.value u).kind with
  | .priv => b.isCommittedOf u
  | .padCopy _ _ => b.isCommittedOf u
  | .late => false
  | .bits _ _ => b.isViewOf u
  | _ => b.isPubOf u

/-- **The cuts of value leaf `k`** (its placement): see the module docstring. -/
def placeCutsE (k : ℕ) : Except TReason (List (Wire × TE)) :=
  let nd := E.get k
  let ins := (ir.circuit c).inputs
  cond (!(Nat.beq nd.wires.length nd.len)) (.error .length) <|
  match nd.node with
  | .value u (.block b) =>
    let blk := ins.getD b default
    cond (Nat.blt b ins.length && ir.kindBlockB u blk &&
        (ins.take b).all (fun b' => !ir.kindBlockB u b') &&
        Nat.beq (ir.valueField u) (ir.circField c) && Nat.ble nd.len blk.len &&
        Nat.ble (blk.first + nd.len) env.inputs)
      (.ok (zipCuts nd.wires ((List.range nd.len).map fun i => .wire 0 1 (blk.first + i))))
      (.error .block)
  | .value u (.late pb pd) =>
    match ins.getD pb default, ins.getD pd default with
    | .pub m a n, .pad u' a' n' =>
      cond (Nat.blt pb ins.length && Nat.blt pd ins.length &&
          (match (ir.value u).kind with | .late => true | _ => false) &&
          (Nat.beq m u || (match (ir.value m).kind with | .message u'' => Nat.beq u'' u | _ => false)) &&
          Nat.beq u' u &&
          (ins.take pb).all (fun b' => !b'.isPubOf m) && (ins.take pd).all (fun b' => !b'.isPadOf u) &&
          Nat.beq (ir.valueField u) (ir.circField c) && Nat.ble nd.len n && Nat.ble nd.len n' &&
          Nat.ble (a + nd.len) env.inputs && Nat.ble (a' + nd.len) env.inputs)
        (.ok (zipCuts nd.wires ((List.range nd.len).map fun i =>
          .add (.wire 0 1 (a + i)) (.scale env.neg1 (.wire 0 1 (a' + i))))))
        (.error .late)
    | _, _ => .error .late
  | .value u (.defined y) =>
    match ir.valueDef u with
    | some e =>
      cond (Nat.blt y k && (E.get y).cut && E.eqB env y e &&
          Nat.beq (E.get y).wires.length (E.get y).len &&
          Nat.beq (E.get y).len nd.len && Nat.beq (ir.valueField u) (ir.circField c))
        (.ok (zipCuts nd.wires ((E.get y).wires.take nd.len |>.map teW)))
        (.error .defined)
    | none => .error .defined
  | _ => .error .kind

/-- **The leaves of a chain under kid `a`** (`chain_leaves`): through an uncut kid of the same
combine to its kids, `fuel` levels; any other kid is a leaf. -/
def leavesOf (op : BinOp) : ℕ → ℕ → List ℕ
  | 0, a => [a]
  | fuel + 1, a =>
    match (E.get a).node with
    | .bin op' a1 a2 =>
      cond (!(E.get a).cut && decide (op' = op)) (leavesOf op fuel a1 ++ leavesOf op fuel a2) [a]
    | _ => [a]

/-- **The combine of two tree expressions** (`BinOp.sem`'s printed forms). -/
def combTE (op : BinOp) (x y : TE) : TE :=
  match op with
  | .add => .add x y
  | .mul | .and => .mul x y
  | .or => .add (.add x y) (.scale env.neg1 (.mul x y))
  | .xor =>
    cond env.char2 (.add x y)
      (.add (.add x y) (.scale env.neg1 (.scale (env.ar.add 1 1) (.mul x y))))

/-- **A balanced combine tree over the tree expressions `ls`** (`ExprEmitter::tree`: the lower half
has `⌊n / 2⌋` leaves), its internal results the wires `aux` in post-order: the subtree's
expression, the aux left over, and the cuts of its internal results; `fuel` levels. -/
def chainTree (op : BinOp) : ℕ → List TE → List Wire → Option (TE × List Wire × Cuts)
  | _, [], _ => none
  | _, [x], aux => some (x, aux, [])
  | 0, _ :: _ :: _, _ => none
  | f + 1, x :: y :: zs, aux =>
    let h := (zs.length + 2) / 2
    match chainTree op f ((x :: y :: zs).take h) aux with
    | none => none
    | some (wl, aux1, c1) =>
      match chainTree op f ((x :: y :: zs).drop h) aux1 with
      | none => none
      | some (wr, aux2, c2) =>
        match aux2 with
        | [] => none
        | w :: aux3 => some (teW w, aux3, c1 ++ c2 ++ [(w, combTE env op wl wr)])

/-- **One coordinate of a chain root** over the leaves `ls` and its aux `aux`: the two halves'
trees, then the root's combine (its right-hand side) and the internal cuts; every aux consumed. -/
def chainRoot (op : BinOp) (ls : List TE) (aux : List Wire) : Option (TE × Cuts) :=
  match ls with
  | x :: y :: zs =>
    let h := (zs.length + 2) / 2
    match chainTree env op ls.length ((x :: y :: zs).take h) aux with
    | none => none
    | some (wl, aux1, c1) =>
      match chainTree env op ls.length ((x :: y :: zs).drop h) aux1 with
      | some (wr, [], c2) => some (combTE env op wl wr, c1 ++ c2)
      | _ => none
  | _ => none

/-- **The coordinates of the lists**, each of length `n`: list `i` holds coordinate `i` of every
list, in order. -/
def columnsW {α : Type} (n : ℕ) : List (List α) → List (List α)
  | [] => List.replicate n []
  | l :: ls => List.zipWith List.cons l (columnsW n ls)

/-- **A chain root `k`** (`bin op a b`): its leaves (through uncut same-combine kids), each a kid of
the node's length; two leaves are one combine per coordinate (`combTE`) with no aux; otherwise an
`add` (or a characteristic-two `xor`) is the sum of the leaves with no aux, and any other combine
the balanced tree with `m − 2` aux wires per coordinate. -/
def chainE (kid : ℕ → ℕ → Except TReason (List TE × Cuts)) (k : ℕ) (op : BinOp) (a b : ℕ) :
    Except TReason (List TE × Cuts) := do
  let nd := E.get k
  let ls := leavesOf E op k a ++ leavesOf E op k b
  let rs ← ls.mapM fun l => kid l nd.len
  match rs with
  | [r₁, r₂] => do
    -- two leaves: one combine per coordinate, no aux
    chk nd.aux.isEmpty .length
    .ok (List.zipWith (combTE env op) r₁.1 r₂.1, (rs.map Prod.snd).flatten)
  | _ => do
      let cols := columnsW nd.len (rs.map Prod.fst)
      let kax := (rs.map Prod.snd).flatten
      let sum := match op with
        | .add => true
        | .xor => env.char2
        | _ => false
      cond sum
        (do
          chk nd.aux.isEmpty .length
          .ok (cols.map TE.sumL, kax))
        (do
          let m := ls.length
          chk (Nat.blt 1 m && Nat.beq nd.aux.length (nd.len * (m - 2))) .length
          let per := slices (m - 2) nd.len nd.aux
          match (List.zipWith (chainRoot env op) cols per).mapM id with
          | some l => .ok (l.map Prod.fst, (l.map Prod.snd).flatten ++ kax)
          | none => .error .chain)

/-- **A kept result** (`ExprEmitter::keep`): where `b`, the next aux wire stands for `e` (a cut);
otherwise `e` itself. -/
def keepT (b : Bool) (e : TE) (aux : List Wire) : Option (TE × List Wire × Cuts) :=
  cond b
    (match aux with
     | w :: aux' => some (teW w, aux', [(w, e)])
     | [] => none)
    (some (e, aux, []))

/-- **One level of a balanced product** (`ExprEmitter::product`): neighbours paired, each product
an aux wire, an odd last factor carried. -/
def prodLevel : List TE → List Wire → Option (List TE × List Wire × Cuts)
  | x :: y :: rest, w :: aux =>
    match prodLevel rest aux with
    | some (l, aux', cs) => some (teW w :: l, aux', (w, .mul x y) :: cs)
    | none => none
  | _ :: _ :: _, [] => none
  | l, aux => some (l, aux, [])

/-- **A balanced product** (`ExprEmitter::product`), level by level, every product but the root an
aux wire: the root's expression, the aux left over and the cuts; `fuel` levels. -/
def prodTree : ℕ → List TE → List Wire → Option (TE × List Wire × Cuts)
  | _, [], aux => some (.const 1, aux, [])
  | _, [x], aux => some (x, aux, [])
  | _, [x, y], aux => some (.mul x y, aux, [])
  | 0, _ :: _ :: _ :: _, _ => none
  | f + 1, x :: y :: z :: l, aux =>
    match prodLevel (x :: y :: z :: l) aux with
    | none => none
    | some (l', aux1, c1) =>
      match prodTree f l' aux1 with
      | none => none
      | some (r, aux2, c2) => some (r, aux2, c1 ++ c2)

/-- **A balanced tree** (`ExprEmitter::range_tree`) of `comb` over `a i0, …, a (i0 + n − 1)`, the
lower half `⌊n / 2⌋` leaves, every combination but the root's an aux wire; `unit` for none;
`fuel` levels. -/
def balTree (comb : TE → TE → TE) (unit : TE) (a : ℕ → TE) :
    ℕ → ℕ → ℕ → Bool → List Wire → Option (TE × List Wire × Cuts)
  | 0, _, _, _, _ => none
  | _ + 1, 0, _, _, aux => some (unit, aux, [])
  | _ + 1, 1, i0, _, aux => some (a i0, aux, [])
  | f + 1, n + 2, i0, root, aux =>
    match balTree comb unit a f ((n + 2) / 2) i0 false aux with
    | none => none
    | some (lo, aux1, c1) =>
      match balTree comb unit a f (n + 2 - (n + 2) / 2) (i0 + (n + 2) / 2) false aux1 with
      | none => none
      | some (hi, aux2, c2) =>
        match keepT (!root) (comb lo hi) aux2 with
        | none => none
        | some (r, aux3, c3) => some (r, aux3, c1 ++ c2 ++ c3)

/-- **`Logic::lxor`** of two tree expressions. -/
def lxorT (x y : TE) : TE := combTE env .xor x y

/-- **`Logic::lor`** of two tree expressions: `¬(¬x ∧ ¬y)`. -/
def lorT (x y : TE) : TE := lnotT env (.mul (lnotT env x) (lnotT env y))

/-- **`eq_reduce`** (`ExprEmitter::eq_reduce`) on the bits `[i0, i0 + n)` of `a` and `b`: one bit's
`¬lxor`, the product of the halves above; every non-root result an aux wire; `fuel` levels. -/
def eqTree (a b : ℕ → TE) : ℕ → ℕ → ℕ → Bool → List Wire → Option (TE × List Wire × Cuts)
  | 0, _, _, _, _ => none
  | _ + 1, 0, _, _, aux => some (.const 1, aux, [])
  | _ + 1, 1, i0, root, aux => keepT (!root) (lnotT env (lxorT env (a i0) (b i0))) aux
  | f + 1, n + 2, i0, root, aux =>
    match eqTree a b f ((n + 2) / 2) i0 false aux with
    | none => none
    | some (lo, aux1, c1) =>
      match eqTree a b f (n + 2 - (n + 2) / 2) (i0 + (n + 2) / 2) false aux1 with
      | none => none
      | some (hi, aux2, c2) =>
        match keepT (!root) (.mul lo hi) aux2 with
        | none => none
        | some (r, aux3, c3) => some (r, aux3, c1 ++ c2 ++ c3)

/-- **`lt_reduce`** (`ExprEmitter::lt_reduce`) on the bits `[i0, i0 + n)` of `a` and `b`: the
pair `(eq, lt)`; one bit's `(¬lxor, ¬a ∧ b)`, above it `(eq_hi · eq_lo, lt_hi + eq_hi · lt_lo)`;
every non-root call's `eq`, and a lower half's `lt`, an aux wire; `fuel` levels. -/
def ltTree (a b : ℕ → TE) :
    ℕ → ℕ → ℕ → Bool → Bool → List Wire → Option ((TE × TE) × List Wire × Cuts)
  | 0, _, _, _, _, _ => none
  | _ + 1, 0, _, _, _, aux => some ((.const 1, .const 0), aux, [])
  | _ + 1, 1, i0, root, lower, aux =>
    match keepT (!root) (lnotT env (lxorT env (a i0) (b i0))) aux with
    | none => none
    | some (eq, aux1, c1) =>
      match keepT (!root && lower) (.mul (lnotT env (a i0)) (b i0)) aux1 with
      | none => none
      | some (lt, aux2, c2) => some ((eq, lt), aux2, c1 ++ c2)
  | f + 1, n + 2, i0, root, lower, aux =>
    match ltTree a b f ((n + 2) / 2) i0 false true aux with
    | none => none
    | some (lo, aux1, c1) =>
      match ltTree a b f (n + 2 - (n + 2) / 2) (i0 + (n + 2) / 2) false false aux1 with
      | none => none
      | some (hi, aux2, c2) =>
        match keepT (!root) (.mul hi.1 lo.1) aux2 with
        | none => none
        | some (eq, aux3, c3) =>
          match keepT (!root && lower) (.add hi.2 (.mul hi.1 lo.2)) aux3 with
          | none => none
          | some (lt, aux4, c4) => some ((eq, lt), aux4, c1 ++ c2 ++ c3 ++ c4)

/-- **A comparison of `w`-bit words** (`ExprEmitter`'s `kLt kLeq kEq`): `a < b` is `lt_reduce`'s
`lt`, `a ≤ b` is `¬(b < a)`, `a = b` is `eq_reduce`. -/
def cmpTree (op : CmpOp) (w : ℕ) (a b : ℕ → TE) (aux : List Wire) :
    Option (TE × List Wire × Cuts) :=
  match op with
  | .lt => (ltTree env a b (w + 1) w 0 true false aux).map fun r => (r.1.2, r.2.1, r.2.2)
  | .leq => (ltTree env b a (w + 1) w 0 true false aux).map fun r => (lnotT env r.1.2, r.2.1, r.2.2)
  | .eq => eqTree env a b (w + 1) w 0 true aux

/-- **Per coordinate** `j` of the list, `f j` from the aux left over by the earlier coordinates. -/
def auxCoords (f : ℕ → List Wire → Option (TE × List Wire × Cuts)) :
    List ℕ → List Wire → Option (List TE × List Wire × Cuts)
  | [], aux => some ([], aux, [])
  | j :: js, aux =>
    match f j aux with
    | none => none
    | some (t, aux1, c1) =>
      match auxCoords f js aux1 with
      | none => none
      | some (ts, aux2, c2) => some (t :: ts, aux2, c1 ++ c2)

/-- **The coordinates of a node of length `n` from its per-coordinate rule**, every aux wire
consumed. -/
def auxAll (f : ℕ → List Wire → Option (TE × List Wire × Cuts)) (n : ℕ) (aux : List Wire) :
    Except TReason (List TE × Cuts) :=
  match auxCoords f (List.range n) aux with
  | some (ts, [], cs) => .ok (ts, cs)
  | _ => .error .chain

/-- **The core of a staged operator**: `ntt n ψ o` under `batched b` (`b ≥ 1`) at any depth, as
`(n, ψ, o, N)`, `N` the operator's block width (`NamedOp.cols`, `(Πb)·n`). -/
def stagedCore? : NamedOp → Option (ℕ × ℕ × NttOrder × ℕ)
  | .ntt n psi o => some (n, psi, o, n)
  | .batched (b + 1) op =>
    match stagedCore? op with
    | some (n, psi, o, w) => some (n, psi, o, (b + 1) * w)
    | none => none
  | _ => none

/-- **A staged transform** (`.staged`, either order, plain or batched) and its core
(`stagedCore?`); its stage mask names the `share` boundaries, while its aux holds the working
array after every stage but the last whatever the mask (`expr.h`). -/
def staged? : EOp → Option (ℕ × ℕ × NttOrder × ℕ)
  | .staged op _ => stagedCore? op
  | _ => none

/-- **One butterfly stage** of half-size `h` on the `n` tree expressions `arr`, the twiddle code
`tw q` at the upper position `q` of each pair: in each block of `2h`, positions `q` and `q + h`
become `u + w·v` and `u − w·v`, `u, v` the positions `q, q + h`, `w = tw q` (`bflyF`). -/
def bflyT (n h : ℕ) (tw : ℕ → ℕ) (arr : List TE) : List TE :=
  let T := Trie.ofList arr
  (List.range n).map fun p =>
    cond (Nat.blt (p % (2 * h)) h)
      (.add (T.get p) (.scale (tw p) (T.get (p + h))))
      (.add (T.get (p - h)) (.scale env.neg1 (.scale (tw (p - h)) (T.get p))))

/-- **The stages of a schedule** (`stagesF`) from stage `s`, `r` left, stage `s` of half-size
`(sched s).1` and twiddle codes `(sched s).2`; after every stage but the last, the next `n` aux
wires stand for the working array in position order (cuts). -/
def stagesT (n : ℕ) (sched : ℕ → ℕ × (ℕ → ℕ)) :
    ℕ → ℕ → List TE → List Wire → Option (List TE × List Wire × Cuts)
  | 0, _, arr, aux => some (arr, aux, [])
  | r + 1, s, arr, aux =>
    let arr' := bflyT env n (sched s).1 (sched s).2 arr
    match r with
    | 0 => some (arr', aux, [])
    | r' + 1 =>
      cond (Nat.ble n aux.length)
        (match stagesT n sched (r' + 1) (s + 1) ((aux.take n).map teW) (aux.drop n) with
         | some (out, aux', cs) => some (out, aux', zipCuts (aux.take n) arr' ++ cs)
         | none => none)
        none

/-- **The schedule of a staged transform** of length `n = 2^L` in order `o` (`nttSchedF`), its
twiddle codes read from the table `Tw` of `ψ^0, …, ψ^(n−1)`. -/
def nttSchedT (n L : ℕ) (Tw : Trie ℕ) (o : NttOrder) (s : ℕ) : ℕ × (ℕ → ℕ) :=
  (nttHalf L o s, fun q => Tw.get (nttTwIdx n L o s q))

/-- **The input of a staged transform** (`nttInF`) from the operand's trie `Tx`: natural order
twists by `ψ^i` and reverses the bits (`ntt_gadget::transform`); scheme order reads the
coefficients as they are. -/
def nttInT (n L : ℕ) (Tw : Trie ℕ) (Tx : Trie TE) : NttOrder → List TE
  | .natural =>
    (List.range n).map fun p => .scale (Tw.get (bitRevNat L p)) (Tx.get (bitRevNat L p))
  | .scheme => (List.range n).map Tx.get

/-- **One block of a staged transform** of length `n = 2^L` at `ψ` in order `o`: its input, its
`L` stages. -/
def nttBlockT (n L psi : ℕ) (o : NttOrder) (xs : List TE) (aux : List Wire) :
    Option (List TE × List Wire × Cuts) :=
  let Tw := Trie.ofList (powList env.ar psi n 1)
  stagesT env n (nttSchedT n L Tw o) L 0 (nttInT n L Tw (Trie.ofList xs) o) aux

/-- **`k` blocks of a staged transform** (`expand_operator`), block-major aux. -/
def nttBlocksT (n L psi : ℕ) (o : NttOrder) :
    ℕ → List TE → List Wire → Option (List TE × List Wire × Cuts)
  | 0, _, aux => some ([], aux, [])
  | k + 1, xs, aux =>
    match nttBlockT env n L psi o (xs.take n) aux with
    | none => none
    | some (o', aux1, c1) =>
      match nttBlocksT n L psi o k (xs.drop n) aux1 with
      | none => none
      | some (os, aux2, c2) => some (o' ++ os, aux2, c1 ++ c2)

/-- **The one-level form of node `k`** by its kind, over its kids' tree expressions (`kid a n`),
with the cuts it needs (its aux cuts and its uncut kids'). -/
def nodeStep (kid : ℕ → ℕ → Except TReason (List TE × Cuts)) (k : ℕ) :
    Except TReason (List TE × Cuts) := do
  let nd := E.get k
  let n := nd.len
  let noAux := chk nd.aux.isEmpty .length
  match nd.node with
  | .bin op a b => chainE env E kid k op a b
  | .lin [] z => do
    noAux
    chk (zeroConstB ir z && Nat.beq (ir.valueField z) (ir.circField c)) .constant
    .ok (List.replicate n (.const 0), [])
  | .lin (t :: ts) _ => do
    noAux
    let r ← termTE ir c env E kid n t
    let q ← termsTE ir c env E kid n ts r.1
    .ok (q.1, r.2 ++ q.2)
  | .const v => do
    noAux
    let es ← constE ir c v
    .ok ((padTo n es).map .const, [])
  | .scale s a => do
    noAux
    let r ← kid a n
    .ok (r.1.map (.scale s), r.2)
  | .sum w a => do
    noAux
    let r ← kid a (n * w)
    .ok ((slices w n r.1).map TE.sumL, r.2)
  | .broadcast idx a => do
    noAux
    let r ← kid a (E.get a).len
    chk (idx.inRange r.1.length) .index
    .ok (pickL r.1 idx, r.2)
  | .lnot o a => do
    noAux
    let es ← constE ir c o
    let r ← kid a n
    .ok ((padTo n es).zipWith (fun e x => .add (.const e) (.scale env.neg1 x)) r.1, r.2)
  | .mux false cc t e => do
    let rc ← kid cc n
    let rt ← kid t n
    let re ← kid e n
    chk (Nat.beq nd.aux.length n) .length
    .ok (List.zipWith (fun d (p : TE × TE) => .add p.2 (.mul p.1 (teW d))) nd.aux (rc.1.zip re.1),
      List.zipWith (fun d (p : TE × TE) => (d, .add p.1 (.scale env.neg1 p.2))) nd.aux
        (rt.1.zip re.1) ++ rc.2 ++ rt.2 ++ re.2)
  | .mux true cc t e => do
    noAux
    let rc ← kid cc n
    let rt ← kid t n
    let re ← kid e n
    .ok (List.zipWith (fun x (p : TE × TE) => .add (.mul x p.1) (.mul (lnotT env x) p.2)) rc.1
      (rt.1.zip re.1), rc.2 ++ rt.2 ++ re.2)
  | .materialize a => do
    noAux
    kid a n
  | .gather idx ps => do
    noAux
    chk (!ps.isEmpty) .kid
    let rs ← ps.mapM fun p => kid p (E.get p).len
    let xs := flattenL (rs.map Prod.fst)
    chk (idx.inRange xs.length) .index
    .ok (pickL xs idx, (rs.map Prod.snd).flatten)
  | .apply op a =>
    match staged? op with
    | some (nn, psi, o, w) => do
      let r ← kid a (E.get a).len
      chk (Nat.ble 2 nn && Nat.beq (2 ^ Nat.log2 nn) nn && Nat.beq (r.1.length % w) 0 &&
        Nat.beq (env.ar.add (codePow env.ar psi nn) 1) 0) .rows
      match nttBlocksT env nn (Nat.log2 nn) psi o (r.1.length / nn) r.1 nd.aux with
      | some (out, [], cs) => .ok (out, cs ++ r.2)
      | _ => .error .chain
    | none => do
      noAux
      let r ← kid a (E.get a).len
      let ys ← opTE ir c env op r.1
      .ok (ys, r.2)
  | .prod w a => do
    let r ← kid a (n * w)
    let T := Trie.ofList r.1
    let q ← auxAll (fun j aux => prodTree (w + 1) ((List.range w).map fun t => T.get (j * w + t))
      aux) n nd.aux
    .ok (q.1, q.2 ++ r.2)
  | .tree any w a => do
    let r ← kid a (n * w)
    let T := Trie.ofList r.1
    let q ← auxAll (fun j aux => balTree (cond any (lorT env) .mul) (.const (cond any 0 1))
      (fun t => T.get (j * w + t)) (w + 1) w 0 true aux) n nd.aux
    .ok (q.1, q.2 ++ r.2)
  | .cmp op w a b => do
    let r ← kid a (n * w)
    let Ta := Trie.ofList r.1
    let rb ← (match b with
      | .node b' => kid b' (n * w)
      | .imm v idx => do
        let es ← constE ir c v
        .ok ((List.range (n * w)).map fun i => .const (es.getD (idx.entry i) 0), []))
    let Tb := Trie.ofList rb.1
    let q ← auxAll (fun j aux => cmpTree env op w (fun t => Ta.get (j * w + t))
      (fun t => Tb.get (j * w + t)) aux) n nd.aux
    .ok (q.1, q.2 ++ r.2 ++ rb.2)
  | _ => .error .kind

/-- **The expansion of node `k`** with `fuel` levels: its one-level form (`nodeStep`), each uncut
kid expanded in turn, of the node's length. -/
def nodeEF : ℕ → ℕ → Except TReason (List TE × Cuts)
  | 0, _ => .error .kid
  | f + 1, k => do
    let r ← nodeStep ir c env E (kidTEF E (nodeEF f) k) k
    chk (Nat.beq r.1.length (E.get k).len) .length
    .ok r

/-- **The cuts of node `k`**: a value leaf's placement (it must be cut); any other cut node's wires
(as many as its length) against its expansion, with the cuts the expansion needs; an uncut node
none (its parents expand it). -/
def nodeCutsE (k : ℕ) : Except TReason (List (Wire × TE)) := do
  let nd := E.get k
  match nd.node with
  | .value _ _ =>
    chk (nd.cut && Nat.beq nd.wires.length nd.len && nd.aux.isEmpty) .length
    ir.placeCutsE c env E k
  | _ =>
    cond nd.cut
      (do
        chk (Nat.beq nd.wires.length nd.len) .length
        let r ← nodeEF ir c env E (k + 1) k
        .ok (zipCuts nd.wires r.1 ++ r.2))
      (.ok [])

end Cuts

end GordieHowe.RealizedProgram
