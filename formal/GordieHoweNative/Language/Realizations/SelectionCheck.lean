-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Library.Table
public import GordieHoweNative.Language.RealizedProgram.Shapes

/-!
# GordieHowe: the compiled check of a program's table selections

The check the selections' soundness (`GordieHowe.RealizedProgram.SelSound`) and the frontends'
table selections (`GordieHowe.RealizedProgram.TableSelect`) read, in the Mathlib-free library
`GordieHoweNative`. The compiler emits one certificate per `select_row`
(`lib/gordiehowe/lib/table.h`): the selection's fingerprint predicate and the gadget's identifiers
(`SelCert`). The check confirms

* each certificate's gadget facts (`TableShape.selectB`: the facts `TableSelect` states), and
* for every selection a product form's kernel reads (`kernelSel?`), a certificate whose gadget is
  that selection (`selLinkB`): its predicate is the selection's, its record's cells are the
  kernel values' cells (`leafRun?`), its row map's leaves at the kernel blocks are the kernel's
  transform (`leafAt?`), its first column block is the selection's table, and its degree is
  within the selection's exported degree.

A program without a product form needs no link. Their lemmas are in
`GordieHowe/Language/Realizations/SelectionCheck.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **A table-selection certificate** (`select_row`): predicate `q` is the fingerprint equation of
the gadget `table`. -/
structure SelCert where
  /-- The selection's fingerprint predicate. -/
  q : ℕ
  /-- The gadget's identifiers and row map. -/
  table : TableShape

/-- **The start of a run of `len` entries from entry `i` of an index map**, when they are
consecutive entries of one step-`1` run: its first entry. -/
def IndexMap.stepRun? : IndexMap → ℕ → ℕ → Option ℕ
  | [], _, _ => none
  | (s, d, c) :: rest, i, len =>
    if i < c then (if d = 1 ∧ i + len ≤ c then some (s + i) else none)
    else IndexMap.stepRun? rest (i - c) len

/-- **The levels of the record walker.** -/
abbrev leafFuel : ℕ := 64

section

variable (ir : RealizedProgram)

/-- **Cells `[start, start + len)` of an expression as cells of one value**, with `n` levels:
`some (v, i)` when they are cells `[i, i + len)` of `.leaf v`, through shared expressions,
concatenations and step-`1` runs of index maps. -/
def leafRun? : ℕ → Expr → ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _, _, _ => none
  | n + 1, E, start, len =>
    match E with
    | .leaf v => some (v, start)
    | .ref k => if k < ir.exprs.length then leafRun? n (ir.expr k) start len else none
    | .concat a b =>
      if start + len ≤ ir.exprLen a then leafRun? n a start len
      else if ir.exprLen a ≤ start then leafRun? n b (start - ir.exprLen a) len
      else none
    | .reindex m a =>
      match IndexMap.stepRun? m start len with
      | some s => leafRun? n a s len
      | none => none
    | _ => none

end

/-- **The leaf of a row map starting at cell `c`** (`none` unless a leaf starts there). -/
def leafAt? : List RowLeaf → ℕ → Option RowLeaf
  | [], _ => none
  | l :: ls, c => if c = 0 then some l else if l.n ≤ c then leafAt? ls (c - l.n) else none

section

variable (ir : RealizedProgram)

/-- **Every value a predicate reads is fixed when challenge `j` is drawn** (`ReadFixedAt`, through
the reads table, as `readsFixedB`, the table built once). -/
def predFixedB (j : ℕ) (b : PredBody) : Bool :=
  let reads := ir.readsT
  (ir.predNodes b).all fun v => (reads.getD v []).all fun rd => decide (ir.ReadFixedAt j rd)

namespace TableShape

variable (t : TableShape)

/-- **The gadget's facts** (the fields of `GordieHowe.RealizedProgram.TableSelect`): the matchers
(`okB`), the powers and the digests public expressions, the index bits' check, the selection's two
predicates source predicates, the constants `1` and `0`, `γ` its challenge of one full coordinate
in the domain's field, the values read in the domain's field and of their sizes, the index bits
committed, the record reading only committed values and constants, the rows only the statement. -/
def selectB : Bool :=
  t.okB ir && decide (0 < ir.exprs.length) && decide (0 < ir.values.length) &&
    (ir.value t.pow).kind.isExprB && (ir.value t.dig).kind.isExprB &&
    (ir.predicate t.idxPred).body.isEqualB t.dom (.mul (.leaf t.idx) (.leaf t.idx)) (.leaf t.idx) &&
    [t.pred, t.idxPred].all (fun p => decide (p < ir.predicates.length) &&
      ir.inSource (ir.predicate p)) &&
    ir.isConstant t.one && (ir.constEntries t.one).getD 0 0 == 1 &&
    ir.isConstant t.zero && (ir.constEntries t.zero).getD 0 0 == 0 &&
    (ir.value t.gamma).kind.isChallengeB t.chal &&
    (ir.challenge t.chal).size == 1 && (ir.challenge t.chal).isFullB &&
    ir.chalField t.chal == ir.domainField t.dom &&
    (([t.one, t.zero, t.gamma, t.pow, t.dig, t.idx] ++ t.parts.map (·.1)).all fun v =>
      ir.valueField v == ir.domainField t.dom) &&
    (ir.value t.one).size == 1 && (ir.value t.gamma).size == 1 &&
    (ir.value t.idx).size == t.bits && (ir.value t.dig).size == 2 ^ t.bits &&
    (ir.value t.pow).size == (powerExps t.map).length &&
    (ir.value t.idx).kind.isPrivB &&
    (ir.exprNodes t.record).all (fun v => (ir.nodeReads ir.fuel v).isEmpty) &&
    t.parts.all (fun p => (ir.nodeReads ir.values.length p.1).isEmpty)

end TableShape

/-- **Record `i`'s cells and blocks are the gadget's** (`selLinkB`): its cells are the record's
cells from its first block on, and the row map has, at each of its blocks, a leaf of the
selection's transform. -/
def recordLinkB (sh : SelShape) (t : TableShape) (i : ℕ) : Bool :=
  let v := sh.records.getD i 0
  let s := ir.blockStart sh i
  ir.leafRun? leafFuel t.record (s * sh.n) (ir.value v).size == some (v, 0) &&
    (List.range (ir.recBlocks sh v)).all fun b =>
      match leafAt? t.map ((s + b) * sh.n) with
      | some l => l.ntt && l.n == sh.n && l.psi == sh.psi && l.natural == sh.natural
      | none => false

/-- **The gadget `t` is the selection `sh` of predicate `q`**: the same predicate, domain,
challenge and rows; its two predicates equalities read only what is fixed at the challenge; the
table its first column block, an opaque statement value; its record and row map the selection's
records and transforms (`recordLinkB`); its degree `W − 1` within the selection's; and its `−1` the
field's. -/
def selLinkB (q : ℕ) (sh : SelShape) (t : TableShape) : Bool :=
  t.pred == q && t.dom == sh.domain && t.chal == sh.chal && t.rows == sh.rows &&
    [t.pred, t.idxPred].all (fun p => decide (p < ir.predicates.length) &&
      (ir.predicate p).body.isEqual && ir.predFixedB sh.chal (ir.predicate p).body) &&
    t.parts.head? == some (sh.table, sh.width) &&
    (match (ir.value sh.table).kind with
      | .pub (.opaque _ []) => true
      | _ => false) &&
    (List.range sh.records.length).all (ir.recordLinkB sh t) &&
    decide (mapWidth t.map - 1 ≤ sh.deg) &&
    decide (t.dom < ir.domains.length) &&
    decide (2 ≤ (ir.field (ir.domainField t.dom)).characteristic) &&
    t.mOne + 1 == (ir.field (ir.domainField t.dom)).characteristic

/-- **The program's table selections**: every certificate's gadget facts hold, and every
selection a product form's kernel reads has a certificate linked to it (none is needed without a
product form). -/
def selectionsB (cs : List SelCert) : Bool :=
  cs.all (fun c => c.table.selectB ir) &&
    (ir.predicates.all (fun p => !p.body.isProductMod) ||
      (List.range ir.predicates.length).all fun q =>
        match ir.kernelSel? q with
        | none => true
        | some sh => cs.any fun c => c.q == q && ir.selLinkB q sh c.table)

end

end GordieHowe.RealizedProgram
