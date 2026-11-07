-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.CellsReader
public import GordieHoweNative.Language.PackingDesc
public import GordieHoweNative.Language.TableauNums
public import GordieHoweNative.ProofSystem.Program.FieldTree
public import GordieHoweNative.ProofSystem.Program.FieldDomain

/-!
# GordieHowe: the numbers of a domain's forked proof

The size bounds of a domain's forked proof (`RealizedProgram.FitsOk`, `ForkSizesLe`,
`ForkLoadNumbers`, `ForkRestNumbers`, Mathlib-side) read the ready data only through numbers:
the covered batches (which batches, their rounds, degree, width, operands and product cells), the
plan's edges with their kits' mask cells, the cells at no node, the rows and quadratic triples, the
circuits' widths and layers, and the tableau's numbers. Here they are computed from the program, the
plan, the field's packing descriptor (`PackingDesc`, the kits' mask cells at its `masks` queries)
and the tableau's numbers (`TableauNums`), at a cells reader (`CellsReader`): compiled code runs
them at the context built once. The equalities with the Mathlib-side numbers are in
`GordieHowe/ProofSystem/Program/ForkNums.lean`.
-/

public section

namespace GordieHowe.RealizedProgram

open Export

/-- Doubling `p = 2^k` until it reaches `n`, at most `fuel` times. -/
@[expose] def clog2.go (n p k : Nat) : Nat → Nat
  | 0 => k
  | fuel + 1 => if n ≤ p then k else go n (2 * p) (k + 1) fuel

/-- **The smallest `k` with `n ≤ 2^k`** (`Nat.clog 2 n`), by doubling. -/
@[expose] def clog2 (n : Nat) : Nat := clog2.go n 1 0 n

/-- Inserting `a` into a sorted list (`List.orderedInsert` at `≤`). -/
@[expose] def insN (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: insN a l

/-- **Sorting by insertion** (`List.insertionSort` at `≤`), structural: the kernel evaluates it,
where `List.mergeSort`'s well-founded recursion does not reduce. -/
@[expose] def sortN : List Nat → List Nat
  | [] => []
  | a :: l => insN a (sortN l)

/-- **The number of product cells of a shape** (`Shape.cellsL`) with the factors sorted by
insertion (`Shape.cellsK_eq`). -/
@[expose] def Shape.cellsK (sh : Shape) : Nat :=
  (insertAll [] (sh.monos.flatMap fun c =>
    (subListsN (sortN c.2)).filter fun s => decide (2 ≤ s.length))).length

namespace ForkReader

variable (ir : RealizedProgram) [r : CellsReader] (d : Nat)

/-! ## The covered batches -/

/-- **The covered batches of a kind**: the batches of domain `d` on the operand map `om`, merged
or not (every batch passes the batch check at its domain, `CellsValid`). -/
@[expose] def batchesOf (om : OperandMap) (merged : Bool) : List Nat :=
  (List.range ir.batches.length).filter fun b =>
    (ir.batch b).domain == d && (ir.batch b).operands == om && ir.merged b == merged

/-- **Batch `b`'s shape** (`relShape` at its operand map). -/
@[expose] def shapeOf (b : Nat) : Shape := ir.batchShape (CellsReader.formsOf ir d b) d b

/-- Batch `b`'s skip pads `(D − 1)(w − 1)`. -/
@[expose] def bE (b : Nat) : Nat := ((ir.batch b).degree - 1) * ((ir.batch b).width - 1)

/-- Batch `b`'s operands. -/
@[expose] def bK (b : Nat) : Nat := (shapeOf ir d b).k

/-- Batch `b`'s product cells. -/
@[expose] def bM (b : Nat) : Nat := (shapeOf ir d b).cellsK

/-- **Batch `b`'s pads**: skip pads, `n · D` round pads, the operands and the product cells. -/
@[expose] def bPads (b : Nat) : Nat :=
  bE ir b + (ir.batch b).rounds * (ir.batch b).degree + bK ir d b + bM ir d b

/-- The covered batches on columns, unmerged. -/
@[expose] def cbs : List Nat := batchesOf ir d .columns false
/-- The covered batches on bits, unmerged. -/
@[expose] def sbs : List Nat := batchesOf ir d .bits false
/-- The covered batches on columns, merged. -/
@[expose] def mbs : List Nat := batchesOf ir d .columns true
/-- The covered batches on bits, merged. -/
@[expose] def smbs : List Nat := batchesOf ir d .bits true

/-- The number of covered batches. -/
@[expose] def nBatches : Nat := (cbs ir d).length + (sbs ir d).length + ((mbs ir d).length + (smbs ir d).length)

/-! ## The edges and their mask cells -/

variable (P : Export.Plan) (D : PackingDesc)

/-- The plan's edges of domain `d`. -/
@[expose] def es : List PackingEdge := ir.planPacking P d

/-- The masks' prefix cells of every edge. -/
@[expose] def npN : Nat := ((es ir d P).map fun e => (D.maskNums e.childDegree e.degree e.mode).1).sum

/-- The masks' own cells of every edge. -/
@[expose] def ownN : Nat := ((es ir d P).map fun e => (D.maskNums e.childDegree e.degree e.mode).2).sum

/-! ## The cells and the tree -/

/-- `cellName`, at the reader. -/
@[expose] def cellName : CellKey → Option String
  | .val v _ => (r.value v).node.map (·.name)
  | .pad v _ =>
    match (r.value v).padSpace with
    | .full => none
    | .node s => some s
  | .filler _ _ => none

/-- `cellNode`, at the reader. -/
@[expose] def cellNode (es : List PackingEdge) (k : CellKey) : Option Nat := (cellName k).bind (nodeIdx es)

/-- `InputBlock.fillerKeys`. -/
@[expose] def fillerKeys (c : Nat) : InputBlock → List CellKey
  | .filler a n => (List.range n).map fun j => .filler c (a + j)
  | _ => []

/-- **A cell's bucket**: its node, `es.length` at no node. -/
@[expose] def bucketOf (es : List PackingEdge) (k : CellKey) : Nat := (cellNode es k).getD es.length

/-- **Each value's cells**: their bucket and number (every coordinate of a value has its node). -/
@[expose] def valueCells (es : List PackingEdge) : List (Nat × Nat) :=
  (List.range r.nValues).map fun v =>
    if CellsReader.isCellValue d v then (bucketOf es (.val v 0), (r.value v).size)
    else if CellsReader.isLateOf ir d v then (bucketOf es (.pad v 0), (r.value v).size)
    else (0, 0)

/-- The filler inputs of the domain's circuits (at no node). -/
@[expose] def fillerCount : Nat :=
  ((List.range ir.circuits.length).map fun c =>
    if (ir.circuit c).domain = d then ((ir.circuit c).inputs.map fun x => (fillerKeys c x).length).sum
    else 0).sum

/-- **The cells in bucket `a`.** -/
@[expose] def cellCount (es : List PackingEdge) (a : Nat) : Nat :=
  ((valueCells ir d es).map fun x => if x.1 = a then x.2 else 0).sum +
    if a = es.length then fillerCount ir d else 0

/-- **The cells at each node**: entry `a` the cells at the child of edge `a`, the last entry those
at no node (`own`, and the cells at the root). -/
@[expose] def nodeCounts (es : List PackingEdge) : List Nat :=
  (List.range (es.length + 1)).map (cellCount ir d es)

/-- `own`, at the counts: entry `a` below the last (the cells at no node). -/
@[expose] def ownC (c : List Nat) (a : Nat) : Nat := if a + 1 < c.length then c.getD a 0 else 0

/-- `isView`. -/
@[expose] def isView (es : List PackingEdge) (b : Nat) : Bool :=
  (es.getD b noEdge).childDegree == 1 && (es.getD b noEdge).degree == 16 &&
    (es.getD b noEdge).mode == .squaringChain && (parentIdx es b).isSome

/-- `viewChild`. -/
@[expose] def viewChild (es : List PackingEdge) (a : Nat) : Option Nat :=
  (List.range es.length).find? fun b => parentIdx es b == some a && isView es b

/-- `otherChild`. -/
@[expose] def otherChild (es : List PackingEdge) (a b : Nat) : Bool :=
  parentIdx es b == some a && viewChild es a != some b

/-- `given`, at the counts. -/
@[expose] def given (es : List PackingEdge) (c : List Nat) (a : Nat) : Nat :=
  match parentIdx es a with
  | some j => if viewChild es j = some a then ownC c j else 0
  | none => 0

/-- `ngFuel`, at the counts. -/
@[expose] def ngFuel (es : List PackingEdge) (c : List Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, a =>
    let dg := (es.getD a noEdge).degree
    let base := match viewChild es a with
      | some b => ngFuel es c f b
      | none => ownC c a
    let others := ((List.range a).filter (otherChild es a)).map (ngFuel es c f)
    (given es c a * dg + base + others.sum + dg - 1) / dg

/-- `nwOf`, at the counts: the groups of every edge at the root. -/
@[expose] def nwOf (es : List PackingEdge) (c : List Nat) : Nat :=
  (((List.range es.length).filter fun b' => (parentIdx es b').isNone).map
    fun a => ngFuel es c (a + 1) a).sum

/-! ## The rows and the quadratic triples -/

/-- `rowLhs`. -/
@[expose] def rowLhs (p : Nat) : Expr := (((r.predicate p).body.rowSides d).map (·.1)).getD default

/-- `rowRhs`. -/
@[expose] def rowRhs (p : Nat) : Expr := (((r.predicate p).body.rowSides d).map (·.2)).getD default

/-- `isRow`, at the reader. -/
@[expose] def isRow (p : Nat) : Bool :=
  match (r.predicate p).body.rowSides d with
  | some (e, e') => CellsReader.rowExprOk ir e && CellsReader.rowExprOk ir e'
  | none => false

/-- `isViewRow`, at the reader. -/
@[expose] def isViewRow (p : Nat) : Bool :=
  match (r.predicate p).body.rowSides d with
  | some (e, e') => !isRow ir d p && CellsReader.viewExprOk ir d e && CellsReader.viewExprOk ir d e'
  | none => false

/-- What value `u` reads of the committed assignment: the table's entry, `asgReads` past the
values. -/
@[expose] def asgReadsOf (u : Nat) : List Nat :=
  if u < r.nValues then r.asgReads u else ir.asgReads ir.fuel u

/-- Node `0` is the node of value `w`'s first cell or of its pad's (`valueNodes`). -/
@[expose] def atZero (es : List PackingEdge) (w : Nat) : Bool :=
  cellNode es (.val w 0) == some 0 || cellNode es (.pad w 0) == some 0

/-- **Row `p` reads node `0`** (`rowNodes`). -/
@[expose] def rowAtZero (es : List PackingEdge) (p : Nat) : Bool :=
  [rowLhs d p, rowRhs d p].any fun e =>
    (ir.exprNodes e).any fun u => (asgReadsOf ir u).any (atZero es)

/-- **View row `p` reads node `0`** (`viewRowNodes`). -/
@[expose] def viewRowAtZero (es : List PackingEdge) (p : Nat) : Bool :=
  (ir.exprNodes (rowLhs d p) ++ ir.exprNodes (rowRhs d p)).any fun u =>
    match (r.value u).kind with
    | .bits w _ => (cellNode es (.val w 0)).bind (viewChild es) == some 0
    | _ => (asgReadsOf ir u).any (atZero es)

/-- **Predicate `p`'s row coordinates** (`Row`, `ViewRow`): its left side's, for a row or a view
row. -/
@[expose] def rowLen (p : Nat) : Nat :=
  if isRow ir d p || isViewRow ir d p then r.exprLen (rowLhs d p) else 0

/-- **Predicate `p`'s row coordinates reading no node `0`.** -/
@[expose] def rowLenOff (es : List PackingEdge) (p : Nat) : Nat :=
  if isRow ir d p then (if rowAtZero ir d es p then 0 else r.exprLen (rowLhs d p))
  else if isViewRow ir d p then (if viewRowAtZero ir d es p then 0 else r.exprLen (rowLhs d p))
  else 0

/-- `quadLhs`, at the reader. -/
@[expose] def quadLhs (p : Nat) : Expr :=
  match (r.predicate p).body with
  | .equal _ e _ _ => e
  | _ => .leaf 0

/-- **The quadratic triples' coordinates** (`QuadIdx`). -/
@[expose] def quadCount : Nat :=
  ((List.range r.nPreds).map fun p =>
    if CellsReader.isQuad d p then r.exprLen (quadLhs p) else 0).sum

/-! ## The circuits -/

/-- The circuits of domain `d`. -/
@[expose] def circs : List Nat :=
  (List.range ir.circuits.length).filter fun c => (ir.circuit c).domain == d

/-- `circuitWidth`. -/
@[expose] def circW (c : Nat) : Nat := clog2 (max (ir.circuit c).wires (ir.circuit c).inputCount)

/-- The layers of circuit `c`. -/
@[expose] def circL (c : Nat) : Nat := (ir.circuit c).layers


/-! ## The domain's numbers and its size bounds -/

/-- **A covered batch's numbers.** -/
structure BatchNums where
  /-- It has a merging challenge. -/
  merged : Bool
  /-- It is on bits. -/
  bits : Bool
  /-- The sumcheck rounds. -/
  rounds : Nat
  /-- The degree. -/
  degree : Nat
  /-- The skip width. -/
  width : Nat
  /-- The parts. -/
  parts : Nat
  /-- The operands. -/
  k : Nat
  /-- The pads. -/
  pads : Nat
  /-- The product cells. -/
  cells : Nat
  /-- The skip pads. -/
  e : Nat

/-- **The elements of a covered batch's first challenge point**: the zerocheck point `ρ`, and the
merging challenge `γ` with it when the batch is merged. -/
@[expose] def BatchNums.firstReads (b : BatchNums) : Nat := bif b.merged then b.rounds + 1 else b.rounds

/-- **The numbers of domain `d`'s forked proof** that its size bounds read. -/
structure DomainNums where
  /-- Each covered batch. -/
  batches : List BatchNums
  /-- The edges' relative degrees. -/
  degrees : List Nat
  /-- The masks' prefix cells. -/
  np : Nat
  /-- The masks' own cells. -/
  nOwn : Nat
  /-- The groups at the root. -/
  nw : Nat
  /-- The cells at no node. -/
  root : Nat
  /-- The rows' coordinates. -/
  rows : Nat
  /-- The rows' coordinates reading no node `0`. -/
  rowsOff : Nat
  /-- The quadratic triples' coordinates. -/
  quads : Nat
  /-- Each circuit's width and layers. -/
  circuits : List (Nat × Nat)

/-- **The numbers of domain `d`** at the plan `P` and the packing descriptor `D`. -/
@[expose] def domainNums : DomainNums :=
  let es := es ir d P
  let c := nodeCounts ir d es
  let entry (merged bits : Bool) (b : Nat) : BatchNums :=
    ⟨merged, bits, (ir.batch b).rounds, (ir.batch b).degree, (ir.batch b).width,
      (ir.batch b).parts.length, bK ir d b, bPads ir d b, bM ir d b, bE ir b⟩
  { batches := (cbs ir d).map (entry false false) ++ (sbs ir d).map (entry false true) ++
      (mbs ir d).map (entry true false) ++ (smbs ir d).map (entry true true)
    degrees := es.map (·.degree)
    np := npN ir d P D
    nOwn := ownN ir d P D
    nw := nwOf es c
    root := c.getD es.length 0
    rows := ((List.range r.nPreds).map (rowLen ir d)).sum
    rowsOff := ((List.range r.nPreds).map (rowLenOff ir d es)).sum
    quads := quadCount d
    circuits := (circs ir d).map fun c => (circW ir c, circL ir c) }

end ForkReader

namespace ForkReader.DomainNums

variable (N : DomainNums) (t : TableauNums)

/-- The tableau's witness positions per row, `block − r`. -/
@[expose] def w : Nat := t.block - t.r

/-- The circuits' pad bounds, `layers · (4 · width + 3)`, summed. -/
@[expose] def gpSum : Nat := (N.circuits.map fun c => c.2 * (4 * c.1 + 3)).sum

/-- The circuits' tail bounds (their layers), summed. -/
@[expose] def gtSum : Nat := (N.circuits.map (·.2)).sum

/-- The covered batches' pads, with `8` more per batch on bits. -/
@[expose] def padsSum : Nat := (N.batches.map fun b => b.pads + if b.bits then 8 else 0).sum

/-- The covered batches' product cells. -/
@[expose] def cellsSum : Nat := (N.batches.map (·.cells)).sum

/-- `laterBound`: one claim per batch, one per circuit, the rows reading no node `0`, and
`d + 1` per edge. -/
@[expose] def later : Nat :=
  N.batches.length + N.circuits.length + N.rowsOff + (N.degrees.map (· + 1)).sum

/-- `claimCount`: one claim per batch, one per circuit, and the rows. -/
@[expose] def claims : Nat := N.batches.length + N.circuits.length + N.rows

/-- `forkQBound`. -/
@[expose] def qBound : Nat := N.cellsSum + N.gtSum + N.quads + N.nOwn

/-- `forkLinBound`. -/
@[expose] def linBound : Nat := N.batches.length + N.gtSum + N.later

/-- `forkRBound`. -/
@[expose] def rBound : Nat :=
  ((N.np + w t - 1) / w t * w t + N.nw + (1 + N.root + N.nOwn + (N.padsSum + N.gpSum)) + w t - 1) /
      w t +
    3 * ((N.qBound + w t - 1) / w t) + 6

/-- **`ForkSizesLe` on the numbers**: every batch's skip pads, degree and operands within `Mx`,
`2 ≤ Mx` with a batch on bits, every edge's relative degree within `Mx`. -/
@[expose] def sizesB (Mx : Nat) : Bool :=
  N.batches.all (fun b => decide (b.e ≤ Mx) && decide (b.degree ≤ Mx) &&
    decide (b.k ≤ Mx) && (!b.bits || decide (2 ≤ Mx))) &&
  N.degrees.all fun g => decide (g ≤ Mx)

/-- **`ForkRestNumbers` on the numbers.** -/
@[expose] def restB (Lmax : Nat) : Bool :=
  N.batches.all (fun b => decide (max (max b.firstReads b.k) 3 ≤ Lmax)) &&
  N.circuits.all (fun c => decide (max c.1 2 ≤ Lmax)) && decide (N.later ≤ Lmax) &&
  decide (t.nrep * N.rBound t + ((N.linBound + N.qBound * 3) + (N.qBound + w t - 1) / w t) ≤ Lmax)

/-- **`ForkLoadNumbers` on the numbers**: `ForkRestNumbers` and the claims within `Lmax`. -/
@[expose] def loadB (Lmax : Nat) : Bool := decide (N.claims ≤ Lmax) && N.restB t Lmax

/-- **`FitsOk` on the numbers** at the field's element bytes `fb`, the largest array `Mx` and the
largest read `Lmax`. -/
@[expose] def fitsB (fb Mx Lmax : Nat) : Bool :=
  decide (9 + Mx * fb ≤ 2 ^ 20) && N.sizesB Mx && decide (2 * (1 + fb) ≤ 2 ^ 20) &&
    decide ((9 + t.N * fb) + (9 + t.N * fb) ≤ 2 ^ 20) &&
    decide ((9 + t.block * fb) + ((9 + (2 * t.block - 1) * fb) + (9 + (2 * t.block - 1) * fb)) ≤
      2 ^ 20) &&
    decide (9 + t.nrep * t.block * fb ≤ 2 ^ 20) && decide (0 < t.nrep) && N.loadB t Lmax

end ForkReader.DomainNums

end GordieHowe.RealizedProgram
