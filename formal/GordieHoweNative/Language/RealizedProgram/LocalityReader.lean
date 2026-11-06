-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Reader

/-!
# GordieHowe: the reader of the compiled locality check

The locality check (`GordieHowe.RealizedProgram.localWithB`,
`GordieHowe/Language/RealizedProgram/Locality.lean`) reads the program's values by index and, for each
domain, the values reading only that domain's part of the committed assignment (`readsInB`, a bit
set over `asgReadsL`) and the flags of the shared expressions' closures at that test (`closFlag`):
tables the kernel evaluates once, closed terms, and compiled code would evaluate at every read. A
**locality reader** (`LReader`) adds their reads, and the domains' tree nodes, to a program reader
(`PReader`): `LReader.ofProgram ir treeNodes` reads them as the kernel definitions do,
`LReader.ofCtx ir treeNodes (LCtx.build ir treeNodes)` from a context built once per check, each
domain's tables computed once. Each kernel checker is its generic form here at `ofProgram`, by
definition; the two readers are equal (`LReader.ofCtx_build`), and compiled code runs the check at
the context (`localWithBC`, the code of `localWithB` by `localWithB_csimp`; both in
`GordieHowe/Language/RealizedProgram/LocalityReader.lean`).
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **A locality reader**: what the compiled locality check reads of a program, the program
reader's reads, each domain's test of what a value reads and closure flags at it, and the domains'
tree nodes. -/
class LReader extends PReader where
  /-- Value `v` reads only domain `d`'s part of the committed assignment (`readsInB d v`). -/
  readsIn : ℕ → ℕ → Bool
  /-- Every value an expression reads passes `readsInB d` (`closFlag Expr.directNodes
  (readsInB d)`). -/
  inFlag : ℕ → Expr → Bool
  /-- The tree nodes of domain `d`. -/
  tree : ℕ → List String

/-- **The locality reader of the kernel definitions**: the tables where they are read. -/
@[instance_reducible] def LReader.ofProgram (ir : RealizedProgram) (treeNodes : ℕ → List String) :
    LReader where
  toPReader := PReader.ofProgram ir
  readsIn := ir.readsInB
  inFlag d := ir.closFlag Expr.directNodes (ir.readsInB d)
  tree := treeNodes

/-- **The tables of one domain**: the bit set `readsInFail d` and the closure flags' bit set and
count at `readsInB d`. -/
structure LDomain where
  /-- `readsInFail d`. -/
  readsFail : ℕ
  /-- `closFlagBits Expr.directNodes (readsInB d)`. -/
  flagBits : ℕ
  /-- The number of the closure flags. -/
  nFlags : ℕ
  /-- The tree nodes of `d`. -/
  tree : List String

/-- **The context of a compiled locality check**: the program reader's context, the numbers of
values and of `asgReadsL`'s entries, and each domain's tables. -/
structure LCtx where
  /-- The program reader's context. -/
  base : PCtx
  /-- The number of values. -/
  n : ℕ
  /-- The number of `asgReadsL`'s entries. -/
  m : ℕ
  /-- The tables of each domain. -/
  doms : Array LDomain

/-- **The locality reader of a context**: the program reader's arrays and each domain's tables, the
kernel definitions past the program's domains. -/
@[instance_reducible] def LReader.ofCtx (ir : RealizedProgram) (treeNodes : ℕ → List String)
    (c : LCtx) : LReader where
  toPReader := PReader.ofCtx c.base
  readsIn d v :=
    match c.doms[d]? with
    | some t => decide (v < c.n) && bitTest t.readsFail c.m true v
    | none => ir.readsInB d v
  inFlag d e :=
    match c.doms[d]? with
    | some t => (e.directNodes.all fun v => decide (v < c.n) && bitTest t.readsFail c.m true v) &&
        e.refs.all (bitTest t.flagBits t.nFlags false)
    | none => ir.closFlag Expr.directNodes (ir.readsInB d) e
  tree d :=
    match c.doms[d]? with
    | some t => t.tree
    | none => treeNodes d

/-- **The tables of domain `d`**, at `asgReadsL`'s entries `asgL` (`m` of them): `domFailBits d`
built once and read by every test of `readsInFail d`, whose bit set the closure flags read. -/
def LDomain.build (ir : RealizedProgram) (treeNodes : ℕ → List String) (asgL : List (List ℕ))
    (m d : ℕ) : LDomain :=
  let n := ir.values.length
  let df := ir.domFailBits d
  let rf := failBits (fun _ rs => rs.all fun u => bitTest df n ((default : Value).domain == d) u)
    asgL 0
  let fl := ir.closFlagL Expr.directNodes fun v => decide (v < n) && bitTest rf m true v
  { readsFail := rf, flagBits := failBits (fun _ b => b) fl 0, nFlags := fl.length,
    tree := treeNodes d }

/-- **The context of program `ir`**: the program reader's context, `asgReadsL` through the closure
table built once, and each domain's tables. -/
def LCtx.build (ir : RealizedProgram) (treeNodes : ℕ → List String) : LCtx :=
  let cm := memoAuxL (closureStep Expr.directNodes) [] ir.exprs 0 .nil []
  let asgL := memoList (asgStepWith ir cm.1) [] ir.values
  let m := asgL.length
  { base := PCtx.build ir
    n := ir.values.length
    m := m
    doms := (List.range ir.domains.length).toArray.map (LDomain.build ir treeNodes asgL m) }

namespace LReader

variable (ir : RealizedProgram) [r : LReader]

/-- `entryLocalWithB`, at the reader. -/
def entryLocalWithB (ch : ℕ → Option ℕ) (d : ℕ) : CircuitEntry → Bool
  | .pred p => (r.predicate p).body.domain? == some d
  | .typeCheck p => (r.predicate p).body.domain? == some d
  | .realization (.logup t g) => (ir.logupNodesWith ch t g).all (r.readsIn d)
  | .realization (.macH p) => (ir.macHNodesWith ch p).all (r.readsIn d)
  | _ => true

/-- `blockLocalB`, at the reader. -/
def blockLocalB (d : ℕ) (blk : InputBlock) : Bool :=
  match blk.value? with
  | some u => (r.value u).domain == d
  | none => true

/-- `padLocalB`, at the reader. -/
def padLocalB (v : ℕ) (x : Value) : Bool :=
  !(decide (PReader.IsLate ir v)) ||
    match x.padSpace with
    | .node s => decide (s ∈ r.tree x.domain)
    | .full => true

/-- `localWithB`, at the reader. -/
def localWithB (ch : ℕ → Option ℕ) : Bool :=
  ir.predicates.all (fun p =>
      match p.body.domain? with
      | some d => p.body.exprs.all (r.inFlag d ·.2) && (ir.tableCols p.body).all (r.readsIn d)
      | none => true) &&
    allIdx (fun _ c => c.entries.all (entryLocalWithB ir ch c.domain) &&
      c.inputs.all (blockLocalB c.domain)) ir.circuits 0 &&
    allIdx (fun _ b => b.parts.all fun p => (r.predicate p).body.domain? == some b.domain)
      ir.batches 0 &&
    allIdx (padLocalB ir) ir.values 0

end LReader

/-- **The locality check at a context built once**: the code compiled for `localWithB`
(`localWithB_csimp`). -/
def localWithBC (ir : RealizedProgram) (ch : ℕ → Option ℕ) (treeNodes : ℕ → List String) : Bool :=
  let c := LCtx.build ir treeNodes
  @LReader.localWithB ir (LReader.ofCtx ir treeNodes c) ch

end GordieHowe.RealizedProgram
