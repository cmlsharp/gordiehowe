-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Placement
public import GordieHoweNative.Language.RealizedProgram.Affine
public import GordieHoweNative.Language.RealizedProgram.Reader

/-!
# GordieHowe: the reader of the compiled cells checks

The cells checks (`GordieHowe.RealizedProgram.placementB`,
`GordieHowe/Language/RealizedProgram/Placement.lean`) read the program's values and predicates by
index and the batch forms' leaf tests and shared expressions' summaries from tables: bit sets of
the values (`batchLeafFail`, `cellFail`, `bitsLeafFail`, `constFail`) and of the shared expressions'
summaries (`refBits`). The kernel evaluates each table once, a closed term; compiled code would
evaluate it at every read. A **cells reader** (`CellsReader`) adds the reads of the tables to a
program reader (`PReader`):

* `CellsReader.ofProgram ir` reads the tables as the kernel definitions do;
* `CellsReader.ofCtx ir (CellsCtx.build ir)` reads them from a context built once per check, the
  program reader's arrays (`PCtx`) and the tables computed once.

Each kernel checker is its generic form here (`CellsReader.placementB`, and the checks it calls) at
`ofProgram`, by definition; the two readers are equal (`CellsReader.ofCtx_build`), and compiled code
runs the checker at the context (`placementBC`, the code of `placementB` by `placementB_csimp`; both
in `GordieHowe/Language/RealizedProgram/CellsReader.lean`).
-/

local notation "ℕ" => Nat

public section

namespace GordieHowe.RealizedProgram

open Export Twin

/-- **The sublists of a list**, all `2 ^ l.length` of them in order (`mem_subListsN`); the product
cells by lists (`Shape.cellsL`) filter them. -/
@[expose] def subListsN : List ℕ → List (List ℕ)
  | [] => [[]]
  | a :: l => subListsN l ++ (subListsN l).map (a :: ·)

/-- **The number of product cells of a shape**, by lists (`Shape.cells_eq_cellsL`). -/
@[expose] def Shape.cellsL (sh : Shape) : ℕ :=
  (insertAll [] (sh.monos.flatMap fun c =>
    (subListsN (c.2.mergeSort (· ≤ ·))).filter fun s => decide (2 ≤ s.length))).length

/-- **`atomSum` at the number of shared expressions `n`** (`atomSum_eq_atomSumN` at their
number): compiled code reads the number once. -/
@[expose] def atomSumN (ir : RealizedProgram) (n : ℕ) (lf : ℕ → Bool) (nd : ℕ → ℕ) (e : Expr) :
    AtomSum :=
  ⟨(e.directNodes ++ e.refs.flatMap (ir.refClosure Expr.directNodes n)).all lf &&
      (e.coefNodes ++ e.refs.flatMap (ir.refClosure Expr.coefNodes n)).all (nd · == 0),
    min (e.deg nd (ir.refDeg nd n)) 2⟩

/-- **`bpolySum` at an expression length `el` and a summary `as`** of the expressions it does
not walk (`bpolySumW_eq`: `bpolySum` at `exprLen` and `atomSum lf nd`). -/
@[expose] def bpolySumW (el : Expr → ℕ) (as : Expr → AtomSum) (rs : ℕ → AtomSum) :
    Expr → AtomSum × Option (List BMono)
  | .add a b =>
      let ra := bpolySumW el as rs a
      let rb := bpolySumW el as rs b
      let s := ra.1.join rb.1
      (s, bnode (fun _ => s.atom) (.add a b) do
        let p ← ra.2
        let q ← rb.2
        pure (p ++ q))
  | .sub a b =>
      let ra := bpolySumW el as rs a
      let rb := bpolySumW el as rs b
      let s := ra.1.join rb.1
      (s, bnode (fun _ => s.atom) (.sub a b) do
        let p ← ra.2
        let q ← rb.2
        pure (p ++ q.map BMono.negate))
  | .scale (.const c) a =>
      let ra := bpolySumW el as rs a
      (ra.1, bnode (fun _ => ra.1.atom) (.scale (.const c) a) do
        let p ← ra.2
        pure (p.map (BMono.scale c)))
  | .mul a b =>
      let ra := bpolySumW el as rs a
      let rb := bpolySumW el as rs b
      let s := ra.1.mul rb.1
      (s, bnode (fun _ => s.atom) (.mul a b) do
        let p ← ra.2
        let q ← rb.2
        pure (p.flatMap fun m => q.map m.mul))
  | .reindex idx a =>
      let ra := bpolySumW el as rs a
      (ra.1, bnode (fun _ => ra.1.atom) (.reindex idx a) do
        let p ← ra.2
        viewed (fun _ => true) (p.map (BMono.mapFactors (.reindex idx))))
  | .concat a b =>
      let ra := bpolySumW el as rs a
      let rb := bpolySumW el as rs b
      let s := ra.1.join rb.1
      (s, bnode (fun _ => s.atom) (.concat a b) do
        let p ← ra.2
        let q ← rb.2
        viewed (fun _ => true) (p.map (BMono.mapFactors (Expr.padRight (el a))) ++
          q.map (BMono.mapFactors (Expr.padLeft (el a)))))
  | .ref k =>
      let s := rs k
      (s, bnode (fun _ => s.atom) (.ref k) none)
  | e =>
      let s := as e
      (s, bnode (fun _ => s.atom) e none)

/-- **A cells reader**: what the compiled cells checks read of a program, the program reader's
reads and the batch forms' tables. -/
class CellsReader extends PReader where
  /-- A value a batch operand on columns may read (`batchLeafB`). -/
  batchLeaf : ℕ → Bool
  /-- The degree of a value in the committed cells (`cellNdB`). -/
  cellNd : ℕ → ℕ
  /-- A value a bit operand of domain `d` may read (`bitsLeafB d`). -/
  bitsLeaf : ℕ → ℕ → Bool
  /-- The degree of a value as a bit operand (`bitsNdB`). -/
  bitsNd : ℕ → ℕ
  /-- The summary of a shared expression for a batch on columns (`refSum` at `batchLeafB`). -/
  refSumC : ℕ → AtomSum
  /-- The summary of a shared expression for a batch on bits of domain `d` (`refSum` at
  `bitsLeafB d`). -/
  refSumB : ℕ → ℕ → AtomSum
  /-- The summary of an expression for a batch on columns (`atomSum` at `batchLeafB`). -/
  atomSumC : Expr → AtomSum
  /-- The summary of an expression for a batch on bits of domain `d` (`atomSum` at
  `bitsLeafB d`). -/
  atomSumB : ℕ → Expr → AtomSum
  /-- An expression's length (`exprLen`). -/
  exprLen : Expr → ℕ

/-- **The cells reader of the kernel definitions**: the tables where they are read. -/
@[expose, instance_reducible] def CellsReader.ofProgram (ir : RealizedProgram) : CellsReader where
  toPReader := PReader.ofProgram ir
  batchLeaf := ir.batchLeafB
  cellNd := ir.cellNdB
  bitsLeaf := ir.bitsLeafB
  bitsNd := ir.bitsNdB
  refSumC := ir.refSum ir.batchLeafB ir.cellNdB
  refSumB d := ir.refSum (ir.bitsLeafB d) ir.bitsNdB
  atomSumC := ir.atomSum ir.batchLeafB ir.cellNdB
  atomSumB d := ir.atomSum (ir.bitsLeafB d) ir.bitsNdB
  exprLen := ir.exprLen

/-- **The context of a compiled cells check**: the program reader's context and the tables, each
computed once (`CellsCtx.build`). -/
structure CellsCtx where
  /-- The program reader's context. -/
  base : PCtx
  /-- The number of values. -/
  n : ℕ
  /-- `batchLeafFail`. -/
  leafFail : ℕ
  /-- `cellFail`. -/
  cellFail : ℕ
  /-- `constFail`. -/
  constFail : ℕ
  /-- `bitsLeafFail d` of each domain `d`. -/
  bitsFail : Array ℕ
  /-- Whether the shared expressions read only earlier entries (`refsOrderedB`). -/
  ordered : Bool
  /-- The number of shared expressions. -/
  nExprs : ℕ
  /-- `refBits` at the leaf tests on columns. -/
  refC : RefBits
  /-- `refBits` at the leaf tests on bits of each domain. -/
  refB : Array RefBits

/-- **The cells reader of a context**: the program reader's arrays and the tables of the context,
the kernel definitions where the context has no table (a domain past the program's, an unordered
program's shared expressions). -/
@[expose, instance_reducible] def CellsReader.ofCtx (ir : RealizedProgram) (c : CellsCtx) :
    CellsReader where
  toPReader := PReader.ofCtx c.base
  batchLeaf v := bitTest c.leafFail c.n (batchLeafV default) v
  cellNd v := cond (bitTest c.cellFail c.n (!cellNdV default) v) 0 1
  bitsLeaf d v :=
    match c.bitsFail[d]? with
    | some f => bitTest f c.n (ir.bitsLeafV d default) v
    | none => ir.bitsLeafB d v
  bitsNd v := cond (bitTest c.constFail c.n (bitsNdV default) v) 1 0
  refSumC k :=
    if c.ordered && decide (k < c.nExprs) then c.refC.get k
    else ir.atomSum ir.batchLeafB ir.cellNdB (.ref k)
  refSumB d k :=
    match c.refB[d]? with
    | some t =>
      if c.ordered && decide (k < c.nExprs) then t.get k
      else ir.atomSum (ir.bitsLeafB d) ir.bitsNdB (.ref k)
    | none => ir.refSum (ir.bitsLeafB d) ir.bitsNdB k
  atomSumC e :=
    ir.atomSumN c.nExprs (fun v => bitTest c.leafFail c.n (batchLeafV default) v)
      (fun v => cond (bitTest c.cellFail c.n (!cellNdV default) v) 0 1) e
  atomSumB d e :=
    match c.bitsFail[d]? with
    | some f => ir.atomSumN c.nExprs (fun v => bitTest f c.n (ir.bitsLeafV d default) v)
        (fun v => cond (bitTest c.constFail c.n (bitsNdV default) v) 1 0) e
    | none => ir.atomSum (ir.bitsLeafB d) ir.bitsNdB e
  exprLen e := Expr.len ir (ir.refLen c.nExprs) e

/-- **The context of program `ir`**: the program reader's context, the bit sets of the values, and
the shared expressions' summaries at the leaf tests read through them, each built once. -/
@[expose] def CellsCtx.build (ir : RealizedProgram) : CellsCtx :=
  let n := ir.values.length
  let leafFail := ir.batchLeafFail
  let cellFail := ir.cellFail
  let constFail := ir.constFail
  let bitsFail := (List.range ir.domains.length).toArray.map ir.bitsLeafFail
  let lf := fun v => bitTest leafFail n (batchLeafV default) v
  let nd := fun v => cond (bitTest cellFail n (!cellNdV default) v) 0 1
  let bnd := fun v => cond (bitTest constFail n (bitsNdV default) v) 1 0
  { base := PCtx.build ir
    n := n
    leafFail := leafFail
    cellFail := cellFail
    constFail := constFail
    bitsFail := bitsFail
    ordered := ir.refsOrderedB
    nExprs := ir.exprs.length
    refC := ir.refBits lf nd
    refB := (List.range ir.domains.length).toArray.map fun d =>
      let f := ir.bitsLeafFail d
      ir.refBits (fun v => bitTest f n (ir.bitsLeafV d default) v) bnd }

namespace CellsReader

section

variable (ir : RealizedProgram) [p : PReader]

/-- `chalValuesE`, at the reader. -/
@[expose] def chalValuesE (S : Structure) : Except StructFailure Unit :=
  seqE
    (allE (fun _ jv => guardE (decide (jv.2 < ir.values.length) &&
        match (p.value jv.2).kind with
        | .challenge j => j == jv.1
        | _ => false) ⟨jv.1, jv.2, .chalValue⟩) 0 S.chalValues)
    (allE (fun v x => match x.kind with
        | .challenge j => guardE (match S.chalOf j with
            | some w => decide (w ≤ v)
            | none => false) ⟨v, j, .chalSweep⟩
        | _ => .ok ()) 0 ir.values)

/-- `chalValuesB`, at the reader. -/
@[expose] def chalValuesB (S : Structure) : Bool := okB (chalValuesE ir S)

end

variable (ir : RealizedProgram) [r : CellsReader]

/-! ## The values' tests (`isCellValue`, `isLateOf`, `CellsLowering`, `Views`, `Affine`) -/

/-- `isCellValue`, at the reader. -/
@[expose] def isCellValue (d v : ℕ) : Bool :=
  (r.value v).domain == d &&
    match (r.value v).kind with
    | .priv => true
    | .padCopy _ _ => true
    | _ => false

/-- `isLateOf`, at the reader. -/
@[expose] def isLateOf (d v : ℕ) : Bool :=
  (r.value v).field.isNone && (r.value v).domain == d && decide (PReader.IsLate ir v)

/-- `typeAtCellB`, at the reader. -/
@[expose] def typeAtCellB (d v : ℕ) : Bool :=
  isCellValue d v &&
    (match (r.value v).kind with
      | .priv => true
      | _ => false) &&
    match (r.value v).type with
    | .field => true
    | .sub E => (r.value v).node.map (·.name) == some E
    | .bit => (r.value v).node.isSome

/-- `bitViewTypeB`, at the reader. -/
@[expose] def bitViewTypeB (v : ℕ) : Bool :=
  (match (r.value v).kind with
    | .bits _ _ => true
    | _ => false) && decide ((r.value v).type = .bit)

/-- `lateTypeB`, at the reader. -/
@[expose] def lateTypeB (d v : ℕ) : Bool :=
  isLateOf ir d v && !isCellValue d v &&
    match (r.value v).type, (r.value v).padSpace with
    | .sub E, .node E' => E == E'
    | _, _ => false

/-- `typeOwnB`, at the reader. -/
@[expose] def typeOwnB (v : ℕ) : Bool :=
  decide ((r.value v).domain < ir.domains.length) &&
    (typeAtCellB (r.value v).domain v || bitViewTypeB v ||
      lateTypeB ir (r.value v).domain v)

/-- `quadCellB`, at the reader. -/
@[expose] def quadCellB (d v : ℕ) : Bool :=
  isCellValue d v && (r.value v).phase == 0 && (r.value v).type == .field &&
    (r.value v).node.isNone &&
    match (r.value v).kind with
    | .priv => true
    | _ => false

/-- `quadLeaves`, at the reader. -/
@[expose] def quadLeaves (d p : ℕ) : Option (ℕ × ℕ × ℕ) :=
  match (r.predicate p).body with
  | .equal d' (.mul (.leaf a) (.leaf b)) (.leaf c) .quadratic =>
    if d' = d ∧ quadCellB d a = true ∧ quadCellB d b = true ∧ quadCellB d c = true then
      some (a, b, c) else none
  | _ => none

/-- `isQuad`, at the reader. -/
@[expose] def isQuad (d p : ℕ) : Bool := (quadLeaves d p).isSome

/-- `bitViewOk`, at the reader. -/
@[expose] def bitViewOk (d v : ℕ) : Bool :=
  match (r.value v).kind with
  | .bits w sel =>
    (r.value v).domain == d && (r.value w).domain == d && (r.value w).kind.isPriv &&
      decide (0 < sel.size) && (r.value v).size == 16 * sel.size
  | _ => false

/-- `rowValueOk`, at the reader. -/
@[expose] def rowValueOk (v : ℕ) : Bool :=
  match (r.value v).kind with
  | .priv => true
  | .padCopy _ _ => true
  | .late => true
  | .bits _ _ => false
  | .bound x => ir.linPrivB x
  | _ => ir.pubB ir.fuel v

/-- `rowExprOk`, at the reader. -/
@[expose] def rowExprOk (e : Expr) : Bool :=
  (ir.exprNodes e).all (rowValueOk ir) && (ir.closure Expr.coefNodes e).all (ir.cellNd · == 0) &&
    decide (ir.cellDeg e ≤ 1)

/-- `viewValueOk`, at the reader. -/
@[expose] def viewValueOk (d v : ℕ) : Bool := rowValueOk ir v || bitViewOk d v

/-- `viewExprOk`, at the reader. -/
@[expose] def viewExprOk (d : ℕ) (e : Expr) : Bool :=
  (ir.exprNodes e).all (viewValueOk ir d) &&
    (ir.closure Expr.coefNodes e).all (ir.cellNd · == 0) && decide (ir.cellDeg e ≤ 1)

/-! ## The batches (`Views`) -/

/-- `formsOf`, at the reader. -/
@[expose] def formsOf (d b : ℕ) : Expr → Option (List BMono) :=
  match (ir.batch b).operands with
  | .columns => fun e => (bpolySumW r.exprLen r.atomSumC r.refSumC e).2
  | .bits => fun e => (bpolySumW r.exprLen (r.atomSumB d) (r.refSumB d) e).2

/-- `predLen`, at the reader. -/
@[expose] def predLen (d b : ℕ) (pr : Predicate) : ℕ :=
  ((pr.body.batchSides d b).map fun s => r.exprLen s.1).getD 0

/-- `partLen`, at the reader. -/
@[expose] def partLen (d b j : ℕ) : ℕ := ((ir.partSides d b j).map fun s => r.exprLen s.1).getD 0

/-- `partPredOkB`, at the reader. -/
@[expose] def partPredOkB (bp : Expr → Option (List BMono)) (d b : ℕ) (sh0 : Shape) (l0 : ℕ)
    (pr : Predicate) : Bool :=
  match ir.predForm bp d b pr with
  | some pf => pf.shape.okB (ir.batch b).degree && (ir.merged b || pf.shape == sh0) &&
      (!ir.merged b || predLen d b pr == l0)
  | none => false

/-- `partsOkB`, at the reader, the first part's shape and coordinates computed once. -/
@[expose] def partsOkB (bp : Expr → Option (List BMono)) (d b : ℕ) : Bool :=
  match (ir.batch b).parts with
  | [] => false
  | p0 :: ps =>
    let sh0 := ir.predShape bp d b (r.predicate p0)
    let l0 := predLen d b (r.predicate p0)
    (p0 :: ps).all fun p => decide (p < r.nPreds) && partPredOkB ir bp d b sh0 l0 (r.predicate p)

/-- `partsLen`, at the reader. -/
@[expose] def partsLen (d b : ℕ) : ℕ :=
  if ir.merged b then partLen ir d b 0
  else ((ir.batch b).parts.map fun p => predLen d b (r.predicate p)).sum

/-- `batchOkB`, at the reader, with the product-cell counter supplied explicitly. -/
@[expose] def batchOkWith (cells : Shape → ℕ) (d b : ℕ) : Bool :=
  let bp := formsOf ir d b
  let sh := ir.batchShape bp d b
  decide (b < ir.batches.length) && decide ((ir.batch b).domain = d) &&
    partsOkB ir bp d b &&
    (!ir.merged b || decide (2 ≤ (ir.batch b).parts.length)) &&
    decide (0 < (ir.batch b).degree) &&
    (((ir.batch b).operands != .bits) ||
      decide ((ir.field (ir.domainField d)).characteristic = 2)) &&
    decide ((ir.batch b).skipDomain = skipDomainName (ir.field (ir.domainField d)).characteristic) &&
    decide (SkipFits (ir.batch b).degree (ir.batch b).width
      (ir.field (ir.domainField d)).characteristic) &&
    decide (0 < (ir.batch b).width) &&
    decide (partsLen ir d b ≤ (ir.batch b).operands.lane * (ir.batch b).instances) &&
    decide ((ir.batch b).operands.lane * (ir.batch b).instances ≤
      2 ^ (ir.batch b).rounds * (ir.batch b).width) &&
    decide ((ir.batch b).pads = ((ir.batch b).degree - 1) * ((ir.batch b).width - 1) +
      ((ir.batch b).rounds * (ir.batch b).degree +
        (sh.k + cells sh)) +
      (if (ir.batch b).operands = .bits then 2 * 4 else 0))

/-- `batchOkB`, with the product cells counted by lists. -/
@[expose] def batchOkB (d b : ℕ) : Bool := batchOkWith ir Shape.cellsL d b

/-! ## The placement checks (`Placement`) -/

/-- `batchesE`, with an explicit product-cell counter. -/
@[expose] def batchesWith (cells : Shape → ℕ) : Except StructFailure Unit :=
  allE (fun b B => guardE (batchOkWith ir cells B.domain b) ⟨b, 0, .batch⟩) 0 ir.batches

/-- `batchesE`, at the reader. -/
@[expose] def batchesE : Except StructFailure Unit := batchesWith ir Shape.cellsL

/-- `rowBodyB`, at the reader. -/
@[expose] def rowBodyB (d : ℕ) (b : PredBody) : Bool :=
  match b.rowSides d with
  | some (e, e') => rowExprOk ir e && rowExprOk ir e'
  | none => false

/-- `viewRowBodyB`, at the reader. -/
@[expose] def viewRowBodyB (d : ℕ) (b : PredBody) : Bool :=
  match b.rowSides d with
  | some (e, e') => !rowBodyB ir d b && viewExprOk ir d e && viewExprOk ir d e'
  | none => false

/-- `routeOkE`, at the reader. -/
@[expose] def routeOkE (pid : ℕ) (pr : Predicate) (rt : Route) : Except StructFailure Unit :=
  match pr.body.domain? with
  | none => .error ⟨pid, 0, .routeDomain⟩
  | some d =>
    seqE (guardE (decide (d < ir.domains.length)) ⟨pid, 0, .routeDomain⟩) <|
      match rt with
      | .affine false => guardE (rowBodyB ir d pr.body) ⟨pid, 0, .routePointer⟩
      | .affine true => guardE (viewRowBodyB ir d pr.body) ⟨pid, 0, .routePointer⟩
      | .quadratic => guardE (isQuad d pid) ⟨pid, 0, .routePointer⟩
      | .batch b _ =>
        guardE (decide (b < ir.batches.length) && decide ((ir.batch b).domain = d))
          ⟨pid, b, .routePointer⟩
      | .gkr c k =>
        guardE (decide (c < ir.circuits.length) && decide ((ir.circuit c).domain = d) &&
          (decide ((ir.circuit c).entries[k]? = some (.pred pid)) ||
            decide ((ir.circuit c).entries[k]? = some (.typeCheck pid)))) ⟨pid, c, .routePointer⟩
      | .realized q js => guardE (ir.realizedRouteB pr.body q js) ⟨pid, q, .realized⟩

/-- `routesE`, at the reader. -/
@[expose] def routesE (S : Structure) : Except StructFailure Unit :=
  mergeE (·.body.needsRoute) (routeOkE ir) .routeMissing .routeExtra 0 ir.predicates S.routes

/-- `typesE`, at the reader. -/
@[expose] def typesE : Except StructFailure Unit :=
  allE (fun v x => guardE (!decide (x.typeSource = .node) || typeOwnB ir v) ⟨v, 0, .types⟩) 0
    ir.values

/-- `placementE`, at the reader. -/
@[expose] def placementE (S : Structure) : Except StructFailure Unit :=
  seqE (guardE (ir.domains.length != 0) ⟨0, 0, .nonempty⟩) <|
  seqE (chalValuesE ir S) <| seqE (batchesE ir) <| seqE (routesE ir S) <|
  seqE (ir.batchRoutesE S) <|
  seqE (ir.logupHostsE S) <| seqE (ir.alphasE S) <| seqE (ir.macHostsE S) <|
  seqE (ir.entriesE S) (typesE ir)

/-- `placementB`, at the reader. -/
@[expose] def placementB (S : Structure) : Bool := okB (placementE ir S)

end CellsReader

/-- **The cells checks at a context built once**: the code compiled for `placementB`
(`placementB_csimp`). -/
@[expose] def placementBC (ir : RealizedProgram) (S : Structure) : Bool :=
  let c := CellsCtx.build ir
  @CellsReader.placementB ir (CellsReader.ofCtx ir c) S

/-- **The challenge values' check at a program context built once**: the code compiled for
`chalValuesB` (`chalValuesB_csimp`). -/
@[expose] def chalValuesBC (ir : RealizedProgram) (S : Structure) : Bool :=
  let c := PCtx.build ir
  @CellsReader.chalValuesB ir (PReader.ofCtx c) S

end GordieHowe.RealizedProgram
