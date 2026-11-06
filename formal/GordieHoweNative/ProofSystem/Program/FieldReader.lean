-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.PackingDesc
public import GordieHoweNative.ProofSystem.Program.FieldInput
public import GordieHoweNative.ProofSystem.Program.FieldDomain
public import GordieHoweNative.Language.RealizedProgram.InputLayout
public import GordieHoweNative.Language.RealizedProgram.Affine
public import GordieHoweNative.Language.RealizedProgram.Reader
public import GordieHoweNative.Language.RealizedProgram.Cells

/-!
# GordieHowe: the compiled field checks of a domain, at a packing descriptor

The checks of domain `d` (`GordieHowe.RealizedProgram.fieldOkB`,
`GordieHowe/ProofSystem/Program/FieldDomain.lean`) read the field's packing facts and the program.
Here they are written once:

* **against the packing facts they read** (`PackReads`): the field's degree, whether it realizes an
  edge, a node's degree, whether it has a skip domain, whether it has the bit sumcheck's nodes. A
  packing descriptor (`PackingDesc`, the facts at the queries the program makes, naturals and
  Booleans) gives them (`PackReads.ofDesc`), with `false` (or no degree) where it has no entry;
  the field's packing facts give them too (`PackReads.ofPacking`, in GordieHowe);
* **against a field reader** (`FReader`): a program reader (`PReader`) with the values reading
  nothing of the committed assignment (`pubT`) and the expressions' lengths (`exprLen`), read from
  tables built once in compiled code (`FReader.ofCtx`, `FCtx.build`).

`fieldChecksB` is every check of `fieldOkB` but the Ligero certificate's (`LigeroCert.validB`,
`planLigeroB`, the tableau part), with the quadratic triples' cells by a walk of the predicates
(`quadsOkW`, no enumeration of a finite type). `fieldOkBD` is it at the kernel's reader and a
descriptor, and compiled code runs it at the context built once (`fieldOkBC`, `fieldOkBD_csimp`).
The soundness, `fieldOkB_of_desc`, is in `GordieHowe/ProofSystem/Program/FieldReader.lean`.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **The packing facts the field checks read**: the field's degree, whether it realizes an edge
(child degree, relative degree, masking mode), a node's degree (`none`: unknown, which fails the
check reading it), whether it has a skip domain (width, degree), whether it has the bit sumcheck's
interpolation nodes. -/
structure PackReads where
  /-- The degree of the field over its prime field. -/
  n : ℕ
  /-- Whether the field realizes an edge. -/
  edgeOk : ℕ → ℕ → PackingMode → Bool
  /-- A node's degree, `none` when unknown. -/
  nodeDeg : String → Option (Option ℕ)
  /-- Whether the field has a skip domain. -/
  skipOk : ℕ → ℕ → Bool
  /-- Whether the field has the bit sumcheck's interpolation nodes. -/
  hasNodes : Bool

/-- **The packing facts of a descriptor**, `false` (or no degree) at a query it has no entry
for. -/
def PackReads.ofDesc (D : PackingDesc) : PackReads :=
  ⟨D.n, D.edgeOk, D.nodeDeg?, D.skipOk, D.hasNodes⟩

/-- **A field reader**: a program reader, the values reading nothing of the committed assignment
(`pubT`), and the expressions' lengths (`exprLen`). -/
class FReader extends PReader where
  /-- Value `v` reads nothing of the committed assignment (`pubT`'s entry). -/
  pub : ℕ → Bool
  /-- An expression's length (`exprLen`). -/
  exprLen : Expr → ℕ

/-- **The field reader of the kernel definitions.** -/
@[instance_reducible] def FReader.ofProgram (ir : RealizedProgram) : FReader where
  toPReader := PReader.ofProgram ir
  pub v := ir.pubT.getD v false
  exprLen := ir.exprLen

/-- **The context of a compiled field check**: the program reader's context, `pubT`'s entries and
the number of shared expressions. -/
structure FCtx where
  /-- The program reader's context. -/
  base : PCtx
  /-- `pubT`'s entries, by value. -/
  pub : Array Bool
  /-- The number of shared expressions. -/
  nExprs : ℕ

/-- **The field reader of a context**: array reads, the shared expressions' number read once. -/
@[instance_reducible] def FReader.ofCtx (ir : RealizedProgram) (c : FCtx) : FReader where
  toPReader := PReader.ofCtx c.base
  pub v := c.pub[v]?.getD false
  exprLen e := Expr.len ir (ir.refLen c.nExprs) e

/-- **The context of program `ir`**, each table built once. -/
def FCtx.build (ir : RealizedProgram) : FCtx :=
  { base := PCtx.build ir
    pub := (memoList ir.pubStep false ir.values).toArray
    nExprs := ir.exprs.length }

namespace FReader

variable (ir : RealizedProgram) [r : FReader] (d : ℕ)

/-! ## The values -/

/-- `isCellValue`, at the reader. -/
def isCellValue (v : ℕ) : Bool :=
  (r.value v).domain == d &&
    match (r.value v).kind with
    | .priv => true
    | .padCopy _ _ => true
    | _ => false

/-- `isLateOf`, at the reader. -/
def isLateOf (v : ℕ) : Bool :=
  (r.value v).field.isNone && (r.value v).domain == d && decide (PReader.IsLate ir v)

/-- `valueField`, at the reader. -/
def valueField (v : ℕ) : ℕ :=
  match (r.value v).kind.allowsField, (r.value v).field with
  | true, some f => f
  | _, _ => ir.domainField (r.value v).domain

/-- `bitViewOk`, at the reader. -/
def bitViewOk (v : ℕ) : Bool :=
  match (r.value v).kind with
  | .bits w sel =>
    (r.value v).domain == d && (r.value w).domain == d && (r.value w).kind.isPriv &&
      decide (0 < sel.size) && (r.value v).size == 16 * sel.size
  | _ => false

/-! ## The cells' nodes (`FieldTree`) -/

/-- `cellName`, at the reader. -/
def cellName : CellKey → Option String
  | .val v _ => (r.value v).node.map (·.name)
  | .pad v _ =>
    match (r.value v).padSpace with
    | .full => none
    | .node s => some s
  | .filler _ _ => none

/-- `nodeDegB` at the packing facts `K`: an unknown degree fails. -/
def nodeDegB (K : PackReads) (es : List PackingEdge) (s : String) : Bool :=
  match K.nodeDeg s with
  | some nd => es.all (fun e => e.child != s || nd == some e.childDegree) &&
      (es.any (·.child == s) || nd == some K.n)
  | none => false

/-- `nameOkB` at the packing facts `K`. -/
def nameOkB (K : PackReads) (es : List PackingEdge) : Option String → Bool
  | none => true
  | some s => nodeDegB K es s

/-- `placeValueB`, at the reader and the packing facts `K`. -/
def placeValueB (K : PackReads) (es : List PackingEdge) (v : ℕ) : Bool :=
  (r.value v).size == 0 ||
    if isCellValue d v then nameOkB K es (cellName (.val v 0))
    else if isLateOf ir d v then nameOkB K es (cellName (.pad v 0))
    else true

/-- `placeOkE`, at the reader and the packing facts `K`. -/
def placeOkE (K : PackReads) (es : List PackingEdge) : Except StructFailure Unit :=
  Twin.allE (fun _ v => Twin.guardE (placeValueB ir d K es v) ⟨v, 0, .nodeDegree⟩) 0
    (List.range ir.values.length)

/-- `placeOkB`, at the reader and the packing facts `K`. -/
def placeOkB (K : PackReads) (es : List PackingEdge) : Bool := Twin.okB (placeOkE ir d K es)

/-! ## The circuits' inputs and the viewed words (`FieldInput`) -/

/-- `blockOkT`, at the reader. -/
def blockOkT (c : ℕ) : InputBlock → Bool
  | .committed u a n => decide (u < ir.values.length) && isCellValue d u &&
      decide (n = (r.value u).size) && decide ((ir.circuit c).publicInputs ≤ a) &&
      decide (a + n ≤ ir.privEnd c)
  | .pad u a n => decide (u < ir.values.length) && !isCellValue d u &&
      isLateOf ir d u && decide (n = (r.value u).size) &&
      decide ((ir.circuit c).publicInputs ≤ a) && decide (a + n ≤ ir.privEnd c)
  | .pub u a n => decide (valueField ir u = ir.circField c) &&
      (decide (PReader.IsLate ir u) || ir.pubB ir.fuel u) && decide (1 ≤ a) &&
      decide (a + n ≤ (ir.circuit c).publicInputs)
  | .realizationPub _ a n => decide (1 ≤ a) && decide (a + n ≤ (ir.circuit c).publicInputs)
  | .filler a n => decide ((ir.circuit c).publicInputs ≤ a) && decide (a + n ≤ ir.privEnd c)
  | .view u a n => bitViewOk d u && decide (n ≤ (r.value u).size) &&
      decide ((ir.circuit c).publicInputs ≤ a) && decide (a + n ≤ ir.privEnd c)
  | .batchPads _ a n => decide (ir.privEnd c ≤ a) && decide (a + n ≤ (ir.circuit c).inputCount)

/-- `blockOkB`, at the reader. -/
def blockOkB (c : ℕ) : InputBlock → Bool
  | .pub u a n => decide (valueField ir u = ir.circField c) &&
      (decide (PReader.IsLate ir u) || r.pub u) && decide (1 ≤ a) &&
      decide (a + n ≤ (ir.circuit c).publicInputs)
  | b => blockOkT ir d c b

/-- `entryNodesC`, at the reader. -/
def entryNodesC : CircuitEntry → List ℕ
  | .pred p => PReader.predNodesM ir (r.predicate p).body
  | .typeCheck p => PReader.predNodesM ir (r.predicate p).body
  | .realization (.logup t g) => ir.logupNodesWith (fun _ => none) t g
  | .realization (.macH p) => ir.macHNodesWith (fun _ => none) p
  | _ => []

/-- `circValuesC`, at the reader. -/
def circValuesC (c : ℕ) : List ℕ := (ir.circuit c).entries.flatMap (entryNodesC ir)

/-- `circReadsC`, at the reader. -/
def circReadsC (c : ℕ) : List ℕ := (circValuesC ir c).flatMap r.asgReads

/-- `viewWordsSetB`, at the reader. -/
def viewWordsSetB (S : CircuitSets) : InputBlock → Bool
  | .view u _ _ =>
    match (r.value u).kind with
    | .bits w _ => natMem S.committed w
    | _ => true
  | _ => true

/-- `inputsTB`, at the reader. -/
def inputsTB (c : ℕ) : Bool :=
  let S := circuitSets (ir.circuit c)
  decide (InputBlock.layoutEnd 1 (ir.circuit c).inputs = some (ir.circuit c).inputCount) &&
    decide (1 ≤ (ir.circuit c).publicInputs) &&
    decide ((ir.circuit c).publicInputs ≤ ir.privEnd c) &&
    (ir.circuit c).inputs.all (blockOkB ir d c) && (ir.circuit c).entries.all ir.entryPredOkB &&
    (circValuesC ir c).all (· < ir.values.length) &&
    (circReadsC ir c).all (fun v => (!isCellValue d v || natMem S.committed v) &&
      (!isLateOf ir d v || natMem S.pad v)) &&
    (ir.circuit c).inputs.all (viewWordsSetB S)

/-- `viewsOkB`, at the reader. -/
def viewsOkB (es : List PackingEdge) : Bool :=
  (List.range ir.values.length).all fun u =>
    match (r.value u).kind with
    | .bits w _ => (r.value u).domain != d || ir.viewableB es w
    | _ => true

/-! ## The circuits, the batches and the quadratic triples (`FieldClaim`) -/

/-- `circs`, at the reader. -/
def circs : List (Fin ir.circuits.length) :=
  (List.finRange ir.circuits.length).filter fun c => (ir.circuit c).domain == d

/-- `batchesOkB` at the packing facts `K`. -/
def batchesOkB (K : PackReads) : Bool :=
  (List.finRange ir.batches.length).all fun b =>
    (ir.batch b).domain != d || (K.skipOk (ir.batch b).width (ir.batch b).degree &&
      (!decide ((ir.batch b).operands = .bits) || ((ir.batch b).bitSumcheck && K.hasNodes)))

/-- `quadCellB`, at the reader. -/
def quadCellB (v : ℕ) : Bool :=
  isCellValue d v && (r.value v).phase == 0 && (r.value v).type == .field &&
    (r.value v).node.isNone &&
    match (r.value v).kind with
    | .priv => true
    | _ => false

/-- `quadLeaves`, at a predicate read from the walk. -/
def quadLeavesOf (pr : Predicate) : Option (ℕ × ℕ × ℕ) :=
  match pr.body with
  | .equal d' (.mul (.leaf a) (.leaf b)) (.leaf c) .quadratic =>
    if d' = d ∧ quadCellB d a = true ∧ quadCellB d b = true ∧ quadCellB d c = true then
      some (a, b, c) else none
  | _ => none

/-- `quadLhs`, at a predicate read from the walk. -/
def quadLhsOf (pr : Predicate) : Expr :=
  match pr.body with
  | .equal _ e _ _ => e
  | _ => .leaf 0

/-- **Value `u` is a cell of domain `d` with at least `L` coordinates.** -/
def quadCellsAt (L u : ℕ) : Bool :=
  decide (u < ir.values.length) && isCellValue d u && decide (L ≤ (r.value u).size)

/-- **The quadratic triples' cells are cells of `d`** (`QuadsOk`), in one walk of the predicates:
each quadratic predicate's three cells have its left side's coordinates. -/
def quadsOkW : Bool :=
  allIdx (fun _ pr => match quadLeavesOf d pr with
    | some (a, b, c) =>
      let L := r.exprLen (quadLhsOf pr)
      L == 0 || (quadCellsAt ir d L a && quadCellsAt ir d L b && quadCellsAt ir d L c)
    | none => true) ir.predicates 0

/-! ## The checks of a domain -/

/-- **Every check of domain `d` but the Ligero certificate's** (`fieldOkB`'s), at the reader and
the packing facts `K`: the realized edges, the tree, the cells' nodes, the viewed words, every
circuit's inputs, the covered batches and the quadratic triples' cells. -/
def fieldChecksB (P : Export.Plan) (K : PackReads) : Bool :=
  let es := (ir.planPacking P d).filter fun e => K.edgeOk e.childDegree e.degree e.mode
  es.length == (ir.planPacking P d).length && treeOkB es K.n && placeOkB ir d K es &&
    viewsOkB ir d es && (circs ir d).all (fun c => inputsTB ir d c) && batchesOkB ir d K &&
    quadsOkW ir d

end FReader

/-- **The checks of domain `d` at a packing descriptor** (`FReader.fieldChecksB` at the kernel's
reader): `fieldOkB_of_desc` gives `fieldOkB` from it, the descriptor the field's, and the Ligero
certificate's checks. -/
def fieldOkBD (ir : RealizedProgram) (d : ℕ) (P : Export.Plan) (D : PackingDesc) : Bool :=
  @FReader.fieldChecksB ir (FReader.ofProgram ir) d P (PackReads.ofDesc D)

/-- **The checks of domain `d` at a packing descriptor, at a context built once**: the code
compiled for `fieldOkBD` (`fieldOkBD_csimp`). -/
def fieldOkBC (ir : RealizedProgram) (d : ℕ) (P : Export.Plan) (D : PackingDesc) : Bool :=
  let c := FCtx.build ir
  @FReader.fieldChecksB ir (FReader.ofCtx ir c) d P (PackReads.ofDesc D)

end GordieHowe.RealizedProgram
