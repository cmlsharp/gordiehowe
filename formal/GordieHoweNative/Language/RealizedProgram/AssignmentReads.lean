-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Reader
public import GordieHoweNative.Language.RealizedProgram.MemoRows
public import GordieHoweNative.Language.RealizedProgram.LocalityReader
public import GordieHoweNative.Language.RealizedProgram.CellsReader
public import GordieHoweNative.ProofSystem.Program.FieldReader

public section

namespace GordieHowe.RealizedProgram

/-- Check supplied assignment-read rows using the exact prefix recurrence. These
rows are certificate hints only: neither the runtime program nor its constructors
consume them. The check rejects missing, extra, reordered, or incorrect rows. -/
@[expose] def assignmentReadsB (ir : RealizedProgram) (rows : List (List Nat)) : Bool :=
  memoRowsB (asgStepWith ir (ir.closureT Expr.directNodes)) [] ir.values rows 0 .nil

/-- Assignment-read validation uses the program's shared-expression prefix table. -/
theorem assignmentReadsB_eq (ir : RealizedProgram) (rows : List (List Nat)) :
    assignmentReadsB ir rows =
      memoRowsB (asgStepWith ir (ir.closureT Expr.directNodes)) [] ir.values rows 0 .nil := rfl

/-- The default empty certificate supplies rows only for a program with no values.
Omitting rows for a nonempty program rejects; there is no recomputation fallback. -/
theorem assignmentReadsB_nil (ir : RealizedProgram) :
    assignmentReadsB ir [] = ir.values.isEmpty := by
  rw [assignmentReadsB_eq]
  cases ir.values <;> rfl

/-- Field checks at a reader using supplied assignment rows. Their equivalence
with the canonical reader requires successful `assignmentReadsB`. -/
@[expose] def fieldWithAssignmentReadsB (ir : RealizedProgram) (rows : List (List Nat))
    (domain : Nat) (plan : Export.Plan) (pack : PackingDesc) : Bool :=
  let t := memoRowsTable rows 0 .nil
  let r : FReader := { FReader.ofProgram ir with asgReads := fun v => t.getD v [] }
  @FReader.fieldChecksB ir r domain plan (PackReads.ofDesc pack)

/-- Supplied field reads replace only the canonical assignment-read table. -/
theorem fieldWithAssignmentReadsB_eq (ir : RealizedProgram) (rows : List (List Nat))
    (domain : Nat) (plan : Export.Plan) (pack : PackingDesc) :
    fieldWithAssignmentReadsB ir rows domain plan pack =
      @FReader.fieldChecksB ir
        { FReader.ofProgram ir with
          asgReads := fun v => (memoRowsTable rows 0 .nil).getD v [] }
        domain plan (PackReads.ofDesc pack) := rfl

/-- Domain membership of the supplied assignment reads, with the same out-of-range
behavior as the canonical locality reader. -/
@[expose] def assignmentReadsInB (ir : RealizedProgram) (rows : List (List Nat))
    (d v : Nat) : Bool :=
  decide (v < ir.values.length) &&
    bitTest (failBits (fun _ row => row.all (ir.inDomB d)) rows 0) rows.length true v

/-- Locality checks at the supplied assignment rows. Successful row validation
supplies the equality needed to recover canonical locality. -/
@[expose] def localWithAssignmentReadsB (ir : RealizedProgram) (rows : List (List Nat))
    (ch : Nat → Option Nat) (tree : Nat → List String) : Bool :=
  let r : LReader := { LReader.ofProgram ir tree with
    readsIn := assignmentReadsInB ir rows
    inFlag := fun d => ir.closFlag Expr.directNodes (assignmentReadsInB ir rows d) }
  @LReader.localWithB ir r ch

/-- Supplied locality reads replace only assignment membership and its expression
closure, preserving every other reader field. -/
theorem localWithAssignmentReadsB_eq (ir : RealizedProgram) (rows : List (List Nat))
    (ch : Nat → Option Nat) (tree : Nat → List String) :
    localWithAssignmentReadsB ir rows ch tree =
      @LReader.localWithB ir
        { LReader.ofProgram ir tree with
          readsIn := assignmentReadsInB ir rows
          inFlag := fun d => ir.closFlag Expr.directNodes (assignmentReadsInB ir rows d) }
        ch := rfl

/-- Validate supplied rows once, then run all Fields and Locality consumers with
one shared program context. Invalid rows return false before constructing the
consumer contexts. Every domain in `domains` is checked at its supplied packing
descriptor; the program's own domains determine the locality context as usual. -/
@[expose] def assignmentFactsBC (ir : RealizedProgram) (plan : Export.Plan)
    (records : Structure) (domains : List Nat) (packing : Nat → PackingDesc)
    (tree : Nat → List String) (rows : List (List Nat)) : Bool :=
  let cm := memoAuxL (closureStep Expr.directNodes) [] ir.exprs 0 .nil []
  memoRowsB (asgStepWith ir cm.1) [] ir.values rows 0 .nil &&
    let rl := memoList (readsStepWith cm.1) [] ir.values
    let pc : PCtx := {
      values := ir.values.toArray
      preds := ir.predicates.toArray
      readsL := rl
      reads := rl.toArray
      asgReads := rows.toArray
      nodes := cm.2.toArray }
    let fc : FCtx := {
      base := pc
      pub := (memoList ir.pubStep false ir.values).toArray
      nExprs := ir.exprs.length }
    let lc : LCtx := {
      base := pc
      n := ir.values.length
      m := rows.length
      doms := (List.range ir.domains.length).toArray.map
        (LDomain.build ir tree rows rows.length) }
    allIdx (fun i _ => @FReader.fieldChecksB ir (FReader.ofCtx ir fc) i plan
      (PackReads.ofDesc (packing i))) domains 0 &&
      chalValuesBC ir records &&
      @LReader.localWithB ir (LReader.ofCtx ir tree lc) records.chalOf

/-- When the supplied rows are the recurrence's exact memo list, the shared
compiled context gives the same Fields and Locality checks as their canonical
compiled contexts. This equation does not assume program well-formedness. -/
theorem assignmentFactsBC_eq_of_rows (ir : RealizedProgram) (plan : Export.Plan)
    (records : Structure) (domains : List Nat) (packing : Nat → PackingDesc)
    (tree : Nat → List String) (rows : List (List Nat))
    (hrows : (memoAuxL (asgStepWith ir
      (memoAuxL (closureStep Expr.directNodes) [] ir.exprs 0 .nil []).1)
      [] ir.values 0 .nil []).2 = rows) :
    assignmentFactsBC ir plan records domains packing tree rows =
      (memoRowsB (asgStepWith ir
        (memoAuxL (closureStep Expr.directNodes) [] ir.exprs 0 .nil []).1)
        [] ir.values rows 0 .nil &&
        (allIdx (fun i _ => fieldOkBC ir i plan (packing i)) domains 0 &&
          chalValuesBC ir records && ir.localWithBC records.chalOf tree)) := by
  rw [← hrows]
  rfl

/-- Invalid supplied rows reject the whole shared Fields/Locality check. -/
theorem assignmentFactsBC_eq_false (ir : RealizedProgram) (plan : Export.Plan)
    (records : Structure) (domains : List Nat) (packing : Nat → PackingDesc)
    (tree : Nat → List String) (rows : List (List Nat))
    (hrows : memoRowsB (asgStepWith ir
      (memoAuxL (closureStep Expr.directNodes) [] ir.exprs 0 .nil []).1)
      [] ir.values rows 0 .nil = false) :
    assignmentFactsBC ir plan records domains packing tree rows = false := by
  simp only [assignmentFactsBC, hrows, Bool.false_and]

end GordieHowe.RealizedProgram
