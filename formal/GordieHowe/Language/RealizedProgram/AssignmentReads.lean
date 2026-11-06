-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Reader
public import GordieHowe.Language.RealizedProgram.LocalityReader
public import GordieHowe.Language.RealizedProgram.MemoRows
public import GordieHoweNative.Language.RealizedProgram.AssignmentReads

public section

namespace GordieHowe.RealizedProgram

/-- Checked assignment-read rows equal the canonical list exactly, for every
program, without an acyclicity or well-formedness assumption. -/
theorem assignmentReadsB_sound (ir : RealizedProgram) (rows : List (List Nat))
    (h : assignmentReadsB ir rows = true) : ir.asgReadsL = rows := by
  rw [assignmentReadsB_eq] at h
  have hl := memoRowsB_soundList (asgStepWith ir (ir.closureT Expr.directNodes)) []
    ir.values rows 0 .nil [] h
  rw [asgReadsL_eq_memoList, memoList_eq_aux]
  simpa only [asgStepWith_closureT, List.reverse_nil, List.nil_append] using hl

/-- The table built from checked rows is the canonical assignment-read table. -/
theorem assignmentReadsB_table (ir : RealizedProgram) (rows : List (List Nat))
    (h : assignmentReadsB ir rows = true) : memoRowsTable rows 0 .nil = ir.asgReadsT := by
  rw [assignmentReadsB_eq] at h
  have ht := memoRowsB_sound (asgStepWith ir (ir.closureT Expr.directNodes)) []
    ir.values rows 0 .nil h
  rw [asgReadsT_eq_memo, memo_eq]
  simpa only [asgStepWith_closureT] using ht.symm

/-- The exact canonical assignment-read rows always pass validation. -/
theorem assignmentReadsB_complete (ir : RealizedProgram) :
    assignmentReadsB ir ir.asgReadsL = true := by
  rw [assignmentReadsB_eq, asgReadsL_eq_memoList, memoList_eq_aux, asgStepWith_closureT]
  exact memoRowsB_complete ir.asgStep [] ir.values 0 .nil

/-- Successfully checked rows preserve the complete descriptor field check. -/
theorem fieldWithAssignmentReadsB_eq_canonical (ir : RealizedProgram)
    (rows : List (List Nat)) (domain : Nat) (plan : Export.Plan) (pack : PackingDesc)
    (h : assignmentReadsB ir rows = true) :
    fieldWithAssignmentReadsB ir rows domain plan pack = ir.fieldOkBD domain plan pack := by
  rw [fieldWithAssignmentReadsB_eq, assignmentReadsB_table ir rows h]
  rfl

/-- Successfully checked rows preserve assignment-domain membership, including
the default result for out-of-range assignment indices. -/
theorem assignmentReadsInB_eq_canonical (ir : RealizedProgram) (rows : List (List Nat))
    (h : assignmentReadsB ir rows = true) : assignmentReadsInB ir rows = ir.readsInB := by
  rw [← assignmentReadsB_sound ir rows h]
  rfl

/-- Successfully checked rows preserve the complete locality check. -/
theorem localWithAssignmentReadsB_eq_canonical (ir : RealizedProgram)
    (rows : List (List Nat)) (ch : Nat → Option Nat) (tree : Nat → List String)
    (h : assignmentReadsB ir rows = true) :
    localWithAssignmentReadsB ir rows ch tree = ir.localWithB ch tree := by
  rw [localWithAssignmentReadsB_eq, assignmentReadsInB_eq_canonical ir rows h]
  rfl

/-- The shared compiled check is exactly one row-validity guard conjoined with
all canonical Fields/Locality consumers, including rejection for arbitrary invalid
rows. There is no acyclicity, well-formedness, or backward-reference premise. -/
theorem assignmentFactsBC_eq (ir : RealizedProgram) (plan : Export.Plan)
    (records : Structure) (domains : List Nat) (packing : Nat → PackingDesc)
    (tree : Nat → List String) (rows : List (List Nat)) :
    assignmentFactsBC ir plan records domains packing tree rows =
      (assignmentReadsB ir rows &&
        (allIdx (fun i _ => fieldOkBC ir i plan (packing i)) domains 0 &&
          chalValuesBC ir records && ir.localWithBC records.chalOf tree)) := by
  have ht : (memoAuxL (closureStep Expr.directNodes) [] ir.exprs 0 .nil []).1 =
      ir.closureT Expr.directNodes := by
    rw [memoAuxL_fst, closureT_eq_memo, memo_eq]
  rw [assignmentReadsB_eq, ← ht]
  let F := asgStepWith ir (memoAuxL (closureStep Expr.directNodes) [] ir.exprs 0 .nil []).1
  by_cases h : memoRowsB F [] ir.values rows 0 .nil = true
  · have hr := memoRowsB_soundList F [] ir.values rows 0 .nil [] h
    simp only [List.reverse_nil, List.nil_append] at hr
    exact assignmentFactsBC_eq_of_rows ir plan records domains packing tree rows hr
  · have hf : memoRowsB F [] ir.values rows 0 .nil = false := by
      cases he : memoRowsB F [] ir.values rows 0 .nil <;> simp_all
    rw [assignmentFactsBC_eq_false ir plan records domains packing tree rows hf, hf]
    rfl

end GordieHowe.RealizedProgram
