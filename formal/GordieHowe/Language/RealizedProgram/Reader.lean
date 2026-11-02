-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Check
public import GordieHoweNative.Language.RealizedProgram.Reader

/-!
# GordieHowe: the program reader's lemmas

The kernel's program reader (`PReader.ofProgram`) reads the program's own definitions (its fields,
`ofProgram_*`), and the compiled checkers' reader of a built context equals it
(`PReader.ofCtx_build`): the context's arrays hold the program's values and predicates, and its
reads tables' and closure table's entries are `readsT`'s, `asgReadsT`'s and `closureT`'s
(`getD_memoList`), the closure table read where `nodesOf` reads it (`readsStepWith_closureT`,
`asgStepWith_closureT`).
-/

public section

namespace GordieHowe.RealizedProgram

namespace PReader

variable (ir : RealizedProgram)

@[simp] theorem ofProgram_value : (PReader.ofProgram ir).value = ir.value := rfl

@[simp] theorem ofProgram_predicate : (PReader.ofProgram ir).predicate = ir.predicate := rfl

@[simp] theorem ofProgram_nValues : (PReader.ofProgram ir).nValues = ir.values.length := rfl

@[simp] theorem ofProgram_nPreds : (PReader.ofProgram ir).nPreds = ir.predicates.length := rfl

@[simp] theorem ofProgram_reads (v : ℕ) : (PReader.ofProgram ir).reads v = ir.readsT.getD v [] :=
  rfl

@[simp] theorem ofProgram_readsL : (PReader.ofProgram ir).readsL = ir.readsL := rfl

@[simp] theorem ofProgram_asgReads (v : ℕ) :
    (PReader.ofProgram ir).asgReads v = ir.asgReadsT.getD v [] :=
  rfl

@[simp] theorem ofProgram_nodes (k : ℕ) :
    (PReader.ofProgram ir).nodes k = (ir.closureT Expr.directNodes).getD k [] :=
  rfl

/-- **`IsLate` at the program's reader is the program's.** -/
theorem ofProgram_isLate (v : ℕ) : @PReader.IsLate ir (PReader.ofProgram ir) v ↔ ir.IsLate v :=
  Iff.rfl

/-- **`IsSourceValue` at the program's reader is the program's.** -/
theorem ofProgram_isSourceValue (v : ℕ) :
    @PReader.IsSourceValue (PReader.ofProgram ir) v ↔ ir.IsSourceValue v :=
  Iff.rfl

end PReader

/-- **An array of a list's entries reads as the list.** -/
theorem getD_getElem?_toArray {α : Type} (l : List α) (j : ℕ) (d : α) :
    (l.toArray[j]?).getD d = l.getD j d := by
  rw [List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-- **`readsStepWith` at the closure table is `readsStep`.** -/
theorem readsStepWith_closureT (ir : RealizedProgram) :
    readsStepWith (ir.closureT Expr.directNodes) = ir.readsStep :=
  rfl

/-- **`asgStepWith` at the closure table is `asgStep`.** -/
theorem asgStepWith_closureT (ir : RealizedProgram) :
    asgStepWith ir (ir.closureT Expr.directNodes) = ir.asgStep :=
  rfl

/-- **The compiled checkers' reader of the program's context is the kernel's.** -/
theorem PReader.ofCtx_build (ir : RealizedProgram) :
    PReader.ofCtx (PCtx.build ir) = PReader.ofProgram ir := by
  have hv : (fun v => (ir.values.toArray[v]?).getD default) = ir.value := by
    funext v
    rw [getD_getElem?_toArray, value_eq_getD]
  have hp : (fun p => (ir.predicates.toArray[p]?).getD default) = ir.predicate := by
    funext p
    rw [getD_getElem?_toArray, predicate_eq_getD]
  have hr : (fun v => ((memoList ir.readsStep [] ir.values).toArray[v]?).getD []) =
      fun v => ir.readsT.getD v [] := by
    funext v
    rw [getD_getElem?_toArray]
    exact getD_memoList v
  have ha : (fun v => ((memoList ir.asgStep [] ir.values).toArray[v]?).getD []) =
      fun v => ir.asgReadsT.getD v [] := by
    funext v
    rw [getD_getElem?_toArray]
    exact getD_memoList v
  have hn : (fun k =>
      ((memoAuxL (closureStep Expr.directNodes) [] ir.exprs 0 .nil []).2.toArray[k]?).getD []) =
      fun k => (ir.closureT Expr.directNodes).getD k [] := by
    funext k
    rw [getD_getElem?_toArray]
    exact getD_memoList k
  have hc : (memoAuxL (closureStep Expr.directNodes) [] ir.exprs 0 .nil []).1 =
      ir.closureT Expr.directNodes := rfl
  simp only [PReader.ofCtx, PCtx.build, hc, readsStepWith_closureT, asgStepWith_closureT,
    List.size_toArray, hv, hp, hr, ha, hn]
  rfl

end GordieHowe.RealizedProgram
