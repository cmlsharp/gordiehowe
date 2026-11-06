-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.ShapeReadsAttr
public import GordieHowe.Language.Library.Eval
public import GordieHowe.Language.Library.Cross
public import GordieHowe.Language.Honest.Source

/-!
# GordieHowe: closed goals over a program's checked reads

A frontend's finite facts read parts of its program: sizes, fields, constants, shared expressions.
`shape_decide` rewrites those parts with the program's checked reads (`shape_reads`) and decides the
closed goal left, which reads no program table.
-/

public section

/-- Rewrite a program's parts with its checked reads, then decide the closed goal left. -/
macro "shape_decide" : tactic =>
  `(tactic| (simp only [shape_reads,
    GordieHowe.RealizedProgram.constEntries, GordieHowe.RealizedProgram.isConstant,
    GordieHowe.RealizedProgram.isBitView, GordieHowe.RealizedProgram.isBitsB,
    GordieHowe.RealizedProgram.exprLen_leaf, GordieHowe.RealizedProgram.exprLen_add,
    GordieHowe.RealizedProgram.exprLen_sub, GordieHowe.RealizedProgram.exprLen_mul,
    GordieHowe.RealizedProgram.exprLen_scale, GordieHowe.RealizedProgram.exprLen_reindex,
    GordieHowe.RealizedProgram.exprLen_concat, GordieHowe.RealizedProgram.exprLen_prod,
    GordieHowe.RealizedProgram.exprLen_mux, GordieHowe.RealizedProgram.exprLen_logic_cons,
    GordieHowe.RealizedProgram.exprLen_apply, GordieHowe.RealizedProgram.NamedOp.cols,
    GordieHowe.RealizedProgram.NamedOp.rows,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_imp_iff,
    implies_true, and_true, true_and, and_self] <;> decide +kernel))
