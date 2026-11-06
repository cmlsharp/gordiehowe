-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Init
public meta import Lean.LabelAttribute
public import Lean.LabelAttribute
public import Lean.Meta.Tactic.Simp

/-!
# GordieHowe: the simp set of a program's checked reads

Lean cannot use an attribute in the file that declares it, so the simp set lives here and
`GordieHowe/Language/RealizedProgram/ShapeReads.lean` states the tactic that uses it.
-/

public meta section

/-- A rewrite of one part of a generated program, from a checked shape fact. Each rewrite names its
program, so the set of one program never fires on another. -/
register_simp_attr shape_reads
