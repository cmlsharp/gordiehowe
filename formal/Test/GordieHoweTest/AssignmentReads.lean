-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.AssignmentReads

public section
namespace GordieHoweTest.AssignmentReads
open GordieHowe GordieHowe.RealizedProgram

/-- Repeated shared references distinguish ordered, duplicate-retaining bound
reads from the prefix-table lists used by public expressions. -/
@[expose] def program : RealizedProgram where
  phases := 0
  fields := []
  domains := []
  exprs := [.add (.leaf 1) (.leaf 0), .add (.ref 0) (.ref 0)]
  values := [
    { name := "first", shape := [1], kind := .priv, type := .field },
    { name := "second", shape := [1], kind := .priv, type := .field },
    { name := "public", shape := [1], kind := .pub (.expr (.ref 0)), type := .field },
    { name := "bound", shape := [1], kind := .bound (.ref 1), type := .field }]
  predicates := []

example : assignmentReadsB program [[0], [1], [1, 0], [1, 0, 1, 0]] = true := by
  decide +kernel
example : assignmentReadsB program [[0], [1], [0, 1], [1, 0, 1, 0]] = false := by
  decide +kernel
example : assignmentReadsB program [[0], [1], [1, 0], [1, 0]] = false := by
  decide +kernel
example : assignmentReadsB program [[0], [1], [1, 0]] = false := by
  decide +kernel
example : assignmentReadsB program [[0], [1], [1, 0], [1, 0, 1, 0], []] = false := by
  decide +kernel

example : assignmentReadsB program [] = false := by decide +kernel
example : assignmentReadsB { program with values := [] } [] = true := by decide +kernel

/-- The checker uses the canonical prefix recurrence even for forward value
references; it does not require a separate well-formedness assumption. -/
@[expose] def forwardProgram : RealizedProgram :=
  { program with values := [
      { name := "forward", shape := [1], kind := .pub (.opaque "view" [1]), type := .field },
      { name := "later", shape := [1], kind := .priv, type := .field }] }

example : assignmentReadsB forwardProgram [[], [1]] = true := by decide +kernel
example : assignmentReadsB forwardProgram [[1], [1]] = false := by decide +kernel

end GordieHoweTest.AssignmentReads
