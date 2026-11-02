-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Std

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Export`

The definitions of `GordieHowe.Language.Export` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Export.lean`, which imports this module.
-/

@[expose] public section

namespace GordieHowe.RealizedProgram.Export

/-- **A placement target** (`placement.h`, `Placement`): where a predicate group is realized. -/
inductive PlacementTarget where
  /-- As affine rows of the commitment. -/
  | affine
  /-- As quadratic triples of the commitment. -/
  | quadratic
  /-- In a batch of the domain (`Placement.batch` names it). -/
  | batch
  /-- As constraints of the domain's GKR circuit. -/
  | circuit
  deriving Repr, DecidableEq

/-- **A placed predicate group** (`plan_export.h`, `DomainPlan::Placed`): its name, its target, the
number of same-shaped predicates merged into it, its instances and, for a batch target, the batch.
The program's per-predicate targets (`RealizedProgram.TargetsAdmit`) subsume it. -/
structure Placement where
  /-- The group's name. -/
  name : String
  /-- The target. -/
  target : PlacementTarget
  /-- The predicates merged into the group (the export omits `1`). -/
  predicates : Nat := 1
  /-- The instances. -/
  instances : Nat
  /-- The batch, for a batch target (`""` otherwise). -/
  batch : String := ""
  deriving Repr, DecidableEq

end GordieHowe.RealizedProgram.Export
