-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Cells
public import GordieHoweNative.Language.RealizedProgram.StructureCheck

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Library.Eval`

The definitions of `GordieHowe.Language.Library.Eval` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Library/Eval.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
section

variable {ir : RealizedProgram}

/-- **The entries of a constant value** (none for a value of another kind). -/
def constEntries (v : ℕ) : List ℕ :=
  match (ir.value v).kind with
  | .constant es => es
  | _ => []

/-- **Whether value `v` is a constant.** -/
def isConstant (v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .constant _ => true
  | _ => false

end

end GordieHowe.RealizedProgram
