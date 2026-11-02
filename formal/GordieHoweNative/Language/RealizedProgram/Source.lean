-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Check

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Source`

The definitions of `GordieHowe.Language.RealizedProgram.Source` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/Source.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **A value of the source program**: a value of role `source`. -/
def IsSourceValue (v : ℕ) : Prop := (ir.value v).role = .source

instance (v : ℕ) : Decidable (ir.IsSourceValue v) := inferInstanceAs (Decidable (_ = _))

/-- **A predicate of the source program**: of role `source`, or the type check of a source
value. -/
def inSource (p : Predicate) : Bool :=
  match p.role with
  | .source => true
  | .type v => decide (ir.IsSourceValue v)
  | .realization _ => false

end

end GordieHowe.RealizedProgram
