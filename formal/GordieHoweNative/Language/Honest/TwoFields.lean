-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Honest.Source

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Honest.TwoFields`

The definitions of `GordieHowe.Language.Honest.TwoFields` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Honest/TwoFields.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
section

variable {ir : RealizedProgram} {primeNodes : ℕ → List String}

/-- **The domains `dx` and `dy` of a MAC's operands have characteristic above `1`.** -/
def MacChars (ir : RealizedProgram) (dx dy : ℕ) : Prop :=
  1 < ir.charOf (ir.domainField dx) ∧ 1 < ir.charOf (ir.domainField dy)

instance (ir : RealizedProgram) (dx dy : ℕ) : Decidable (MacChars ir dx dy) := by
  unfold MacChars; infer_instance

end

end GordieHowe.RealizedProgram
