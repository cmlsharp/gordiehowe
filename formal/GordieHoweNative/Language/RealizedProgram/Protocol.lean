-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Source

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Protocol`

The definitions of `GordieHowe.Language.RealizedProgram.Protocol` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/Protocol.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
section

variable (ir : RealizedProgram)

/-- **A challenge of a phase the program has** (`1 ≤ phase ≤ phases`), a challenge of the layout. -/
def IsPhaseChal (j : ℕ) : Prop :=
  j < ir.challenges.length ∧ 1 ≤ (ir.challenge j).phase ∧ (ir.challenge j).phase ≤ ir.phases

instance (j : ℕ) : Decidable (ir.IsPhaseChal j) := by unfold IsPhaseChal; infer_instance

end

section

variable {ir : RealizedProgram}

/-- **Challenge `j'` is drawn no later than challenge `j`**: of an earlier phase, or of the same
phase and declared no later. -/
def ChalBefore (j' j : ℕ) : Prop :=
  (ir.challenge j').phase < (ir.challenge j).phase ∨
    ((ir.challenge j').phase = (ir.challenge j).phase ∧ j' ≤ j)

end

end GordieHowe.RealizedProgram
