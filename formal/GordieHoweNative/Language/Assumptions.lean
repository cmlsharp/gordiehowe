-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Realized

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Assumptions`

The definitions of `GordieHowe.Language.Assumptions` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Assumptions.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **The field of circuit `c`**: its domain's. -/
abbrev circField (c : ℕ) : ℕ := ir.domainField (ir.circuit c).domain

end

end GordieHowe.RealizedProgram
