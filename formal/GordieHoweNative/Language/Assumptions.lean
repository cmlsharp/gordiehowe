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

section

variable (ir : RealizedProgram)

/-- **Value `v` reads nothing of the committed assignment**, with `n` levels (as `RealizedProgram.read`): a
statement value, a constant, a challenge value, a message of a late value, an opaque value or a
public expression reading only such values. -/
def pubB : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, v =>
    match (ir.value v).kind with
    | .pub .input => true
    | .pub (.opaque _ args) => args.all (pubB n)
    | .pub (.expr x) => (ir.exprNodes x).all (pubB n)
    | .constant _ => true
    | .challenge _ => true
    | .message u => decide (u < ir.values.length ∧ ir.IsLate u)
    | _ => false

end

end GordieHowe.RealizedProgram
