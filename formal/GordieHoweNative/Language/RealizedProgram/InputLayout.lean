-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.InputLayout`

The definitions of `GordieHowe.Language.RealizedProgram.InputLayout` that the field checks run (the circuits' private block), in the
Mathlib-free library `GordieHoweNative`, which Lake compiles to a shared library
(`precompileModules`): native mode runs the checkers as compiled code. The declarations keep their
names. Their lemmas are in `GordieHowe/Language/RealizedProgram/InputLayout.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **The inputs of circuit `c` holding batch pads**: the lengths of its batch-pad blocks. -/
def batchPadInputs (c : ℕ) : ℕ :=
  ((ir.circuit c).inputs.map fun b => match b with
    | .batchPads _ _ n => n
    | _ => 0).sum

/-- **The end of circuit `c`'s private block**: the input count less the batch-pad inputs. The C++
allocates a batch's pads as the circuit's last inputs, which no gate reads; the Lean commits them at
full-field cells beside the circuit's input, so the private block ends before them. -/
abbrev privEnd (c : ℕ) : ℕ := (ir.circuit c).inputCount - ir.batchPadInputs c

end

end GordieHowe.RealizedProgram
