-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Field.Defs

@[expose] public section

/-!
# Bit-wire vectors

`BitWires K n` names a vector of field wires intended to represent bits.
The name does not constrain its values: raw committed witnesses are adversarial.
`Bits.AllBool` is the separate proposition established by Booleanity constraints
or hash-gadget soundness, and consumed by bit-operation semantics lemmas.
-/

namespace GordieHowe

/-- Field wires intended to encode `n` bits, without assuming Booleanity. -/
abbrev BitWires (K : Type*) (n : ℕ) := Fin n → K

end GordieHowe
