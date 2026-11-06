-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.BatchRelation

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Views`

The definitions of `GordieHowe.Language.RealizedProgram.Views` that the certificate checkers run (the leaf tests of a batch on bits), in the
Mathlib-free library `GordieHoweNative`, which Lake compiles to a shared library
(`precompileModules`): native mode runs the checkers as compiled code. The declarations keep their
names. Their lemmas are in `GordieHowe/Language/RealizedProgram/Views.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **A value a bit operand of domain `d` may read**, at its record (`bitsLeafOk_eq`). -/
def bitsLeafV (d : ℕ) (x : Value) : Bool :=
  match x.kind with
  | .priv => x.phase == 0
  | .padCopy _ _ => true
  | .constant _ => true
  | .bits w sel => x.domain == d && (ir.value w).domain == d && (ir.value w).kind.isPriv &&
      decide (0 < sel.size) && x.size == 16 * sel.size
  | .pub .input => x.domain == d
  | .pub (.opaque _ []) => x.domain == d
  | _ => false

/-- **A value of degree one in a bit operand's variables**, at its record (`bitsNd_eq`): every value
but a constant. -/
def bitsNdV (x : Value) : Bool :=
  match x.kind with
  | .constant _ => false
  | _ => true

/-- **The values a bit operand of domain `d` may not read**, as a bit set (`failBits`), for
`bitsLeafB`. -/
def bitsLeafFail (d : ℕ) : ℕ := failBits (fun _ x => ir.bitsLeafV d x) ir.values 0

/-- **`bitsLeafOk`, as a test** (`bitsLeafB_eq`): one `Nat.testBit` of `bitsLeafFail`. -/
def bitsLeafB (d v : ℕ) : Bool :=
  bitTest (ir.bitsLeafFail d) ir.values.length (ir.bitsLeafV d default) v

/-- **The constants**, as a bit set (`failBits`), for `bitsNdB`. -/
def constFail : ℕ := failBits (fun _ x => bitsNdV x) ir.values 0

/-- **`bitsNd`, as a test** (`bitsNdB_eq`): one `Nat.testBit` of `constFail`. -/
def bitsNdB (v : ℕ) : ℕ := cond (bitTest ir.constFail ir.values.length (bitsNdV default) v) 1 0

end

end GordieHowe.RealizedProgram
