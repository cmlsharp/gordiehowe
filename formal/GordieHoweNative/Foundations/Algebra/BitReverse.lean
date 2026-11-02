-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Std

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Foundations.Algebra.BitReverse`

The definitions of `GordieHowe.Foundations.Algebra.BitReverse` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Foundations/Algebra/BitReverse.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe

/-- Reverse the low `m` bits of `k`: the lowest bit becomes bit `m - 1`. -/
def bitRevNat : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, k => k % 2 * 2 ^ m + bitRevNat m (k / 2)

end GordieHowe
