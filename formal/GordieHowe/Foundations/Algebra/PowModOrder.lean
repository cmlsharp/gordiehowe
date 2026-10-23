-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.PowMod

@[expose] public section

/-!
# Transporting a `powMod` value of `p - 1` to `-1` in `ZMod p`

`GordieHowe.Foundations.Algebra.PowMod` transports a `powMod` value of `1` (`powMod_eq_one_of_eq`) or a value other than
`1` (`powMod_ne_one_of_ne`) to a fact about `ZMod` exponentiation. An order-of-unity certificate
built from `IsPrimitiveRoot.of_pow_two_pow_eq_neg_one` needs the `ZMod p` value `-1` itself, which
is `((p - 1 : ℕ) : ZMod p)` for `1 ≤ p`.
-/

namespace GordieHowe

/-- A `powMod` value of exactly `p - 1` transports to a `ZMod` fact of `-1`. -/
theorem powMod_eq_neg_one_of_eq {b e p : ℕ} (hp : 1 ≤ p) (h : powMod b e p = p - 1) :
    (b : ZMod p) ^ e = -1 := by
  rw [← powMod_eq_pow, h, Nat.cast_sub hp, Nat.cast_one, ZMod.natCast_self, zero_sub]

end GordieHowe
