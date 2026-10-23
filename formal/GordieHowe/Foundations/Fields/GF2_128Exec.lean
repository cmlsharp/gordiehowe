-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.BinaryRep

@[expose] public section

/-!
# Executable `GF(2¹²⁸)` arithmetic

`gfMul` is multiplication in `GF(2¹²⁸)` on `BitVec 128`, bit `i` holding the coefficient of
`X^i` (the polynomial-basis order `GordieHowe.Conv` uses, the reverse of the bit-reflected convention
GCM's `0x87` reduction constant is usually quoted in): the shift-and-add multiplication of
`GordieHowe.Foundations.Fields.BinaryRep` with the reduction `X¹²⁸ = X⁷ + X² + X + 1`, i.e. `0x87`.

`GordieHowe.Foundations.Fields.GF2_128` builds the field `GF2_128` on `BitVec 128` with `gfMul` as its multiplication,
and checks the irreducibility certificate for the reduction polynomial with `sqPow` and `gfMul`.
`Test/PQTest/FieldEvals.lean` checks `gfMul` against `Conv.ConvBasis.conv_parity` by evaluation.
-/

namespace GordieHowe.GF2_128Exec

/-- Carry-less multiplication in `GF(2¹²⁸)`, bit `i` the coefficient of `X^i`: Horner's rule on
`b`'s bits from `127` down to `0`, reducing by `X¹²⁸ = X⁷ + X² + X + 1` (`0x87`). -/
def gfMul (a b : BitVec 128) : BitVec 128 := BinaryRep.mul 0x87#128 a b

/-- `r ^ (2 ^ n)` in `GF(2¹²⁸)`, by `n` squarings. -/
def sqPow : ℕ → BitVec 128 → BitVec 128
  | 0, r => r
  | n + 1, r => sqPow n (gfMul r r)

/-- `b ^ n` for `n < 2 ^ k`, by square-and-multiply over the `k` low bits of `n`. -/
def gfPow : ℕ → ℕ → BitVec 128 → BitVec 128
  | 0, _, _ => 1
  | k + 1, n, b =>
    if n % 2 = 1 then gfMul b (gfPow k (n / 2) (gfMul b b)) else gfPow k (n / 2) (gfMul b b)

end GordieHowe.GF2_128Exec
