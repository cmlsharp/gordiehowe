-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Std

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Foundations.Fields.BinarySpread`

The executable parameters of a spread representation of a binary field (`Exec`) and its
arithmetic, in the Mathlib-free library `GordieHoweNative`. The declarations keep their names;
their lemmas are in `GordieHowe/Foundations/Fields/BinarySpread.lean`, which imports this module.
-/

@[expose] public section

namespace GordieHowe.BinarySpread

/-- The executable parameters: digit width `k`, degree `n`, the natural `tapN` whose
digits are the low coefficients of `f`, and the parity mask `mask` (one in the lowest bit
of each of the `n` digits). -/
structure Exec where
  k : Nat
  n : Nat
  tapN : Nat
  mask : Nat

namespace Exec

variable (E : Exec)

/-- Replace the digits from position `n` on, `H`, by `H * tap`. -/
def fold (N : Nat) : Nat := N % 2 ^ (E.k * E.n) + N / 2 ^ (E.k * E.n) * E.tapN

/-- Multiplication: integer product, two folds, parity of each digit. -/
def mul (a b : Nat) : Nat := E.fold (E.fold (a * b)) &&& E.mask

/-- Addition: integer sum, parity of each digit. -/
def add (a b : Nat) : Nat := (a + b) &&& E.mask

/-- `r ^ (2 ^ j)`, by `j` squarings. -/
def sqPow : Nat → Nat → Nat
  | 0, r => r
  | j + 1, r => sqPow j (E.mul r r)

/-- `b ^ e` for `e < 2 ^ j`, by square-and-multiply over the `j` low bits of `e`. -/
def pow : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | j + 1, e, b =>
    if e % 2 = 1 then E.mul b (pow j (e / 2) (E.mul b b)) else pow j (e / 2) (E.mul b b)

/-- The `i` low bits of `v`, bit `j` moved to bit `k * j`. -/
def spread : Nat → Nat → Nat
  | 0, _ => 0
  | i + 1, v => v % 2 + 2 ^ E.k * spread i (v / 2)

/-- The representation of the element with polynomial-basis coordinates the bits of `v`. -/
def ofBits (v : Nat) : Nat := E.spread E.n v

/-- The sum of `g 0, …, g (m - 1)`. -/
def sum : (m : Nat) → (Fin m → Nat) → Nat
  | 0, _ => 0
  | m + 1, g => E.add (g 0) (sum m fun j => g j.succ)

/-- `trace s m y = ∑_{j < m} y ^ (2 ^ (s * j))`. -/
def trace (s : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, y => E.add y (trace s m (E.sqPow s y))

end Exec

end GordieHowe.BinarySpread
