-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.ProofSystem.GKR.Codes
public import GordieHoweNative.Foundations.Fields.BinarySpread

/-!
# GordieHowe: the compiled definitions of `GordieHowe.ProofSystem.GKR.FieldCodes`

The code arithmetic of the fields' encodings: modulo a prime (`primeArith`), of a binomial
extension over a base code arithmetic (`ExtCode`, `ExtCode.overPrime`), of a binary field by
spread naturals (`BinCode`), and the fast path at a prime subfield (`CodeArith.withPrime`), in
the Mathlib-free library `GordieHoweNative`. The declarations keep their names; their lemmas are
in `GordieHowe/ProofSystem/GKR/FieldCodes.lean`, which imports this module.
-/

@[expose] public section

namespace GordieHowe.GKR.Fold

/-- **The code arithmetic modulo `p`**: the sum and the product of the naturals, reduced modulo
`p`. -/
def primeArith (p : Nat) : CodeArith where
  add a b := (a + b) % p
  mul a b := a * b % p

/-- **Digit `i` of `c` in base `2^s`**: bits `s i` to `s i + s - 1` of `c`. -/
def digit (s c i : Nat) : Nat := c / 2 ^ (s * i) % 2 ^ s

/-- **The natural with digits `g 0, …, g (n - 1)` in base `2^s`**: `Σ_{i<n} g i · 2^(s i)`. -/
def undigits (s : Nat) (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => undigits s g n + g n * 2 ^ (s * n)

/-- **The code arithmetic of an extension `K[X] / (X^n - β)`** over a base code arithmetic, codes
read as coefficient vectors (`extDecode`): `n` coefficients of `s` bits, `beta` the code of `β`. -/
structure ExtCode where
  /-- The code arithmetic of the base field `K`. -/
  base : CodeArith
  /-- The bits per coefficient. -/
  s : Nat
  /-- The degree `n`. -/
  n : Nat
  /-- The code of `β`, with `X^n = β`. -/
  beta : Nat

namespace ExtCode

variable (E : ExtCode)

/-- The code of the sum: the coefficientwise sums. -/
def add (a b : Nat) : Nat :=
  undigits E.s (fun i => E.base.add (digit E.s a i) (digit E.s b i)) E.n

/-- Coefficient `i` of `X · acc + b_j · a` (`PolyRep.mulStep`): coefficient `i - 1` of `acc`, or
`β` times its top coefficient at `i = 0`, plus `b_j a_i`. -/
def stepDigit (a b j acc i : Nat) : Nat :=
  E.base.add (if i = 0 then E.base.mul E.beta (digit E.s acc (E.n - 1)) else digit E.s acc (i - 1))
    (E.base.mul (digit E.s b j) (digit E.s a i))

/-- One step of Horner's rule: the code of `X · acc + b_j · a`. -/
def step (a b j acc : Nat) : Nat := undigits E.s (E.stepDigit a b j acc) E.n

/-- The code of the product: Horner's rule on the coefficients of `b` from `X^(n-1)` down to `X^0`
(`PolyRep.mul`). -/
def mul (a b : Nat) : Nat := (List.range E.n).foldr (E.step a b) 0

/-- **The code arithmetic of the extension.** -/
def arith : CodeArith where
  add := E.add
  mul := E.mul

/-- **The code arithmetic of a binomial extension of `ZMod p`**: `n` coefficients of `s` bits, the
arithmetic modulo `p` on each, `X^n = β` with `beta` the code of `β`. -/
def overPrime (p s n beta : Nat) : ExtCode := ⟨primeArith p, s, n, beta⟩

end ExtCode

open BinarySpread

/-- **A binary field's code arithmetic**: the spread representation `E` (digits of `E.k` bits, `E.n`
of them) and the repetition constant `rep = Σ_{i < n} 2^((k-1) i)` (`Nat.ones (k - 1) n`), kept as
data so the kernel does not recompute it. -/
structure BinCode where
  /-- The spread representation. -/
  E : Exec
  /-- `Nat.ones (E.k - 1) E.n`. -/
  rep : Nat

/-- The spread representation of the `n` low bits of `v`: `v` repeated every `k - 1` bits, bit `j`
of the `j`-th copy kept. -/
def BinCode.spread (B : BinCode) (v : Nat) : Nat := (v % 2 ^ B.E.n * B.rep) &&& B.E.mask

/-- The code of a spread natural: its remainder modulo `2^(k-1) - 1`. -/
def BinCode.unspread (B : BinCode) (N : Nat) : Nat := N % (2 ^ (B.E.k - 1) - 1)

/-- **The code arithmetic of a binary field**: exclusive or, and the spread product. -/
def BinCode.arith (B : BinCode) : CodeArith where
  add a b := a ^^^ b
  mul a b := B.unspread (B.E.mul (B.spread a) (B.spread b))

/-- **The arithmetic with the fast path**: codes below `p` by arithmetic modulo `p`, any other pair
by `ar`. -/
def CodeArith.withPrime (ar : CodeArith) (p : Nat) : CodeArith where
  add a b := cond (Nat.blt a p && Nat.blt b p) ((a + b) % p) (ar.add a b)
  mul a b := cond (Nat.blt a p && Nat.blt b p) (a * b % p) (ar.mul a b)

end GordieHowe.GKR.Fold
