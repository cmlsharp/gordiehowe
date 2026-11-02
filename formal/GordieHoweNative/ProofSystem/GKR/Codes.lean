-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.ProofSystem.GKR.Certificate

/-!
# GordieHowe: the compiled definitions of `GordieHowe.ProofSystem.GKR.Codes`

The definitions of `GordieHowe.ProofSystem.GKR.Codes` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/ProofSystem/GKR/Codes.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.GKR.Fold

open GordieHowe.GKR.Certificate

/-- **Arithmetic on the codes of a field**: computable addition and multiplication of the natural
numbers that encode field elements (the C++ `to_bytes_field` bytes, read as a natural). -/
structure CodeArith where
  /-- The code of the sum. -/
  add : ℕ → ℕ → ℕ
  /-- The code of the product. -/
  mul : ℕ → ℕ → ℕ

/-- The code of constant `i`. -/
def Consts.code (Kc : Consts) (i : ℕ) : ℕ := cell Kc.width Kc.table i

/-- The product of two codes, without the field's multiplication when a factor is `0` or `1`. -/
def cmul (ar : CodeArith) (a b : ℕ) : ℕ :=
  cond (Nat.beq a 0 || Nat.beq b 0) 0 (cond (Nat.beq a 1) b (cond (Nat.beq b 1) a (ar.mul a b)))

/-- The elements of `ys` before the first one at least `x`. -/
def dropLt (x : ℕ) : List ℕ → List ℕ
  | [] => []
  | y :: ys => cond (Nat.blt y x) (dropLt x ys) (y :: ys)

/-- Every element of the increasing list `xs` is in the increasing list `ys` (a merge-join). -/
def subsetSorted : List ℕ → List ℕ → Bool
  | [], _ => true
  | x :: xs, ys =>
    match dropLt x ys with
    | y :: ys' => Nat.beq x y && subsetSorted xs (y :: ys')
    | [] => false

end GordieHowe.GKR.Fold
