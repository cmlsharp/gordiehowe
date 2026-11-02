-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.RealizeLookup

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.RealizeMac`

The definitions of `GordieHowe.Language.Realizations.RealizeMac` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/RealizeMac.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
section

variable {ir : RealizedProgram} {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

variable (ir) in
/-- **`MacHostedCore` as a Boolean.** -/
def macHostedCoreB (pid dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr) (k : CrossKind)
    (real : MacRealization) : Bool :=
  decide (k.width = 1) && decide (0 < real.width) && decide (real.macField < ir.fields.length) &&
    decide (ir.domainField dx = real.macField) && ir.macKeyB pid real && ir.macTagB real &&
    decide (ir.exprLen x ≤ real.chunks * real.width) &&
    decide (ir.exprLen y = ir.exprLen x) && ir.macReadsBeforeB x y real &&
    decide (2 < ir.charOf (ir.domainField dy)) && ir.macHalfB pid dx x real &&
    decide (real.blindX = none)

variable (ir) in
/-- **`MacTwoCore` as a Boolean.** -/
def macTwoCoreB (pid : ℕ) (x y : Expr) (k : CrossKind) (real : MacRealization) : Bool :=
  decide (k.width = 1) && decide (0 < real.width) && decide (real.macField < ir.fields.length) &&
    ir.macKeyB pid real && ir.macTagB real && decide (real.hPredicate = none) &&
    decide (ir.exprLen x = real.chunks * real.width) &&
    decide (ir.exprLen y = real.chunks * real.width) && ir.macReadsBeforeB x y real

end

end GordieHowe.RealizedProgram
