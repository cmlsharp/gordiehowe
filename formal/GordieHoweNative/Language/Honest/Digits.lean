-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Honest.TwoFields

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Honest.Digits`

The definitions of `GordieHowe.Language.Honest.Digits` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Honest/Digits.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
section

variable {ir : RealizedProgram} {primeNodes : ℕ → List String}

variable (ir) in
/-- **The values the rows of table `t` read** (`tableRow`): none for a range, the first column for
a committed table, the expression's values for a table of an expression's coordinates. -/
def tableRowReads (t : ℕ) : List ℕ :=
  match (ir.table t).rows with
  | .range _ => []
  | .columns cols => [cols.headD 0]
  | .expr e' => ir.exprNodes e'

variable (ir) in
/-- **`DigitsMac.topRoom`, as a check**: every lookup of a single record `D` with `D.beq top` into
a range `[0, N)` is of domain `dy` with `m < N`. -/
def topRoomB (top : Expr) (dy m : ℕ) : Bool :=
  ir.predicates.all fun p =>
    match p.body with
    | .mem d [D] (.range N) (.lookup _) => !(D.beq top) || (d == dy && decide (m < N))
    | _ => true

variable (ir) in
/-- **`DigitsMac.wrapRoom`, as a check**: every membership of a single record `D` with `D.beq W`
in a range `[0, N)` is of domain `dy` with `m < N`. -/
def wrapRoomB (W : Expr) (dy m : ℕ) : Bool :=
  ir.predicates.all fun p =>
    match p.body with
    | .mem d [D] (.range N) _ => !(D.beq W) || (d == dy && decide (m < N))
    | _ => true

end

end GordieHowe.RealizedProgram
