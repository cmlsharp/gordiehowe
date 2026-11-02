-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Honest.Digits

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Honest.Packed`

The definitions of `GordieHowe.Language.Honest.Packed` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Honest/Packed.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

section

variable {ir : RealizedProgram}

/-- **The rows of a packed expression** of `n` records of `A` columns, packed at the coordinates
of value `P`: row `j` is `[(A j + c, node P c) | c < A]`. -/
def packRows (A P n : ℕ) : List (List (ℕ × Coef)) :=
  (List.range n).map fun j => (List.range A).map fun c => (A * j + c, Coef.node P c)

/-- **An expression packed at the coordinates of a value** (`packRows`): `linear rows b` with
records of `A ≥ 2` columns at the value `P`, read off its first coefficient; the powers' value
`P`, the arity `A` and the records' expression `b`. -/
def packOf? : Expr → Option (ℕ × ℕ × Expr)
  | .linear rows b =>
    match rows with
    | ((_, .node P _) :: r0) :: _ =>
      if 2 ≤ r0.length + 1 ∧ rows = packRows (r0.length + 1) P rows.length then
        some (P, r0.length + 1, b)
      else none
    | _ => none
  | _ => none

variable (ir) in
/-- **Table `t` is packed at a value**: its rows are a packed expression (`packOf?`). -/
def gammaPack? (t : ℕ) : Option (ℕ × ℕ × Expr) :=
  match (ir.table t).rows with
  | .expr e' => packOf? e'
  | _ => none

variable (ir) in
/-- **The records' expression of member `m`'s needle** packed at the value `P` with `A` columns,
when its needle is one. -/
def memberBase? (P A : ℕ) (m : Member) : Option Expr :=
  match packOf? (ir.needleExpr m.pred m.needle) with
  | some (P', A', b) => if P' = P ∧ A' = A then some b else none
  | none => none

end

end GordieHowe.RealizedProgram
