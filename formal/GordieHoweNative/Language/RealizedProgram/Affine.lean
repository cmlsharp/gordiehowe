-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Check

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Affine`

The definitions of `GordieHowe.Language.RealizedProgram.Affine` that the certificate checkers run (the sides of a row), in the
Mathlib-free library `GordieHoweNative`, which Lake compiles to a shared library
(`precompileModules`): native mode runs the checkers as compiled code. The declarations keep their
names. Their lemmas are in `GordieHowe/Language/RealizedProgram/Affine.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **The sides of a predicate of domain `d` with target `affine`**: a field `equal`'s, or a
`mod_0`'s field equation's. -/
def PredBody.rowSides (b : PredBody) (d : ℕ) : Option (Expr × Expr) :=
  match b with
  | .equal d' e e' .affine => if d' = d then some (e, e') else none
  | .mod d' 0 e e' real => if d' = d ∧ real.target = some .affine then some (e, e') else none
  | _ => none

section

variable (ir : RealizedProgram)

/-- **A sum of constant multiples of committed values and constants**: a committed value, a
constant, a sum, or a constant multiple. Its values are affine in the cells
(`RealizedProgram.isAff_evalE_linPriv`). -/
def linPrivB : Expr → Bool
  | .leaf u =>
    match (ir.value u).kind with
    | .priv => true
    | .constant _ => true
    | _ => false
  | .add a b => linPrivB a && linPrivB b
  | .scale (.const _) a => linPrivB a
  | _ => false

end

section

variable (ir : RealizedProgram)

/-- **The step of `pubT`**: whether value `v` reads nothing of the committed assignment, from
whether the values it reads do (`r`; the step of `pubB`). -/
def pubStep (r : ℕ → Bool) (_ : ℕ) (x : Value) : Bool :=
  match x.kind with
  | .pub .input => true
  | .pub (.opaque _ args) => args.all r
  | .pub (.expr e) => (ir.nodesOf e).all r
  | .constant _ => true
  | .challenge _ => true
  | .message u => decide (u < ir.values.length ∧ ir.IsLate u)
  | _ => false

/-- **The table of the values reading nothing of the committed assignment** (`pubB`), one entry
per value. -/
def pubT : NatTrie Bool := memo ir.pubStep false ir.values

end

end GordieHowe.RealizedProgram
