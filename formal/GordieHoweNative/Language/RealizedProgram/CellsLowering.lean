-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Locality

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.CellsLowering`

The definitions of `GordieHowe.Language.RealizedProgram.CellsLowering` that the certificate checkers run (the predicates that need a route or a host), in the
Mathlib-free library `GordieHoweNative`, which Lake compiles to a shared library
(`precompileModules`): native mode runs the checkers as compiled code. The declarations keep their
names. Their lemmas are in `GordieHowe/Language/RealizedProgram/CellsLowering.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **Whether a predicate body needs a lowering route** (`Structure.routes`): a field `equal`, a
`mod_0` or a product-form `mod_q`, the predicates `CellsValid.equal` covers. -/
def _root_.GordieHowe.RealizedProgram.PredBody.needsRoute (b : PredBody) : Bool :=
  b.isEqual || b.isIntEq || b.isProductMod

/-- **Whether a predicate body needs its H half hosted by a circuit** (`Structure.macHosts`): a
hosted cross-field `equal` (no `x`-side blind) with no `<mac>.H` predicate. -/
def _root_.GordieHowe.RealizedProgram.PredBody.needsH : PredBody → Bool
  | .cross _ _ _ _ _ real => real.hPredicate.isNone && real.blindX.isNone
  | _ => false

end GordieHowe.RealizedProgram
