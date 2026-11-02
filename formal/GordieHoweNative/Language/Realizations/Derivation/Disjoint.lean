-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.Basic

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.Disjoint`

The definitions of `GordieHowe.Language.Realizations.Derivation.Disjoint` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/Disjoint.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **The coordinates where a sum of masked views may be nonzero**: a masked view
`reindex m (concat A (leaf z))`, `z` a constant holding `0` and `A` any expression of length `n`
at the lengths `rl`, is nonzero only where its entry reads `A` (`mapNz n`); a sum of two such sums
only on the union of theirs, when the two are disjoint (`disjointNz`). As `maskedNz`, with any
first operand of the concatenation. -/
def maskSupp (rl : ℕ → ℕ) : Expr → Option (List (ℕ × ℕ))
  | .reindex m (.concat A (.leaf z)) =>
    if ir.zeroConstB z then some (mapNz (Expr.len ir rl A) 0 m) else none
  | .add e e' =>
    match maskSupp rl e, maskSupp rl e' with
    | some L, some L' => if disjointNz L L' then some (L ++ L') else none
    | _, _ => none
  | _ => none

/-- **`ivlDisjoint a b`** in domain `d`: from `ivl d x lo hi` (`a`) and `ivl d y lo' hi'` (`b`), `x`
and `y` of one length and well-formed shape, masked views of disjoint supports: `ivl d (x + y)
(min lo lo') (max hi hi')`. -/
def ivlDisjointFact (fs : List Fact) (d a b : ℕ) : Option Fact :=
  match fs[a]?, fs[b]? with
  | some (.ivl d₁ x lo hi), some (.ivl d₂ y lo' hi') =>
    if d₁ = d ∧ d₂ = d ∧ ir.exprLen x = ir.exprLen y ∧ ir.exprShapeOk x = true ∧
        ir.exprShapeOk y = true ∧ (ir.maskSupp (ir.refLen ir.exprs.length) (.add x y)).isSome = true
    then some (.ivl d (.add x y) (min lo lo') (max hi hi'))
    else none
  | _, _ => none

end

end GordieHowe.RealizedProgram
