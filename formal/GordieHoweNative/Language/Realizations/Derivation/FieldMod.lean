-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.Basic

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.FieldMod`

The definitions of `GordieHowe.Language.Realizations.Derivation.FieldMod` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/FieldMod.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **`fieldDvd k a b`** in domain `d`: from `eq d x y` (`k`), `ivl d x lo hi` (`a`) and
`ivl d y lo' hi'` (`b`), `x` and `y` of one length: `dvd d (x − y) p`, `p` the characteristic of
`d`'s field. -/
def fieldDvdFact (fs : List Fact) (d k a b : ℕ) : Option Fact :=
  match fs[k]?, fs[a]?, fs[b]? with
  | some (.eq d₀ x y), some (.ivl d₁ x' _ _), some (.ivl d₂ y' _ _) =>
    if d₀ = d ∧ d₁ = d ∧ d₂ = d ∧ x'.beq x = true ∧ y'.beq y = true ∧
        ir.exprLen x = ir.exprLen y ∧ d < ir.domains.length then
      some (.dvd d (.sub x y) (ir.charOf (ir.domainField d)))
    else none
  | _, _, _ => none

end

end GordieHowe.RealizedProgram
