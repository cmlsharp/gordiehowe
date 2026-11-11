-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.MemberValues
public import GordieHoweNative.Language.RealizedProgram.RealizationValid

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.Roots`

The definitions of `GordieHowe.Language.Realizations.Derivation.Roots` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/Roots.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section Defs

variable (ir : RealizedProgram)

/-- **The quadratic root equation on value `v`** in predicate `pr` (`quadRootView`'s shape): the
value `m` and the constant `c` of the field `equal` `(m + a v) · (m + a (a v + C)) = z`, `a = p − 1`,
`z` a constant holding `0`, `C` a constant expression holding `c` (`constOf`). -/
def quadView (v : ℕ) (pr : Predicate) : Option (ℕ × ℕ) :=
  match pr.body with
  | .equal d lhs (.leaf z) _ =>
    match lhs with
    | .mul (.add (.leaf m) (.scale (.const a) (.leaf v₁)))
        (.add (.leaf m₂) (.scale (.const a₂) (.add (.scale (.const a₃) (.leaf v₂)) C))) =>
      if v₁ = v ∧ v₂ = v ∧ m₂ = m ∧ a + 1 = ir.charOf (ir.valueField v) ∧ a₂ = a ∧ a₃ = a ∧
          ir.domainField d = ir.valueField v ∧ ir.valueField m = ir.valueField v ∧
          ir.valueField z = ir.valueField v ∧ (ir.value v).size ≤ ir.exprLen lhs ∧
          ir.zeroConstB z = true then
        (ir.constOf (ir.value v).size (ir.valueField v) C).map fun c => (m, c)
      else none
    | _ => none
  | _ => none

/-- **The bound `c + 1` of value `v` from the quadratic root equation of predicate `q`**, its `m`
the value `m` with the interval `[lo, hi]`: `lo = 0` and `hi ≤ c`. -/
def quadSrcN (v q m : ℕ) (lo hi : ℤ) : Option ℕ :=
  if q < ir.predicates.length then
    match ir.quadView v (ir.predicate q) with
    | some (m', c) => if m' = m ∧ lo = 0 ∧ hi ≤ c then some (c + 1) else none
    | none => none
  else none

/-- **The root-set equations on value `v` of the listed predicates `qs`** (`rootSetView`). -/
def rootSetViewsAt (v : ℕ) (qs : List ℕ) : List ((ℕ → ℕ) × ℕ × Ivl) :=
  qs.filterMap fun q => if q < ir.predicates.length then ir.rootSetView v (ir.predicate q) else none

/-- **The interval of value `v` from the root-set equations of the listed predicates `qs`**: as
`rootSetIvlAt`, over the listed equations only (`rootSetViewsAt`). -/
def rootSetSrc (v : ℕ) (qs : List ℕ) : Option Ivl :=
  if (ir.value v).type = .bit then none else
  let ws := ir.rootSetViewsAt v qs
  let lo := (ws.map fun w => w.2.2.lo).foldl min ((ws.map fun w => w.2.2.lo).headD 0)
  let hi := (ws.map fun w => w.2.2.hi).foldl max ((ws.map fun w => w.2.2.hi).headD 0)
  if ws.isEmpty = false ∧ (∀ c < (ir.value v).size, ∃ w ∈ ws, ∃ i < w.2.1, w.1 i = c) ∧
      ∀ w ∈ ws, lo ≤ w.2.2.lo ∧ w.2.2.hi ≤ hi then
    some ⟨lo, hi⟩
  else none

end Defs

end GordieHowe.RealizedProgram
