-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Completeness.Basic

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Completeness.Bound`

The definitions of `GordieHowe.Language.Completeness.Bound` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Completeness/Bound.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable {ir : RealizedProgram} {primeNodes : ℕ → List String}

variable (ir) in
/-- **The facts of a two-sided or digit lookup** `pid` with body `mem d [rec] (range N) (lookup r)`
at the certificate's generators `G`: a source
predicate of a domain with `k` digit values (and `k` second digits for a two-sided lookup, none for
a digit lookup), each generated as this lookup's digit at its position; the digits committed cells
of the record's length in the domain's field and no source values; the base above `1`; the range
within the digits and within the characteristic; the record reading source values that read no
challenge and no late value. -/
structure DigitLookupFactsC (G : Gens) (pid d : ℕ) (rec : Expr) (N : ℕ) (r : LookupRealization) :
    Prop where
  /-- A two-sided or digit lookup. -/
  kind : r.kind = .twoSided ∨ r.kind = .digits
  /-- A source predicate. -/
  source : ir.inSource (ir.predicate pid) = true
  /-- A domain of the program. -/
  domain : d < ir.domains.length
  /-- `k` digit values. -/
  len : r.digitValues.length = r.digits
  /-- `k` second digits for a two-sided lookup, none for a digit lookup. -/
  second : (r.kind = .twoSided → r.second.length = r.digits) ∧ (r.kind = .digits → r.second = [])
  /-- The digit values are generated as this lookup's at their positions. -/
  ownFirst : ∀ j (hj : j < r.digitValues.length), G.at r.digitValues[j] = .lookupDigit pid false j
  /-- The second digits are generated as this lookup's at their positions. -/
  ownSecond : ∀ j (hj : j < r.second.length), G.at r.second[j] = .lookupDigit pid true j
  /-- The digits are committed cells of the record's length in the domain's field, no source
  values. -/
  cells : ∀ u ∈ r.digitValues ++ r.second, ir.privCellB u = true ∧
    (ir.value u).size = ir.exprLen rec ∧ ir.valueField u = ir.domainField d ∧
      ¬ ir.IsSourceValue u
  /-- The base exceeds `1`. -/
  baseGt : 1 < r.base
  /-- The range lies within the digits. -/
  honestRange : N ≤ r.base ^ r.digits
  /-- The range lies within the characteristic. -/
  rangeLe : N ≤ ir.charOf (ir.domainField d)
  /-- The record reads source values that read no challenge and no late value. -/
  recReads : ∀ w ∈ ir.exprNodes rec, ir.IsSourceValue w ∧ (ir.readsT.getD w []).isEmpty = true

instance (G : Gens) (pid d : ℕ) (rec : Expr) (N : ℕ) (r : LookupRealization) :
    Decidable (ir.DigitLookupFactsC G pid d rec N r) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩,
     fun h => ⟨h.kind, h.source, h.domain, h.len, h.second, h.ownFirst, h.ownSecond, h.cells,
      h.baseGt, h.honestRange, h.rangeLe, h.recReads⟩⟩

/-- **The quotient digit a generator is a committed digit of**: `(m, j)` for `commDigit m j _ _`. -/
def _root_.GordieHowe.RealizedProgram.Gen.commPos? : Gen → Option (ℕ × ℕ)
  | .commDigit m j _ _ => some (m, j)
  | _ => none

/-- **The quotient digit a lookup's digits are generated as** at the certificate's generators `G`:
`(m, j)` when the generator of its first digit is `commDigit m j _ _` (`Cert.gens` names it; nothing
is searched). -/
def _root_.GordieHowe.RealizedProgram.Gens.commOf? (G : Gens) (r : LookupRealization) :
    Option (ℕ × ℕ) :=
  r.digitValues.head?.bind fun u => (G.at u).commPos?

end

end GordieHowe.RealizedProgram
