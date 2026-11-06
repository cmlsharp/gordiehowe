-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Check

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Source`

The definitions of `GordieHowe.Language.RealizedProgram.Source` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/Source.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **A value of the source program**: a value of role `source`. -/
def IsSourceValue (v : ℕ) : Prop := (ir.value v).role = .source

instance (v : ℕ) : Decidable (ir.IsSourceValue v) := inferInstanceAs (Decidable (_ = _))

/-- **A predicate of the source program**: of role `source`, or the type check of a source
value. -/
def inSource (p : Predicate) : Bool :=
  match p.role with
  | .source => true
  | .type v => decide (ir.IsSourceValue v)
  | .realization _ => false

/-- A realization-owned value is not a source value. -/
theorem not_IsSourceValue_of_realization {v q : Nat}
    (h : (ir.value v).role = .realization q) : ¬ ir.IsSourceValue v := by
  simp only [IsSourceValue, h, reduceCtorEq, not_false_eq_true]

/-- Source-owned predicates belong to the source program. -/
theorem inSource_of_source {p : Predicate} (h : p.role = .source) : ir.inSource p = true := by
  simp only [inSource, h]

/-- Realization-owned predicates are not source predicates. -/
theorem inSource_of_realization {p : Predicate} {q : Nat} (h : p.role = .realization q) :
    ir.inSource p = false := by
  simp only [inSource, h]

/-- A type predicate is a source predicate when its value has source ownership. -/
theorem inSource_of_type {p : Predicate} {v : Nat} (hp : p.role = .type v)
    (hv : (ir.value v).role = .source) : ir.inSource p = true := by
  simp only [inSource, hp, IsSourceValue, hv, decide_true]

/-- A type predicate for a realization-owned value is not a source predicate. -/
theorem inSource_of_type_realization {p : Predicate} {v q : Nat}
    (hp : p.role = .type v) (hv : (ir.value v).role = .realization q) :
    ir.inSource p = false := by
  simp only [inSource, hp, IsSourceValue, hv, reduceCtorEq, decide_false]

end

/-- Whether a predicate body is an `in`. -/
def PredBody.isMem : PredBody → Bool
  | .mem _ _ _ _ => true
  | _ => false

/-- Whether a predicate body is a cross-field `equal`. -/
def PredBody.isCross : PredBody → Bool
  | .cross _ _ _ _ _ _ => true
  | _ => false

section

variable (ir : RealizedProgram)

/-- **A challenge of the source program**: a challenge of role `source`. -/
def chalIsSource (j : ℕ) : Bool :=
  decide (j < ir.challenges.length) && (ir.challenge j).role == .source

/-- The exhaustive list of source-role challenges, in declaration order. -/
def sourceChallengeIds : List Nat :=
  (List.range ir.challenges.length).filter ir.chalIsSource

/-- **The role of challenge `j` is admissible**: not `unmodeled`; the owner of a realization
challenge is a predicate, an `in` for a table's challenge `α` (`alpha:<D>`), a cross-field
`equal` for any other (the MAC key `<mac>.beta`). -/
def chalRoleOk (j : ℕ) : Bool :=
  match (ir.challenge j).role with
  | .source => true
  | .realization o =>
    decide (o < ir.predicates.length) &&
      if ir.tables.any (·.alpha == j) then PredBody.isMem (ir.predicate o).body
      else PredBody.isCross (ir.predicate o).body
  | .unmodeled => false

end

end GordieHowe.RealizedProgram
