-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.SourceRoles
public import GordieHowe.Language.RealizedProgram.Semantics

public section

namespace GordieHowe.MLDSA44

open RealizedProgram

/-- **The selection witness components of an ML-DSA source execution.**
The components are selected bytes, packed threshold words and the six memory trace columns. -/
structure SelectionSourceValues (K : Type) where
  selected : Nat → K
  threshold : Nat → K
  readValue : Nat → K
  readOrigin : Nat → K
  encoded : Nat → K
  finalOrigin : Nat → K
  unit : Nat → K
  origin : Nat → K

/-- **Interpret the eight declared selection witness slots.** Other roles and slots contribute zero. -/
@[expose] def SelectionSourceValues.meaning {K : Type} [Zero K] (s : SelectionSourceValues K) :
    SourceRole → Nat → Nat → K
  | .selection, 0, j => s.selected j
  | .selection, 1, j => s.threshold j
  | .selection, 2, j => s.readValue j
  | .selection, 3, j => s.readOrigin j
  | .selection, 4, j => s.encoded j
  | .selection, 5, j => s.finalOrigin j
  | .selection, 6, j => s.unit j
  | .selection, 7, j => s.origin j
  | _, _, _ => 0

/-- **Witness slot 0 is the semantic `selected` component.** -/
theorem SelectionSourceValues.meaning_selected {K : Type} [Zero K] (s : SelectionSourceValues K)
    (j : Nat) : s.meaning .selection 0 j = s.selected j := rfl

/-- **Witness slot 1 is the semantic `threshold` component.** -/
theorem SelectionSourceValues.meaning_threshold {K : Type} [Zero K] (s : SelectionSourceValues K)
    (j : Nat) : s.meaning .selection 1 j = s.threshold j := rfl

/-- **Witness slot 2 is the semantic `readValue` component.** -/
theorem SelectionSourceValues.meaning_readValue {K : Type} [Zero K] (s : SelectionSourceValues K)
    (j : Nat) : s.meaning .selection 2 j = s.readValue j := rfl

/-- **Witness slot 3 is the semantic `readOrigin` component.** -/
theorem SelectionSourceValues.meaning_readOrigin {K : Type} [Zero K] (s : SelectionSourceValues K)
    (j : Nat) : s.meaning .selection 3 j = s.readOrigin j := rfl

/-- **Witness slot 4 is the semantic `encoded` component.** -/
theorem SelectionSourceValues.meaning_encoded {K : Type} [Zero K] (s : SelectionSourceValues K)
    (j : Nat) : s.meaning .selection 4 j = s.encoded j := rfl

/-- **Witness slot 5 is the semantic `finalOrigin` component.** -/
theorem SelectionSourceValues.meaning_finalOrigin {K : Type} [Zero K] (s : SelectionSourceValues K)
    (j : Nat) : s.meaning .selection 5 j = s.finalOrigin j := rfl

/-- **Witness slot 6 is the semantic `unit` component.** -/
theorem SelectionSourceValues.meaning_unit {K : Type} [Zero K] (s : SelectionSourceValues K)
    (j : Nat) : s.meaning .selection 6 j = s.unit j := rfl

/-- **Witness slot 7 is the semantic `origin` component.** -/
theorem SelectionSourceValues.meaning_origin {K : Type} [Zero K] (s : SelectionSourceValues K)
    (j : Nat) : s.meaning .selection 7 j = s.origin j := rfl

/-- **Read selection witness components through the shared source classifier.**
The role determines the semantic component; the program index is used only for lookup. -/
@[expose] def SelectionSourceValues.valuation {program : RealizedProgram} {I : Interp}
    (s : SelectionSourceValues (I 1).K) (classifier : SourceRoleClassifier) : program.Valuation I :=
  fun v j => match classifier.lookup v with
    | some (role, slot) => castElt (a := 1) (s.meaning role slot j)
    | none => 0

/-- **A checked lookup selects its exact selection witness component.** -/
theorem SelectionSourceValues.valuation_of_lookup {program : RealizedProgram} {I : Interp}
    (s : SelectionSourceValues (I 1).K) {classifier : SourceRoleClassifier} {v : Nat}
    {role : SourceRole} {slot : Nat} (h : classifier.lookup v = some (role, slot)) (j : Nat) :
    s.valuation (program := program) classifier v j = castElt (s.meaning role slot j) := by
  simp only [valuation, h]

/-- **An absent role contributes zero.** -/
theorem SelectionSourceValues.valuation_of_none {program : RealizedProgram} {I : Interp}
    (s : SelectionSourceValues (I 1).K) {classifier : SourceRoleClassifier} {v : Nat}
    (h : classifier.lookup v = none) (j : Nat) :
    s.valuation (program := program) classifier v j = 0 := by
  simp only [valuation, h]

end GordieHowe.MLDSA44
