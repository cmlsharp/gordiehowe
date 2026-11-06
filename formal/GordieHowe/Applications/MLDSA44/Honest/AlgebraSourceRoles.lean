-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.SourceRoles
public import GordieHowe.Language.RealizedProgram.Semantics

public section

namespace GordieHowe.MLDSA44

open RealizedProgram

/-- **The algebra witness components of an ML-DSA source execution.**
The bound sources carry their semantic values; realization digits are supplied by completion. -/
structure AlgebraSourceValues (K : Type) where
  z : Nat → K
  hint : Nat → K
  challenge : Nat → K
  w : Nat → K
  w1 : Nat → K
  nonpositive : Nat → K
  offset : Nat → K
  slack : Nat → K

/-- **Interpret the eight declared algebra witness slots.** Other roles and slots contribute zero. -/
@[expose] def AlgebraSourceValues.meaning {K : Type} [Zero K] (s : AlgebraSourceValues K) :
    SourceRole → Nat → Nat → K
  | .aWitness, 0, j => s.z j
  | .aWitness, 1, j => s.hint j
  | .aWitness, 2, j => s.challenge j
  | .aWitness, 3, j => s.w j
  | .aWitness, 4, j => s.w1 j
  | .aWitness, 5, j => s.nonpositive j
  | .aWitness, 6, j => s.offset j
  | .aWitness, 7, j => s.slack j
  | _, _, _ => 0

/-- **Witness slot 0 is the semantic `z` component.** -/
theorem AlgebraSourceValues.meaning_z {K : Type} [Zero K] (s : AlgebraSourceValues K)
    (j : Nat) : s.meaning .aWitness 0 j = s.z j := rfl

/-- **Witness slot 1 is the semantic `hint` component.** -/
theorem AlgebraSourceValues.meaning_hint {K : Type} [Zero K] (s : AlgebraSourceValues K)
    (j : Nat) : s.meaning .aWitness 1 j = s.hint j := rfl

/-- **Witness slot 2 is the semantic `challenge` component.** -/
theorem AlgebraSourceValues.meaning_challenge {K : Type} [Zero K] (s : AlgebraSourceValues K)
    (j : Nat) : s.meaning .aWitness 2 j = s.challenge j := rfl

/-- **Witness slot 3 is the semantic `w` component.** -/
theorem AlgebraSourceValues.meaning_w {K : Type} [Zero K] (s : AlgebraSourceValues K)
    (j : Nat) : s.meaning .aWitness 3 j = s.w j := rfl

/-- **Witness slot 4 is the semantic `w1` component.** -/
theorem AlgebraSourceValues.meaning_w1 {K : Type} [Zero K] (s : AlgebraSourceValues K)
    (j : Nat) : s.meaning .aWitness 4 j = s.w1 j := rfl

/-- **Witness slot 5 is the semantic `nonpositive` component.** -/
theorem AlgebraSourceValues.meaning_nonpositive {K : Type} [Zero K] (s : AlgebraSourceValues K)
    (j : Nat) : s.meaning .aWitness 5 j = s.nonpositive j := rfl

/-- **Witness slot 6 is the semantic `offset` component.** -/
theorem AlgebraSourceValues.meaning_offset {K : Type} [Zero K] (s : AlgebraSourceValues K)
    (j : Nat) : s.meaning .aWitness 6 j = s.offset j := rfl

/-- **Witness slot 7 is the semantic `slack` component.** -/
theorem AlgebraSourceValues.meaning_slack {K : Type} [Zero K] (s : AlgebraSourceValues K)
    (j : Nat) : s.meaning .aWitness 7 j = s.slack j := rfl

/-- **Read algebra witness components through the shared source classifier.**
The role determines the semantic component; the program index is used only for lookup. -/
@[expose] def AlgebraSourceValues.valuation {program : RealizedProgram} {I : Interp}
    (s : AlgebraSourceValues (I 0).K) (classifier : SourceRoleClassifier) : program.Valuation I :=
  fun v j => match classifier.lookup v with
    | some (role, slot) => castElt (a := 0) (s.meaning role slot j)
    | none => 0

/-- **A checked lookup selects its exact algebra witness component.** -/
theorem AlgebraSourceValues.valuation_of_lookup {program : RealizedProgram} {I : Interp}
    (s : AlgebraSourceValues (I 0).K) {classifier : SourceRoleClassifier} {v : Nat}
    {role : SourceRole} {slot : Nat} (h : classifier.lookup v = some (role, slot)) (j : Nat) :
    s.valuation (program := program) classifier v j = castElt (s.meaning role slot j) := by
  simp only [valuation, h]

/-- **An absent role contributes zero.** -/
theorem AlgebraSourceValues.valuation_of_none {program : RealizedProgram} {I : Interp}
    (s : AlgebraSourceValues (I 0).K) {classifier : SourceRoleClassifier} {v : Nat}
    (h : classifier.lookup v = none) (j : Nat) :
    s.valuation (program := program) classifier v j = 0 := by
  simp only [valuation, h]

end GordieHowe.MLDSA44
