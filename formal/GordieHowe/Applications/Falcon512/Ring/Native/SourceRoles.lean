-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Honest
public import GordieHowe.Language.Honest.SourceRoles

public section

namespace GordieHowe.Falcon512.Ring.Native

open RealizedProgram

/-- **The witness components read by the native ring's source-role interpreter.**
The field is a parameter; the record contains only computational values and functions. -/
structure SourceValues (K : Type) where
  spectrum : ℕ → K
  signer : ℕ
  s2 : ℕ → ℕ
  s1 : ℕ → ℕ
  magnitudes : ℕ → ℕ
  squareDigits : ℕ → ℕ
  columnCarries : ℕ → ℕ
  batchDigits : ℕ → ℕ
  batchCarries : ℕ → ℕ
  finalDigits : ℕ → ℕ
  finalCarries : ℕ → ℕ

/-- **Interpret a declared native-ring role and slot.** Statement values are supplied separately
by the execution's statement. Unused tags and slots contribute zero. -/
@[expose] def SourceValues.meaning {K : Type} [Semiring K] (s : SourceValues K) :
    SourceRole → ℕ → ℕ → K
  | .ringSigma, 0, j => if j < 512 then s.spectrum j else 0
  | .selection, 0, j => (s.signer / 2 ^ j % 2 : ℕ)
  | .aWitness, 0, j => (s.s2 j : ℕ)
  | .aWitness, 1, j => (s.s1 j : ℕ)
  | .aWitness, 2, j => (s.magnitudes j : ℕ)
  | .aWitness, 3, j => (s.squareDigits j : ℕ)
  | .aWitness, 4, j => (s.columnCarries j : ℕ)
  | .aWitness, 5, j => (s.batchDigits j : ℕ)
  | .aWitness, 6, j => (s.batchCarries j : ℕ)
  | .aWitness, 7, j => (s.finalDigits j : ℕ)
  | .aWitness, 8, j => (s.finalCarries j : ℕ)
  | _, _, _ => 0

/-- **Assign source values through the shared, already constructed classifier.**
The interpreter does not inspect the program's syntax or reconstruct the role table. -/
@[expose] def SourceValues.valuation {program : RealizedProgram} {I : Interp}
    (s : SourceValues (I 0).K) (classifier : SourceRoleClassifier) : program.Valuation I :=
  fun v j => match classifier.lookup v with
    | some (role, slot) => castElt (s.meaning role slot j)
    | none => 0

/-- **A named lookup fixes the witness component read by the valuation.** -/
theorem SourceValues.valuation_of_lookup {program : RealizedProgram} {I : Interp}
    (s : SourceValues (I 0).K) {classifier : SourceRoleClassifier} {v : ℕ}
    {role : SourceRole} {slot : ℕ} (h : classifier.lookup v = some (role, slot)) (j : ℕ) :
    s.valuation (program := program) classifier v j = castElt (s.meaning role slot j) := by
  simp only [valuation, h]

/-- **An absent source-role entry contributes zero.** -/
theorem SourceValues.valuation_of_none {program : RealizedProgram} {I : Interp}
    (s : SourceValues (I 0).K) {classifier : SourceRoleClassifier} {v : ℕ}
    (h : classifier.lookup v = none) (j : ℕ) :
    s.valuation (program := program) classifier v j = 0 := by
  simp only [valuation, h]

end GordieHowe.Falcon512.Ring.Native
