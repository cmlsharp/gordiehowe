-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Honest.SourceRoles

public section

namespace GordieHowe.Falcon512.Native

open RealizedProgram

/-- **The computational witness components of native Falcon.** Hash words and raw samples use
field H; counters and flags use the selection field. Algebraic witnesses are natural numbers. -/
structure SourceValues (H S : Type) where
  hash : HashSourceValues H
  rawSamples : Nat → H
  counts : Nat → S
  full : Nat → S
  crossing : Nat → Nat
  s2 : Nat → Nat
  s1 : Nat → Nat
  magnitudes : Nat → Nat
  squareDigits : Nat → Nat
  columnCarries : Nat → Nat
  batchDigits : Nat → Nat
  batchCarries : Nat → Nat
  finalDigits : Nat → Nat
  finalCarries : Nat → Nat

/-- **Read the algebraic witness component named by a slot.** -/
@[expose] def SourceValues.algebra {H S : Type} (s : SourceValues H S) : Nat → Nat → Nat
  | 0, j => s.crossing j
  | 1, j => s.s2 j
  | 2, j => s.s1 j
  | 3, j => s.magnitudes j
  | 4, j => s.squareDigits j
  | 5, j => s.columnCarries j
  | 6, j => s.batchDigits j
  | 7, j => s.batchCarries j
  | 8, j => s.finalDigits j
  | 9, j => s.finalCarries j
  | _, _ => 0

/-- **Interpret a role in the value's field.** Statement values are supplied by the statement;
unknown roles and slots contribute zero. The interpretation reads no program syntax. -/
@[expose] def SourceValues.meaning {I : Interp} {selectField : Nat}
    (s : SourceValues (I 0).K (I selectField).K) (field : Nat) :
    SourceRole → Nat → Nat → (I field).K
  | .hashWord, slot, j => castElt (s.hash.meaning .hashWord slot j)
  | .hashBit, slot, j => castElt (s.hash.meaning .hashBit slot j)
  | .selection, 0, j => castElt (s.rawSamples j)
  | .selection, 1, j => castElt (a := selectField) (s.counts j)
  | .selection, 2, j => castElt (a := selectField) (s.full j)
  | .aWitness, slot, j => castElt (a := 1) (s.algebra slot j : (I 1).K)
  | _, _, _ => 0

/-- **Read the declared role through a captured classifier.** -/
@[expose] def SourceValues.valuation {program : RealizedProgram} {I : Interp}
    {selectField : Nat} (s : SourceValues (I 0).K (I selectField).K)
    (classifier : SourceRoleClassifier) : program.Valuation I :=
  fun v j => match classifier.lookup v with
    | some (role, slot) => s.meaning (program.valueField v) role slot j
    | none => 0

/-- **A named lookup determines the semantic component read at a source value.** -/
theorem SourceValues.valuation_of_lookup {program : RealizedProgram} {I : Interp}
    {selectField : Nat} (s : SourceValues (I 0).K (I selectField).K)
    {classifier : SourceRoleClassifier} {v : Nat} {role : SourceRole} {slot : Nat}
    (h : classifier.lookup v = some (role, slot)) (j : Nat) :
    s.valuation (program := program) classifier v j =
      s.meaning (program.valueField v) role slot j := by
  simp only [valuation, h]

end GordieHowe.Falcon512.Native
