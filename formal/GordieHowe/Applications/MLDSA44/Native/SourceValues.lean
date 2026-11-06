-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Honest.SourceRoles
public import GordieHowe.Applications.MLDSA44.Honest.AlgebraSourceRoles
public import GordieHowe.Applications.MLDSA44.Honest.SelectionSourceRoles

public section

namespace GordieHowe.MLDSA44.Native

open RealizedProgram

/-- **Interpret one native source coordinate from its checked semantic role.**
The classifier is captured once by the strategy. Public statement roles are supplied by the
statement; the four witness tags select the algebra, hash, or selection component. -/
@[expose] def sourceVal {program : RealizedProgram} {I : Interp}
    (a : AlgebraSourceValues (I 0).K) (h : HashSourceValues (I 1).K)
    (s : SelectionSourceValues (I 1).K) (classifier : SourceRoleClassifier) :
    program.Valuation I := fun v j =>
  match classifier.lookup v with
  | some (.aWitness, slot) => castElt (a := 0) (a.meaning .aWitness slot j)
  | some (.hashBit, slot) => castElt (a := 1) (h.meaning .hashBit slot j)
  | some (.hashWord, slot) => castElt (a := 1) (h.meaning .hashWord slot j)
  | some (.selection, slot) => castElt (a := 1) (s.meaning .selection slot j)
  | _ => 0

variable {program : RealizedProgram} {I : Interp}
  (a : AlgebraSourceValues (I 0).K) (h : HashSourceValues (I 1).K)
  (s : SelectionSourceValues (I 1).K) {classifier : SourceRoleClassifier} {v slot : Nat}

/-- **An algebra role selects the algebra witness interpreter.** -/
theorem sourceVal_algebra (hr : classifier.lookup v = some (.aWitness, slot)) (j : Nat) :
    sourceVal (program := program) a h s classifier v j = a.valuation classifier v j := by
  rw [AlgebraSourceValues.valuation_of_lookup _ hr]
  simp only [sourceVal, hr]

/-- **A bit role selects the hash witness interpreter.** -/
theorem sourceVal_hashBit (hr : classifier.lookup v = some (.hashBit, slot)) (j : Nat) :
    sourceVal (program := program) a h s classifier v j = h.valuation classifier v j := by
  rw [HashSourceValues.valuation_of_lookup _ hr]
  simp only [sourceVal, hr]

/-- **A word role selects the hash witness interpreter.** -/
theorem sourceVal_hashWord (hr : classifier.lookup v = some (.hashWord, slot)) (j : Nat) :
    sourceVal (program := program) a h s classifier v j = h.valuation classifier v j := by
  rw [HashSourceValues.valuation_of_lookup _ hr]
  simp only [sourceVal, hr]

/-- **A selection role selects the selection witness interpreter.** -/
theorem sourceVal_selection (hr : classifier.lookup v = some (.selection, slot)) (j : Nat) :
    sourceVal (program := program) a h s classifier v j = s.valuation classifier v j := by
  rw [SelectionSourceValues.valuation_of_lookup _ hr]
  simp only [sourceVal, hr]

end GordieHowe.MLDSA44.Native
