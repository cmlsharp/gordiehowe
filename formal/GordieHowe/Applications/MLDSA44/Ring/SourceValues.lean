-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.SourceValues

public section

namespace GordieHowe.MLDSA44.Ring

open RealizedProgram

/-- The selected member's algebra inputs, the signature relation's quotient by `q` (the carrier's
`carry` slot `0`, `signature.relation.q`) and the high halves of its products by `X^n + 1`
(algebra slot `8`, `signature.Q`, of both rings). -/
structure MemberSourceValues (K : Type) where
  aHat : Nat → K
  t1 : Nat → K
  mu : Nat → K
  index : Nat → K
  quotient : Nat → K
  high : Nat → K

/-- Interpret the ring-specific roles and delegate the common ML-DSA witness roles to their
algebra, hash and selection interpreters. The ring index is selection slot eight in field zero;
SampleInBall's selection slots remain in field one. No program identifier selects a meaning. -/
@[expose] def sourceVal {program : RealizedProgram} {I : Interp}
    (m : MemberSourceValues (I 0).K)
    (a : AlgebraSourceValues (I 0).K) (h : HashSourceValues (I 1).K)
    (s : SelectionSourceValues (I 1).K) (classifier : SourceRoleClassifier) :
    program.Valuation I := fun v j =>
  match classifier.lookup v with
  | some (.ringSigma, 0) => castElt (a := 0) (m.aHat j)
  | some (.ringSigma, 1) => castElt (a := 0) (m.t1 j)
  | some (.ringSigma, 2) => castElt (a := 0) (m.mu j)
  | some (.selection, 8) => castElt (a := 0) (m.index j)
  | some (.carry, 0) => castElt (a := 0) (m.quotient j)
  | some (.aWitness, 8) => castElt (a := 0) (m.high j)
  | _ => Native.sourceVal a h s classifier v j

variable {program : RealizedProgram} {I : Interp}
  (m : MemberSourceValues (I 0).K)
  (a : AlgebraSourceValues (I 0).K) (h : HashSourceValues (I 1).K)
  (s : SelectionSourceValues (I 1).K) {classifier : SourceRoleClassifier} {v slot : Nat}

/-- Member slot zero reads the selected public matrix. -/
theorem sourceVal_aHat (hr : classifier.lookup v = some (.ringSigma, 0)) (j : Nat) :
    sourceVal (program := program) m a h s classifier v j = castElt (a := 0) (m.aHat j) := by
  simp only [sourceVal, hr]

/-- Member slot one reads the selected transformed key vector. -/
theorem sourceVal_t1 (hr : classifier.lookup v = some (.ringSigma, 1)) (j : Nat) :
    sourceVal (program := program) m a h s classifier v j = castElt (a := 0) (m.t1 j) := by
  simp only [sourceVal, hr]

/-- Member slot two reads the selected message digest. -/
theorem sourceVal_mu (hr : classifier.lookup v = some (.ringSigma, 2)) (j : Nat) :
    sourceVal (program := program) m a h s classifier v j = castElt (a := 0) (m.mu j) := by
  simp only [sourceVal, hr]

/-- The ring-selection slot reads the signer's position bits. -/
theorem sourceVal_index (hr : classifier.lookup v = some (.selection, 8)) (j : Nat) :
    sourceVal (program := program) m a h s classifier v j = castElt (a := 0) (m.index j) := by
  simp only [sourceVal, hr]

/-- The carrier's quotient role reads its semantic quotient coordinates. -/
theorem sourceVal_quotient (hr : classifier.lookup v = some (.carry, 0)) (j : Nat) :
    sourceVal (program := program) m a h s classifier v j = castElt (a := 0) (m.quotient j) := by
  simp only [sourceVal, hr]

/-- The high halves' slot (algebra slot `8`) reads the high halves' coordinates. -/
theorem sourceVal_high (hr : classifier.lookup v = some (.aWitness, 8)) (j : Nat) :
    sourceVal (program := program) m a h s classifier v j = castElt (a := 0) (m.high j) := by
  simp only [sourceVal, hr]

/-- Algebra witness roles other than the quotient's retain the shared ML-DSA meaning. -/
theorem sourceVal_algebra (hr : classifier.lookup v = some (.aWitness, slot)) (hs : slot ≠ 8)
    (j : Nat) :
    sourceVal (program := program) m a h s classifier v j = a.valuation classifier v j := by
  simp only [sourceVal, hr]
  split <;> simp_all
  exact Native.sourceVal_algebra a h s hr j

/-- Hash-bit roles retain the shared hash meaning. -/
theorem sourceVal_hashBit (hr : classifier.lookup v = some (.hashBit, slot)) (j : Nat) :
    sourceVal (program := program) m a h s classifier v j = h.valuation classifier v j := by
  simp only [sourceVal, hr]
  exact Native.sourceVal_hashBit a h s hr j

/-- Hash-word roles retain the shared hash meaning. -/
theorem sourceVal_hashWord (hr : classifier.lookup v = some (.hashWord, slot)) (j : Nat) :
    sourceVal (program := program) m a h s classifier v j = h.valuation classifier v j := by
  simp only [sourceVal, hr]
  exact Native.sourceVal_hashWord a h s hr j

/-- SampleInBall's slots are distinct from the ring index slot and retain their meaning. -/
theorem sourceVal_selection (hr : classifier.lookup v = some (.selection, slot))
    (hs : slot ≠ 8) (j : Nat) :
    sourceVal (program := program) m a h s classifier v j = s.valuation classifier v j := by
  simp only [sourceVal, hr]
  split <;> simp_all
  exact Native.sourceVal_selection a h s hr j

end GordieHowe.MLDSA44.Ring
