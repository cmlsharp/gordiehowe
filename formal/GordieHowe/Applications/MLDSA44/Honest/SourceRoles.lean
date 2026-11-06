-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.SourceRoles
public import GordieHowe.Language.RealizedProgram.Semantics

public section

namespace GordieHowe.MLDSA44

open RealizedProgram

/-- **The computational components of an ML-DSA hash witness.**
Round words are indexed by permutation, round and word coordinate, independently of program IDs. -/
structure HashSourceValues (K : Type) where
  buffer : Nat → K
  flags : Nat → K
  w1 : Nat → K
  mu : Nat → K
  rounds : Nat → Nat → Nat → K

/-- **Interpret hash-role slots.** Bit slots zero and one are the message buffer and flags;
word slots zero and one are `w1` and `mu`. Subsequent word slots enumerate the 24 rounds of each
permutation. Other tags and bit slots contribute zero. -/
@[expose] def HashSourceValues.meaning {K : Type} [Zero K] (s : HashSourceValues K) :
    SourceRole → Nat → Nat → K
  | .hashBit, 0, j => s.buffer j
  | .hashBit, 1, j => s.flags j
  | .hashWord, 0, j => s.w1 j
  | .hashWord, 1, j => s.mu j
  | .hashWord, slot + 2, j => s.rounds (slot / 24) (slot % 24) j
  | _, _, _ => 0

/-- **Read hash witness values through an already constructed source classifier.**
Only the classifier lookup depends on the program value index. -/
@[expose] def HashSourceValues.valuation {program : RealizedProgram} {I : Interp}
    (s : HashSourceValues (I 1).K) (classifier : SourceRoleClassifier) : program.Valuation I :=
  fun v j => match classifier.lookup v with
    | some (role, slot) => castElt (a := 1) (s.meaning role slot j)
    | none => 0

/-- **A named role lookup selects its exact witness component.** -/
theorem HashSourceValues.valuation_of_lookup {program : RealizedProgram} {I : Interp}
    (s : HashSourceValues (I 1).K) {classifier : SourceRoleClassifier} {v : Nat}
    {role : SourceRole} {slot : Nat} (h : classifier.lookup v = some (role, slot)) (j : Nat) :
    s.valuation (program := program) classifier v j = castElt (s.meaning role slot j) := by
  simp only [valuation, h]

/-- **An absent role contributes zero.** -/
theorem HashSourceValues.valuation_of_none {program : RealizedProgram} {I : Interp}
    (s : HashSourceValues (I 1).K) {classifier : SourceRoleClassifier} {v : Nat}
    (h : classifier.lookup v = none) (j : Nat) :
    s.valuation (program := program) classifier v j = 0 := by
  simp only [valuation, h]

/-- **The round-word slot reads the declared permutation and round.** -/
theorem HashSourceValues.meaning_round {K : Type} [Zero K] (s : HashSourceValues K)
    (p t j : Nat) (ht : t < 24) :
    s.meaning .hashWord (2 + 24 * p + t) j = s.rounds p t j := by
  have hs : 2 + 24 * p + t = (24 * p + t) + 2 := by omega
  rw [hs]
  simp only [meaning]
  congr 1 <;> omega

end GordieHowe.MLDSA44
