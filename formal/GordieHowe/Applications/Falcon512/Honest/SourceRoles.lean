-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.SourceRoles
public import GordieHowe.Language.RealizedProgram.Semantics

public section

namespace GordieHowe.Falcon512

open RealizedProgram

/-- **The computational components of the Falcon hash witness.**
Round words use permutation, round and coordinate indices, independent of program IDs. -/
structure HashSourceValues (K : Type) where
  nonce : Nat → K
  message : Nat → K
  flags : Nat → K
  state : Nat → K
  rounds : Nat → Nat → Nat → K

/-- **Read the witness component named by a hash role and slot.** Bit slots identify nonce,
message and flags. Word slot zero holds the squeeze state; subsequent slots identify rounds. -/
@[expose] def HashSourceValues.meaning {K : Type} [Zero K] (s : HashSourceValues K) :
    SourceRole → Nat → Nat → K
  | .hashBit, 0, j => s.nonce j
  | .hashBit, 1, j => s.message j
  | .hashBit, 2, j => s.flags j
  | .hashWord, 0, j => s.state j
  | .hashWord, slot + 1, j => s.rounds (slot / 24) (slot % 24) j
  | _, _, _ => 0

/-- **Read a hash witness through a captured checked classifier.** -/
@[expose] def HashSourceValues.valuation {program : RealizedProgram} {I : Interp}
    (s : HashSourceValues (I 0).K) (classifier : SourceRoleClassifier) : program.Valuation I :=
  fun v j => match classifier.lookup v with
    | some (role, slot) => castElt (a := 0) (s.meaning role slot j)
    | none => 0

/-- **A checked lookup selects its exact witness component.** -/
theorem HashSourceValues.valuation_of_lookup {program : RealizedProgram} {I : Interp}
    (s : HashSourceValues (I 0).K) {classifier : SourceRoleClassifier} {v : Nat}
    {role : SourceRole} {slot : Nat} (h : classifier.lookup v = some (role, slot)) (j : Nat) :
    s.valuation (program := program) classifier v j = castElt (s.meaning role slot j) := by
  simp only [valuation, h]

/-- **The round slot selects the stated permutation and round.** -/
theorem HashSourceValues.meaning_round {K : Type} [Zero K] (s : HashSourceValues K)
    (p t j : Nat) (ht : t < 24) :
    s.meaning .hashWord (1 + 24 * p + t) j = s.rounds p t j := by
  have hs : 1 + 24 * p + t = (24 * p + t) + 1 := by omega
  rw [hs]
  simp only [meaning]
  congr 1 <;> omega

end GordieHowe.Falcon512
