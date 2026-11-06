-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Honest.SourceRoles
public import GordieHowe.Applications.MLDSA44.Honest.HashVal

public section

namespace GordieHowe.MLDSA44

open RealizedProgram GordieHowe.Keccak GordieHowe.KeccakTrace

variable {program : RealizedProgram} [MldsaHHonest program]
  {F0 FH : FieldInterp} [HField FH] [MldsaHConstsSelect program FH]
  {L : Nat} (y : MLDSA44.PoP.HonestInput 0 L)

set_option hygiene false in
local notation "hashInputs" => (⟨(honestData (K := FH.K) y).buf,
  (fun j => ((flagNat L j : Nat) : FH.K)),
  packWord (honestData (K := FH.K) y).w1,
  packWord (honestData (K := FH.K) y).mu,
  (fun p t j => if hp : p < 10 then if ht : t < 24 then
    stateWords HField.packing
      (iterRounds ((honestData (K := FH.K) y).states ⟨p, hp⟩) (t + 1)) j
    else 0 else 0)⟩ : HashSourceValues FH.K)

/-- **A checked buffer role reads exactly the existing honest hash buffer.** -/
theorem hash_role_buffer {classifier : SourceRoleClassifier}
    (h : classifier.lookup 67 = some (.hashBit, 0)) (j : Nat) :
    (hashInputs).valuation (program := program) (I := mldsaInterpOf F0 FH) classifier 67 j =
      hashVal (program := program) (F0 := F0) y 67 j := by
  rw [HashSourceValues.valuation_of_lookup _ h]
  exact (hashVal_buffer y j).symm

/-- **A checked flag role reads exactly the existing honest prefix flags.** -/
theorem hash_role_flags {classifier : SourceRoleClassifier}
    (h : classifier.lookup 68 = some (.hashBit, 1)) (j : Nat) :
    (hashInputs).valuation (program := program) (I := mldsaInterpOf F0 FH) classifier 68 j =
      hashVal (program := program) (F0 := F0) y 68 j := by
  rw [HashSourceValues.valuation_of_lookup _ h]
  exact (hashVal_flags y j).symm

/-- **A checked `w1` role reads exactly the existing honest packed words.** -/
theorem hash_role_w1 {classifier : SourceRoleClassifier}
    (h : classifier.lookup 69 = some (.hashWord, 0)) (j : Nat) :
    (hashInputs).valuation (program := program) (I := mldsaInterpOf F0 FH) classifier 69 j =
      hashVal (program := program) (F0 := F0) y 69 j := by
  rw [HashSourceValues.valuation_of_lookup _ h]
  exact (hashVal_w1 y j).symm

/-- **A checked digest role reads exactly the existing honest packed digest.** -/
theorem hash_role_mu {classifier : SourceRoleClassifier}
    (h : classifier.lookup 119 = some (.hashWord, 1)) (j : Nat) :
    (hashInputs).valuation (program := program) (I := mldsaInterpOf F0 FH) classifier 119 j =
      hashVal (program := program) (F0 := F0) y 119 j := by
  rw [HashSourceValues.valuation_of_lookup _ h]
  exact (hashVal_mu y j).symm

/-- **A checked round-word role reads exactly the existing honest permutation trace.** -/
theorem hash_role_words {classifier : SourceRoleClassifier} (p : Fin 10) (t : Fin 24)
    (h : classifier.lookup (wordsVal p t) = some (.hashWord, 2 + 24 * (p : Nat) + (t : Nat))) (j : Nat) :
    (hashInputs).valuation (program := program) (I := mldsaInterpOf F0 FH)
      classifier (wordsVal p t) j =
      hashVal (program := program) (F0 := F0) y (wordsVal p t) j := by
  rw [HashSourceValues.valuation_of_lookup _ h, HashSourceValues.meaning_round _ _ _ _ t.isLt]
  simp only [dite_eq_left p.isLt, dite_eq_left t.isLt]
  exact (hashVal_words y p t j).symm

end GordieHowe.MLDSA44
