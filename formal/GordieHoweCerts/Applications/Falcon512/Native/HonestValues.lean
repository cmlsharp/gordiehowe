-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.Falcon512.Native.HonestFull
public import GordieHowe.Applications.Falcon512.Native.SourceRoles

@[expose] public section

/-!
# The witness components of the native Falcon honest strategy

An honest input's components (`honestSourceValues`), read through a source role's meaning
(`SourceValues.meaning`), are the honest values of the role's value: the hash's bits and words, the
selection's values and the natural digits of domain `A`.
-/

namespace GordieHowe.Falcon512.Native

open RealizedProgram
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

set_option linter.unusedSectionVars false

variable (program : RealizedProgram) [FalconACore program] [Norm.FalconNorm program]
  [Norm.FalconNormHonest program] [FalconAHonest program] {FH FA : FieldInterp} [HField FH]
  [AField FA] [FalconHBase program] [FalconSelField program FH FA]

set_option hygiene false in
local notation "interp" => falconInterpOf FH FA

variable [FalconHHonest program] [FalconHSelHonest program] [FalconHConsts program FH]
  [FalconHValues program]

variable (FH FA) in
/-- **The witness components of an honest input**, as equations: each component is the honest
value of its role. -/
structure HonestSourceValues (i : HonestIn)
    (s : SourceValues (interp 0).K (interp (SelectShape.field program selShape)).K) : Prop where
  nonce : ∀ j, s.hash.nonce j =
    if h : j < 320 then hBlock FH i.y ⟨j / 8, by omega⟩ ⟨j % 8, by omega⟩ else 0
  message : ∀ j, s.hash.message j =
    if h : j < 768 then hBlock FH i.y ⟨40 + j / 8, by omega⟩ ⟨j % 8, by omega⟩ else 0
  flags : ∀ j, s.hash.flags j = if j < 40 + i.L then 1 else 0
  state : ∀ j, s.hash.state j = stateWords HField.packing (hStarts FH i.y 1) j
  rounds : ∀ p t j, s.hash.rounds p t j =
    stateWords HField.packing (iterRounds (hStarts FH i.y p) (t + 1)) j
  rawSamples : ∀ j, s.rawSamples j = PackedClaim.pack (HField.packing (FH := FH)) fun b =>
    decide (Bits.constBit (K := FH.K) (if h : j < 512 then i.y.samples ⟨j, h⟩ else 0) b = 1)
  counts : ∀ j, s.counts j = if h : j < 717 then (hRoute program FH FA i.y ⟨j, h⟩).count_enc else 0
  full : ∀ j, s.full j =
    if h : j < 205 then (hRoute program FH FA i.y ⟨512 + j, by omega⟩).full else 0
  algebra : ∀ slot j, slot < 10 → s.algebra slot j = hNat program i.y (594 + slot) j

private theorem castElt_zero {I : Interp} {a b : ℕ} : castElt (I := I) (a := a) (b := b) 0 = 0 := by
  by_cases h : a = b
  · subst h
    rw [castElt_self]
  · exact castElt_of_ne h 0

variable {program} {i : HonestIn}
  {s : SourceValues (interp 0).K (interp (SelectShape.field program selShape)).K}
  (hs : HonestSourceValues program FH FA i s) (j : ℕ)
include hs

theorem HonestSourceValues.meaning_nonce :
    s.meaning (program.valueField 45) .hashBit 0 j = honestVal program FH FA i 45 j := by
  rw [honestVal_hash i 45 (Or.inl rfl), hashVal_nonce]
  simp only [SourceValues.meaning, HashSourceValues.meaning, hs.nonce]
  split
  · rfl
  · exact castElt_zero

theorem HonestSourceValues.meaning_message :
    s.meaning (program.valueField 46) .hashBit 1 j = honestVal program FH FA i 46 j := by
  rw [honestVal_hash i 46 (Or.inr (Or.inl rfl)), hashVal_message]
  simp only [SourceValues.meaning, HashSourceValues.meaning, hs.message]
  split
  · rfl
  · exact castElt_zero

theorem HonestSourceValues.meaning_flags :
    s.meaning (program.valueField 47) .hashBit 2 j = honestVal program FH FA i 47 j := by
  rw [honestVal_hash i 47 (Or.inr (Or.inr (Or.inl rfl))), hashVal_flags]
  simp only [SourceValues.meaning, HashSourceValues.meaning, hs.flags]

theorem HonestSourceValues.meaning_state :
    s.meaning (program.valueField 96) .hashWord 0 j = honestVal program FH FA i 96 j := by
  rw [honestVal_hash i 96 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hashVal_state]
  simp only [SourceValues.meaning, HashSourceValues.meaning, hs.state]

theorem HonestSourceValues.meaning_round (p : Fin 11) (t : Fin 24) :
    s.meaning (program.valueField (wordsVal p t)) .hashWord (1 + 24 * p + t) j =
      honestVal program FH FA i (wordsVal p t) j := by
  have ho : (wordsOwner? (wordsVal p t)).isSome = true := by
    rw [wordsOwner_checks.1 p t]
    rfl
  rw [honestVal_hash i _ (Or.inr (Or.inr (Or.inr (Or.inr ho)))), hashVal_round]
  simp only [SourceValues.meaning]
  rw [HashSourceValues.meaning_round _ _ _ _ t.isLt, hs.rounds]

theorem HonestSourceValues.meaning_raw :
    s.meaning (program.valueField 588) .selection 0 j = honestVal program FH FA i 588 j := by
  rw [honestVal_sel i 588 (by simp), selVal_raw]
  simp only [SourceValues.meaning, hs.rawSamples]

theorem HonestSourceValues.meaning_count :
    s.meaning (program.valueField 590) .selection 1 j = honestVal program FH FA i 590 j := by
  rw [honestVal_sel i 590 (by simp), selVal_count]
  simp only [SourceValues.meaning, hs.counts]

theorem HonestSourceValues.meaning_full :
    s.meaning (program.valueField 591) .selection 2 j = honestVal program FH FA i 591 j := by
  rw [honestVal_sel i 591 (by simp), selVal_full]
  simp only [SourceValues.meaning, hs.full]

/-- **A value of domain `A` at its witness slot.** -/
theorem HonestSourceValues.meaning_algebra {slot : ℕ} (hslot : slot < 10)
    (hv : 594 + slot ∈ NormValues program) :
    s.meaning (program.valueField (594 + slot)) .aWitness slot j =
      honestVal program FH FA i (594 + slot) j := by
  rw [honestVal_norm i _ hv, algVal_of_mem i.y hv]
  simp only [SourceValues.meaning, hs.algebra slot j hslot]

end GordieHowe.Falcon512.Native
