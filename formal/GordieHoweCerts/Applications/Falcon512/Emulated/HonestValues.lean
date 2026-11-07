-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Honest.SourceRoles
public import GordieHoweCerts.Applications.Falcon512.Emulated.HonestFull

@[expose] public section

/-!
# The witness components of the emulated Falcon honest strategy

Source roles read an input's hash and selection components, and the naturals of domain `A`. The
values bound to their digits, `magnitudes.mag1` and `norm.squares`, read the natural the digits
denote.
-/

namespace GordieHowe.Falcon512.Emulated

open RealizedProgram
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace
open Native (HonestIn)

set_option linter.unusedSectionVars false

/-- **The computational witness components of emulated Falcon.** -/
structure SourceValues (H S : Type) where
  hash : HashSourceValues H
  rawSamples : Nat → H
  counts : Nat → S
  full : Nat → S
  algebra : Nat → Nat → Nat

/-- **Interpret a role in the value's field.** Statement values are supplied by the statement;
unknown roles and slots contribute zero. The interpretation reads no program syntax. -/
def SourceValues.meaning {I : Interp} {selectField : Nat}
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
def SourceValues.valuation {program : RealizedProgram} {I : Interp}
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

variable (program : RealizedProgram) [FalconACore program] [FalconEAlg program]
  [FalconEHonest program] {FH FA : FieldInterp} [HField FH] [EField FA] [FalconHBase program]
  [FalconHHonest program] [FalconHSelHonest program] [FalconHConsts program FH]
  [FalconSelField program FH FA]

set_option hygiene false in
local notation "interp" => falconInterpOf FH FA

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
  cA : ∀ j, s.algebra 0 j = aNat i.y 595 j
  s2 : ∀ j, s.algebra 1 j = aNat i.y 596 j
  s1 : ∀ j, s.algebra 2 j = aNat i.y 597 j
  mag1 : ∀ j, s.algebra 3 j = Ring.Carrier.mag1 (Native.hIn i.y) j
  mag2 : ∀ j, s.algebra 4 j = aNat i.y 599 j
  low2 : ∀ j, s.algebra 5 j = aNat i.y 600 j
  squares : ∀ j, s.algebra 6 j = Ring.Carrier.squares (Native.hIn i.y)

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

/-- **A committed value of domain `A` at its witness slot.** -/
theorem HonestSourceValues.meaning_algebra {v slot : ℕ} (hv : v ∈ aValues)
    (he : s.algebra slot j = aNat i.y v j) :
    s.meaning (program.valueField v) .aWitness slot j = honestVal program FH FA i v j := by
  rw [honestVal_a i v hv]
  simp only [SourceValues.meaning, he, aVal]

omit hs in
private theorem reader_eq_rdA {e : program.Env interp} {v : ℕ} (hf : program.valueField v = 1)
    (j : ℕ) : program.reader e v j = castElt (a := 1) (rdA e v j) := by
  unfold rdA
  rw [evalE_leaf]
  revert hf
  generalize program.reader e v = r
  generalize program.valueField v = f at r
  intro hf
  subst hf
  rw [castElt_self, castElt_self]

/-- **`magnitudes.mag1` reads its honest natural through its digits.** -/
theorem HonestSourceValues.meaning_mag1 (x : program.Valuation interp)
    (c : ∀ k, (program.layout interp).Ch k) (hj : j < 512) :
    s.meaning (program.valueField 598) .aWitness 3 j =
      program.execOf interp (honestVal program FH FA i) 598 j := by
  have hk := FalconEHonest.mag1Kind (program := program)
  rw [execOf_bound_eq_reader _ (program.srcEnv interp x (honestVal program FH FA i) c 0) rfl hk,
    reader_eq_rdA (FalconEAlg.fields (program := program) 598 (by simp)) j,
    rd_mag1 (honestVal_a i) hj]
  simp only [SourceValues.meaning, hs.mag1]

/-- **`norm.squares` reads its honest natural through its digits.** -/
theorem HonestSourceValues.meaning_squares (x : program.Valuation interp)
    (c : ∀ k, (program.layout interp).Ch k) :
    s.meaning (program.valueField 602) .aWitness 6 0 =
      program.execOf interp (honestVal program FH FA i) 602 0 := by
  have hk := FalconEHonest.sqKind (program := program)
  rw [execOf_bound_eq_reader _ (program.srcEnv interp x (honestVal program FH FA i) c 0) rfl hk,
    reader_eq_rdA (FalconEAlg.fields (program := program) 602 (by simp)) 0,
    rd_sq (honestVal_a i) i.valid]
  simp only [SourceValues.meaning, hs.squares]

end GordieHowe.Falcon512.Emulated
