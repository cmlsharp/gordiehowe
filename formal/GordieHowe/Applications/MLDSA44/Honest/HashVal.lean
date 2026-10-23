-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Honest.Data

@[expose] public section

/-!
# GordieHowe: the honest values of an ML-DSA program's hash

The honest committed values of domain `H`'s hash (`hashVal`): the message buffer and its flags,
`w1`'s and `μ`'s words, the rounds' words, all from the honest data (`honestData`). At an
environment reading committed values agreeing with them (`GordieHowe.RealizedProgram.ReadsCells`, such as the source
environment), the round predicates and `μ`'s padding hold (`rounds_holds_honest`,
`pad_holds_hashVal`).
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open Generated.MLDSA44.Native.ROMParams.Program
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

/-- **The round whose committed words are value `v`**, the first such. -/
def wordsOwner? (v : ℕ) : Option (Fin 10 × Fin 24) :=
  ((List.finRange 10).flatMap fun p => (List.finRange 24).map fun t => (p, t)).find?
    fun pt => wordsVal pt.1 pt.2 == v

/-- The rounds' words are distinct values, none the buffer, the flags, `w1`'s or `μ`'s words,
decided. -/
theorem wordsOwner_checks : (∀ p t, wordsOwner? (wordsVal p t) = some (p, t)) ∧
    wordsOwner? 68 = none ∧ wordsOwner? 69 = none ∧ wordsOwner? 70 = none ∧
    wordsOwner? 120 = none := by
  decide +kernel

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaHHonest program] {F0 FH : RealizedProgram.FieldInterp} [HField FH]
  [MldsaHConstsSelect program FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

section Values

variable {L : ℕ} (y : MLDSA44.PoP.HonestInput 0 L)

/-- **The packed words of a bit function** `f`: word `i` the packing of bits `16 i … 16 i + 15`. -/
-- spec-side
noncomputable def packWord (f : ℕ → FH.K) (i : ℕ) : FH.K :=
  PackedClaim.pack HField.packing fun b => decide (f (16 * i + b) = 1)

/-- **The honest values of the hash's committed inputs**: the buffer the honest data's buffer
bits, the flags the prefix of length `66 + L`, `w1`'s and `μ`'s words their bits packed, the rounds'
words the packed states of the honest trace; `0` elsewhere.

Running time: a prover computing these values would take ten Keccak-f permutations (the trace) and
`16` packing sums per word. This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def hashVal (v i : ℕ) : (interp (program.valueField v)).K :=
  if v = 68 then RealizedProgram.castElt (a := 1) ((honestData (K := FH.K) y).buf i)
  else if v = 69 then RealizedProgram.castElt (a := 1) ((flagNat L i : ℕ) : FH.K)
  else if v = 70 then RealizedProgram.castElt (a := 1) (packWord (honestData (K := FH.K) y).w1 i)
  else if v = 120 then RealizedProgram.castElt (a := 1) (packWord (honestData (K := FH.K) y).mu i)
  else match wordsOwner? v with
    | some pt => RealizedProgram.castElt (a := 1) (RealizedProgram.stateWords HField.packing
        (iterRounds ((honestData (K := FH.K) y).states pt.1) ((pt.2 : ℕ) + 1)) i)
    | none => 0

/-- **Value `v` is a committed input of the hash.** -/
def IsHashValue (v : ℕ) : Prop :=
  v = 68 ∨ v = 69 ∨ v = 70 ∨ v = 120 ∨ (wordsOwner? v).isSome

instance (v : ℕ) : Decidable (IsHashValue v) := by unfold IsHashValue; infer_instance

end Values

section Agree

variable {L : ℕ} {y : MLDSA44.PoP.HonestInput 0 L} {e : program.Env interp}
  {val : program.Valuation interp} (hr : program.ReadsCells 1 e val)
  (h : ∀ v, IsHashValue v → val v = hashVal y v)

set_option hygiene false in
local notation "RD" => program.reader e

include hr h

omit hr in
theorem wordsAgree_of_hashVal : WordsAgree val (honestData (K := FH.K) y).states := by
  obtain ⟨hw, h68, h69, h70, h120⟩ := wordsOwner_checks
  refine ⟨fun p t i _ => ?_⟩
  have hv : wordsVal p t ≠ 68 ∧ wordsVal p t ≠ 69 ∧ wordsVal p t ≠ 70 ∧ wordsVal p t ≠ 120 := by
    refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_⟩ <;>
      · have := hw p t
        rw [h'] at this
        simp_all
  rw [h _ (Or.inr (Or.inr (Or.inr (Or.inr (by rw [hw p t]; rfl)))))]
  unfold hashVal
  rw [if_neg hv.1, if_neg hv.2.1, if_neg hv.2.2.1, if_neg hv.2.2.2, hw p t]

theorem inputsAgree_of_hashVal
    (htr : ∀ j < 512, (RealizedProgram.castElt (b := 1) (e.stmt 67 j) : (interp 1).K) = (honestData (K := FH.K) y).tr j) :
    InputsAgree RD (honestData (K := FH.K) y) :=
  inputsAgree_of hr (honestData_bool y) htr
    (fun j _ => by rw [h _ (Or.inl rfl)]; rfl)
    (fun i _ => by rw [h _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; rfl)
    (fun i _ => by rw [h _ (Or.inr (Or.inr (Or.inl rfl)))]; rfl)

/-- **The flags read the prefix of length `66 + L`.** -/
theorem flag_honest {i : ℕ} (hi : i < 136) :
    flag e i = ((flagNat L i : ℕ) : (interp 1).K) := by
  obtain ⟨-, -, hp, hf⟩ := MldsaHHonest.priv6869 (program := program)
  unfold flag
  rw [RealizedProgram.evalE_leaf, hr hp hf
    (by rw [(pad_facts (program := program)).2.2.1]; exact hi),
    h _ (Or.inr (Or.inl rfl))]
  exact RealizedProgram.castElt_castElt_of_eq hf.symm _

/-- **The buffer bytes past `66` read the honest buffer bytes.** -/
theorem bufByte_honest {i : ℕ} (hi : i < 136) (h66 : 66 ≤ i) :
    bufByte e i =
      fun u : Fin 8 => constBit (K := (interp 1).K) (bufNat L (msgNat y) i) u := by
  obtain ⟨hp, hf, -, -⟩ := MldsaHHonest.priv6869 (program := program)
  funext u
  have hu := u.isLt
  unfold bufByte
  rw [evalE_ref11 _ (by omega), if_neg (by omega), if_neg (by omega), RealizedProgram.evalE_leaf,
    hr hp hf
      (by rw [(pad_facts (program := program)).2.2.2.1]; omega), h _ (Or.inl rfl)]
  rw [show hashVal y 68 (8 * i + u - 528) = RealizedProgram.castElt (a := 1)
    ((honestData (K := FH.K) y).buf (8 * i + u - 528)) from rfl, RealizedProgram.castElt_castElt_of_eq hf.symm]
  simp only [honestData, data0]
  rw [show 66 + (8 * i + (u : ℕ) - 528) / 8 = i by omega, show (8 * i + (u : ℕ) - 528) % 8 = u by omega]

/-- **The round predicates hold at honest hash values.** -/
theorem rounds_holds_honest
    (htr : ∀ j < 512, (RealizedProgram.castElt (b := 1) (e.stmt 67 j) : (interp 1).K) = (honestData (K := FH.K) y).tr j)
    (p : Fin 10) (t : Fin 24) :
    program.HoldsWith RD (program.predicate (roundPred p t)).body :=
  trace_holds hr (honestData_bool y) (inputsAgree_of_hashVal hr h htr) (wordsAgree_of_hashVal h) p t

/-- **`μ`'s padding holds at honest hash values**, for a message of at most `32` bytes. -/
theorem pad_holds_hashVal (hL : L ≤ 32)
    (htr : ∀ j < 512, (RealizedProgram.castElt (b := 1) (e.stmt 67 j) : (interp 1).K) = (honestData (K := FH.K) y).tr j)
    {q : ℕ} (hq : q ∈ [42, 43, 44, 45, 46, 47]) :
    program.HoldsWith RD (program.predicate q).body := by
  have hmsg : ∀ k, msgNat y k < 256 := fun k => by
    unfold msgNat
    split_ifs
    · exact UInt8.toNat_lt _
    · norm_num
  have hp : ∀ {q}, q ∈ [42, 43, 44, 45, 46] → program.HoldsWith RD (program.predicate q).body :=
    fun hq => pad_holds_honest _ hL hmsg (fun i hi => flag_honest hr h hi)
      (fun i hi h66 => bufByte_honest hr h hi h66) hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp (by simp)
  · exact hp (by simp)
  · exact hp (by simp)
  · exact hp (by simp)
  · exact hp (by simp)
  refine pad47_of _ fun j hj => ?_
  have hin := inputsAgree_of_hashVal hr h htr
  rw [hin.mu j hj, show (119 : ℕ) = outVal (0 : Fin 10) (23 : Fin 24) from rfl,
    evalE_out hr (honestData_bool y) (wordsAgree_of_hashVal h) 0 23 (by omega)]
  rfl

/-- **The stream's bits read the honest stream**: bit `t` is bit `t mod 1088` of Keccak-f of the
stream's absorbed state (`t < 1088`) or of its squeeze state. -/
theorem sibBits_honest (t : Fin (8 * 272)) :
    sibBits RD t = RealizedProgram.stateBit (iterRounds (if (t : ℕ) < 1088 then (honestData (K := FH.K) y).sbState
      else iterRounds (honestData (K := FH.K) y).sbState 24) 24) ((t : ℕ) % 1088) := by
  have ht := t.isLt
  have hb := honestData_bool (K := FH.K) y
  have hw := wordsAgree_of_hashVal h
  have h8 : (honestData (K := FH.K) y).states 8 = (honestData (K := FH.K) y).sbState := by
    simp [HashData.states]
  have h9 : (honestData (K := FH.K) y).states 9 = iterRounds (honestData (K := FH.K) y).sbState 24 := by
    simp [HashData.states]
  unfold sibBits
  split_ifs with h1
  · rw [evalE_555 _ h1, show (506 : ℕ) = outVal (8 : Fin 10) (23 : Fin 24) from rfl,
      evalE_out hr hb hw 8 23 (by omega), h8, Nat.mod_eq_of_lt h1]
    rfl
  · rw [evalE_556 _ (by omega), show (554 : ℕ) = outVal (9 : Fin 10) (23 : Fin 24) from rfl,
      evalE_out hr hb hw 9 23 (by omega), h9, show (t : ℕ) % 1088 = t - 1088 by omega]
    rfl

end Agree

end GordieHowe.MLDSA44.Native.ROMParams
