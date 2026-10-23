-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.HonestValues

@[expose] public section

/-!
# GordieHowe: the source predicates of a native ML-DSA program at its honest values

At the source environment of the honest values (`honestVal`) on an honest input at its key's
statement, every predicate of a native ML-DSA program other than the MAC's holds (`source_holds`):
the hash's rounds and `μ`'s padding (`GordieHowe/Applications/MLDSA44/Honest/HashVal.lean`), SampleInBall
(`GordieHowe/Applications/MLDSA44/Native/ROMParams/HonestSelect.lean`), domain `A`'s (`GordieHowe/Applications/MLDSA44/Native/ROMParams/HonestValues.lean`), the blind's
Booleanity and the crossing `mac.equal` (here). This file also proves the MAC's source facts
(`srcMac_holds`).
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open GordieHowe.Bits RealizedProgram

set_option linter.unusedSectionVars false

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

/-! ## Bits of domain `A` read as naturals -/

section Bits

variable {F0 FH : FieldInterp} [QField F0]

/-- The integer reading of a bit constant in domain `A`'s field. -/
theorem toNatA_ite (p : Prop) [Decidable p] :
    (interp 0).toNat (if p then (1 : (interp 0).K) else 0) = if p then 1 else 0 := by
  split_ifs
  · exact_mod_cast QField.toNat_natCast (F0 := F0) (k := 1) (by norm_num)
  · exact_mod_cast QField.toNat_natCast (F0 := F0) (k := 0) (by norm_num)

theorem toNatA_zero : (interp 0).toNat 0 = 0 := by
  have := toNatA_ite (F0 := F0) (FH := FH) False
  simpa using this

theorem toNatA_one : (interp 0).toNat 1 = 1 := by
  have := toNatA_ite (F0 := F0) (FH := FH) True
  simpa using this

theorem tern1_A (z : ℤ) : (interp 0).toNat (HashCircuit.ternaryBits (K := (interp 0).K) z).1 =
    if z = 0 then 0 else 1 := by
  rw [show (HashCircuit.ternaryBits (K := (interp 0).K) z).1 = if z = 0 then 0 else 1 from rfl]
  split_ifs
  · exact toNatA_zero
  · exact toNatA_one

theorem tern2_A (z : ℤ) : (interp 0).toNat (HashCircuit.ternaryBits (K := (interp 0).K) z).2 =
    if z = -1 then 1 else 0 := by
  rw [show (HashCircuit.ternaryBits (K := (interp 0).K) z).2 = if z = -1 then 1 else 0 from rfl]
  exact toNatA_ite _

end Bits

variable {program : RealizedProgram} [MldsaAAlgebra program] [MldsaHHonest program] [MldsaHShuffle program]
  [MldsaHSelHonest program] {F0 FH : FieldInterp} [QField F0] [HField FH]
  [MldsaHConsts program FH] [MldsaHNativeData FH] [MldsaHNodes FH]
  [hN : MldsaNativeHonest program F0 FH]

open MldsaNativeHonest

section Src

variable (i : MLDSA44.HonestInput) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH i) c π

/-- **The key's statement holds `tr`'s bits** as the honest hash data's. -/
theorem htr_honest (hx : x = hN.stmtOfKey i.y.key) : ∀ j < 512,
    (castElt (b := 1) (x 67 j) : (interp 1).K) = (honestData (K := FH.K) i.y).tr j := by
  intro j hj
  rw [hx, stmt67 (program := program) i.y.key j hj]
  change _ = constBit (trNat i.y (j / 8)) (j % 8)
  unfold trNat
  rw [dif_pos (by omega)]

/-! ## The crossing `mac.equal` -/

/-- **The crossing's coordinates agree** at the honest values: H's `w1` bits and decoded challenge
bits are A's `hint.w1` and challenge bits, read as naturals; A's are bits. -/
theorem cross_coords (hx : x = hN.stmtOfKey i.y.key) {j : ℕ} (hj : j < 6656) :
    (interp 1).toNat (program.evalE (program.reader E) 1 (.ref 525) j) =
        (interp 0).toNat (program.evalE (program.reader E) 0 (.ref 7) j) ∧
      (program.evalE (program.reader E) 0 (.ref 7) j = 0 ∨
        program.evalE (program.reader E) 0 (.ref 7) j = 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, h60, -, h63, -⟩ := (a_bound (program := program))
  by_cases hlo : j < 6144
  · rw [xH_lo i (readsCells_honest i x c π) (htr_honest i hx) hlo, y_lo _ hlo]
    change _ = (interp 0).toNat (rdA E 63 j) ∧ (rdA E 63 j = 0 ∨ rdA E 63 j = 1)
    rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [h63]; exact hlo), aVal_63 i hlo]
    have hw : MLDSA44.NativeAlgebraCircuit.outputBits (nativeA F0 i).w1A ⟨j / 6, by change j / 6 < 4 * 256; omega⟩
        ⟨j % 6, by change j % 6 < 6; omega⟩ =
        constBit (K := (interp 0).K) (w1Nat i.y (j / 8)) (j % 8) := by
      unfold MLDSA44.NativeAlgebraCircuit.outputBits w1Nat
      rw [dif_pos (by omega)]
      change Falcon512.HashCircuit.wiresOfByteVec (K := F0.K)
        (fun p => (Native.honestW1Bytes i.y p).toNat) _ = _
      unfold Falcon512.HashCircuit.wiresOfByteVec
      simp only [show mldsa44.r1_bits * (j / 6) + j % 6 = j by
        change 6 * (j / 6) + j % 6 = j; omega]
    rw [hw]
    unfold constBit
    refine ⟨by rw [toNatH_ite, toNatA_ite], ?_⟩
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < 256, j = 6144 + 2 * k ∨ j = 6144 + (2 * k + 1) :=
      ⟨(j - 6144) / 2, by omega, by omega⟩
    · rw [xH_even i (readsCells_honest i x c π) hk, y_hi _ (by omega)]
      change _ = (interp 0).toNat (rdA E 60 (2 * k)) ∧ (rdA E 60 (2 * k) = 0 ∨ rdA E 60 (2 * k) = 1)
      rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [h60]; omega), aVal_60 i (by omega)]
      have hcA : (nativeA F0 i).cA ⟨2 * k / 2, by change 2 * k / 2 < 256; omega⟩
          ⟨2 * k % 2, by omega⟩ =
          (HashCircuit.ternaryBits (K := (interp 0).K) (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).1 := by
        have e1 : 2 * k / 2 = k := by omega
        have e2 : 2 * k % 2 = 0 := by omega
        simp only [e1, e2]
        rfl
      rw [hcA, tern1_H, tern1_A]
      refine ⟨rfl, ?_⟩
      rw [show (HashCircuit.ternaryBits (K := (interp 0).K) (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).1 =
        if i.y.c (Fin.cast cdeg ⟨k, hk⟩) = 0 then 0 else 1 from rfl]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [xH_odd i (readsCells_honest i x c π) hk, y_hi _ (by omega)]
      change _ = (interp 0).toNat (rdA E 60 (2 * k + 1)) ∧
        (rdA E 60 (2 * k + 1) = 0 ∨ rdA E 60 (2 * k + 1) = 1)
      rw [rdA_honest (i := i) (x := x) (c := c) (π := π) (by decide) (by rw [h60]; omega), aVal_60 i (by omega)]
      have hcA : (nativeA F0 i).cA ⟨(2 * k + 1) / 2, by change (2 * k + 1) / 2 < 256; omega⟩
          ⟨(2 * k + 1) % 2, by omega⟩ =
          (HashCircuit.ternaryBits (K := (interp 0).K) (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).2 := by
        have e1 : (2 * k + 1) / 2 = k := by omega
        have e2 : (2 * k + 1) % 2 = 1 := by omega
        simp only [e1, e2]
        rfl
      rw [hcA, tern2_H, tern2_A]
      refine ⟨rfl, ?_⟩
      rw [show (HashCircuit.ternaryBits (K := (interp 0).K) (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).2 =
        if i.y.c (Fin.cast cdeg ⟨k, hk⟩) = -1 then 1 else 0 from rfl]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl

/-- **`mac.equal` holds** at the honest values. -/
theorem cross_holds (hx : x = hN.stmtOfKey i.y.key) :
    program.HoldsWith (program.reader E) (program.predicate 272).body := by
  rw [hb (program := program)]
  have hl : program.exprLen (.ref 525) = 6656 := MldsaACross.len525
  have h1 : program.domainField 1 = 1 := MldsaHCross.domainField1
  have h0 : program.domainField 0 = 0 := MldsaACross.domainField0
  refine ⟨fun j hj => ?_, fun _ j hj => ?_⟩
  · rw [hl] at hj
    unfold RealizedProgram.evalWith
    rw [h0]
    rcases (cross_coords i hx hj).2 with h | h <;> rw [h]
    · rw [toNatA_zero]
      norm_num
    · rw [toNatA_one]
      norm_num
  · rw [hl] at hj
    unfold RealizedProgram.evalWith
    rw [h0, h1]
    exact (cross_coords i hx hj).1

/-- **Every source predicate other than the MAC's holds** at the source environment of the honest
values, at the key's statement (the realization's predicates `5` and `10` are no source predicates,
`MldsaNativeHonest.realPreds`). -/
theorem source_holds (hx : x = hN.stmtOfKey i.y.key) {q : ℕ} (hq : q < program.predicates.length)
    (hr : q ∉ macRolePreds) (hsrc : program.inSource (program.predicate q) = true) :
    program.HoldsWith (program.reader E) (program.predicate q).body := by
  have hreal : ∀ q ∈ [5, 10], program.inSource (program.predicate q) = true → False :=
    fun q hq h => by
      rw [MldsaNativeHonest.realPreds (program := program) q hq] at h
      cases h
  have hlen := predicates_length (program := program)
  rw [hlen] at hq
  simp only [macRolePreds, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hr
  obtain ⟨h4, h15, h16, h17, h271⟩ := hr
  by_cases hh : 18 ≤ q ∧ q < 264
  · exact hash_holds i (readsCells_honest i x c π) (htr_honest i hx) hh.1 hh.2
  by_cases hs : 264 ≤ q ∧ q < 271
  · exact sample_holds i (readsCells_honest i x c π)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
  by_cases h272 : q = 272
  · subst h272
    exact cross_holds i hx
  have hA : q < 18 := by omega
  interval_cases q
  · exact sig_honest i hx
  · exact w1bound_honest i
  · exact decompose_honest i
  · exact interval_honest i
  · exact absurd rfl h4
  · exact (hreal 5 (by decide) hsrc).elim
  · exact bools_honest i (by simp)
  · exact bools_honest i (by simp)
  · exact bools_honest i (by simp)
  · exact bools_honest i (by simp)
  · exact (hreal 10 (by decide) hsrc).elim
  · exact norm_honest i
  · exact offset_honest i
  · exact slack_honest i
  · exact weight_honest i
  · exact absurd rfl h15
  · exact absurd rfl h16
  · exact absurd rfl h17

/-- The integer reading of a bit of domain `A` that is not a constant is its indicator. -/
theorem intOf_bitA {v j : ℕ} (hc : program.isConstant v = false) (hf : program.valueField v = 0)
    (hb : rdA E v j = 0 ∨ rdA E v j = 1) :
    program.intOf (program.reader E) v j = if rdA E v j = 1 then 1 else 0 := by
  rcases hb with h | h
  · rw [intOf_of_rdA E hc hf (k := 0) (by norm_num) (by rw [h]; simp), if_neg (by rw [h]; simp)]
    rfl
  · rw [intOf_of_rdA E hc hf (k := 1) (by norm_num) (by rw [h]; simp), if_pos h]
    rfl

/-- **The MAC's source facts hold** at the honest values: `mac.equal`, its operands' bits and the A
operand's integer reading. -/
theorem srcMac_holds (hx : x = hN.stmtOfKey i.y.key) :
    hN.mac.Source (program.reader E) := by
  have hl : program.exprLen (.ref 525) = 6656 := MldsaACross.len525
  have hl7 := len7 (program := program)
  have h1 : program.domainField 1 = 1 := MldsaHCross.domainField1
  have h0 : program.domainField 0 = 0 := MldsaACross.domainField0
  obtain ⟨-, -, -, -, -, -, -, -, h60, -, h63, -⟩ := (a_bound (program := program))
  obtain ⟨hc63, hc60, hf63, hf60⟩ := cross_vals (program := program)
  have hc6 := MldsaACross.const6 (program := program)
  have he6 := MldsaACross.entries6 (program := program)
  have hf6 := MldsaACross.field6 (program := program)
  have hcr := cross_holds i (c := c) (π := π) hx
  rw [hb (program := program)] at hcr
  obtain ⟨hdx, hx5, hdy, hy7, hk, hcdy, hcy⟩ := mac_shape (program := program)
  constructor
  · rw [hdx, hx5, hcdy, hcy, hk]
    exact hcr
  all_goals simp only [hx5, hy7]
  · rw [hdx]
    intro j hj
    rw [hl] at hj
    change program.evalE _ (program.domainField 1) _ j = 0 ∨ program.evalE _ (program.domainField 1) _ j = 1
    rw [h1]
    exact xH_bits i (readsCells_honest i x c π) hj
  · rw [hdy]
    intro j hj
    rw [hl7] at hj
    change program.evalE _ (program.domainField 0) _ j = 0 ∨ program.evalE _ (program.domainField 0) _ j = 1
    rw [h0]
    exact (cross_coords i hx hj).2
  · rw [hdy]
    intro j hj
    rw [hl7] at hj
    change program.evalIntWith _ 0 (.ref 7) j =
      if program.evalE _ (program.domainField 0) (.ref 7) j = 1 then 1 else 0
    rw [h0, RealizedProgram.evalIntWith_ref MldsaHCross.refsOrdered _ _ MldsaACross.lt7, MldsaACross.expr7,
      RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_reindex,
      RealizedProgram.evalIntWith_concat, RealizedProgram.evalIntWith_concat]
    by_cases hlo : j < 6144
    · rw [idx10_lo j hlo, idx11_lo j hlo, MldsaACross.len63, MldsaACross.len60, if_pos hlo,
        if_neg (lt_irrefl _), Nat.sub_self, RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf,
        intOf_constA _ hc6 hf6 (by rw [he6]; norm_num), he6, y_lo _ hlo]
      change _ = if rdA E 63 j = 1 then 1 else 0
      rw [intOf_bitA i hc63 hf63 (w1Bits_bool i (j / 6) (by omega) (j % 6) (by omega) |>.imp
        (fun h => by rwa [Nat.div_add_mod] at h) (fun h => by rwa [Nat.div_add_mod] at h))]
      simp
    · obtain ⟨k, hk, rfl⟩ : ∃ k < 512, j = 6144 + k := ⟨j - 6144, by omega, by omega⟩
      rw [idx10_hi k hk, idx11_hi k hk, MldsaACross.len63, MldsaACross.len60,
        if_neg (lt_irrefl _), Nat.sub_self, if_pos hk, RealizedProgram.evalIntWith_leaf,
        RealizedProgram.evalIntWith_leaf, intOf_constA _ hc6 hf6 (by rw [he6]; norm_num), he6,
        y_hi _ hk]
      change _ = if rdA E 60 k = 1 then 1 else 0
      rw [intOf_bitA i hc60 hf60 (h60_bool i k hk)]
      simp

end Src

end GordieHowe.MLDSA44.Native.ROMParams
