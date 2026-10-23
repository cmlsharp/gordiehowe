-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.HonestValues

@[expose] public section

/-!
# GordieHowe: the source predicates of an emulated ML-DSA program at its honest values

At the source environment of the honest values (`honestVal`) on an honest input at its key's
statement, every predicate of an emulated ML-DSA program other than the MAC's holds
(`source_holds`): domain `H`'s predicates `20 … 272` are the native program's `18 … 270` renamed
(`MldsaEmbed`), which hold in the environment read as the native program's
(`GordieHowe.MLDSA44.Native.ROMParams.hPreds_holds`, `GordieHowe.RealizedProgram.holdsAt_pullEnv`); domain `A`'s
(`GordieHowe/Applications/MLDSA44/Emulated/HonestValues.lean`); the blind's Booleanity and the crossing `mac.equal` (here). This
file also proves the MAC's source facts (`srcMac_holds`).
-/

namespace GordieHowe.MLDSA44.Emulated

open GordieHowe.Bits RealizedProgram
open MLDSA44 (HonestInput)
open Native.ROMParams (hVal MldsaHHash MldsaHSample MldsaHConsts MldsaHHonest MldsaHShuffle MldsaHSelHonest MldsaHNativeData MldsaHNodes honestData trNat w1Nat cdeg)


set_option linter.unusedSectionVars false

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => MldsaEmbed.nat program

variable {program : RealizedProgram} [MldsaEAlgebra program] {F0 FH : FieldInterp} [AField F0]
  [HField FH] [MldsaHHonest nat] [MldsaHSample nat] [MldsaHSelHonest nat]
  [MldsaHConsts nat FH] [Native.ROMParams.MldsaHNativeData FH] [MldsaHNodes FH]
  [hE : MldsaEmulatedHonest program F0 FH]

open MldsaEmulatedHonest

section Src

variable (i : HonestInput) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH i) c π

/-- **The environment read as the native program's holds `tr`'s bits** as the honest hash data's,
at the key's statement. -/
theorem htr_pull (hx : x = hE.stmtOfKey i.y.key) : ∀ j < 512,
    (castElt (b := 1) ((pull E).stmt 67 j) : (interp 1).K) = (honestData (K := FH.K) i.y).tr j := by
  intro j hj
  have h67 : (67 : ℕ) ∈ hV := by decide
  have hst : (pull E).stmt 67 j = castElt (x 68 j) := by
    change (if (67 : ℕ) ∈ hV then castElt (x (σ.val 67) j) else 0) = _
    rw [if_pos h67]
    rfl
  obtain ⟨hn, hf⟩ := MldsaEMain.trFields (program := program)
  rw [hst, castElt_castElt_eq, if_pos (hf.trans hn.symm), hx, stmt68 (program := program) i.y.key j hj]
  change _ = constBit (trNat i.y (j / 8)) (j % 8)
  unfold trNat
  rw [dif_pos (by omega)]

/-- **Domain `H`'s predicates hold** at the honest values: the native program's, renamed. -/
theorem hash_holds (hx : x = hE.stmtOfKey i.y.key) {q : ℕ} (h20 : 20 ≤ q) (h272 : q ≤ 272) :
    program.HoldsWith (program.reader E) (program.predicate q).body := by
  obtain ⟨hc, -, -⟩ := MldsaEmbed.predCorr (program := program) (q - 2) (by omega) (by omega)
  rw [show q = q - 2 + 2 by omega]
  exact (RealizedProgram.holdsAt_pullEnv MldsaEmbed.embedding E hc).2
    (Native.ROMParams.hPreds_holds i (readsCells_honest i x c π) (htr_pull i hx) (by omega)
      (by omega))

/-! ## The crossing `mac.equal` -/

omit [MldsaHHonest nat] [MldsaHSample nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]
  [Native.ROMParams.MldsaHNativeData FH] [MldsaHNodes FH] hE in
/-- The integer reading of a bit constant in domain `A`'s field. -/
theorem toNatA_ite (p : Prop) [Decidable p] :
    (interp 0).toNat (if p then (1 : (interp 0).K) else 0) = if p then 1 else 0 := by
  split_ifs
  · exact toNatE_one
  · exact toNatE_zero

/-- **The crossing's coordinates agree** at the honest values: H's `w1` bits and decoded challenge
bits are A's `hint.w1` and challenge bits, read as naturals; A's are bits. -/
theorem cross_coords (hx : x = hE.stmtOfKey i.y.key) {j : ℕ} (hj : j < 6656) :
    (interp 1).toNat (program.evalE (program.reader E) 1 (.ref 527) j) =
        (interp 0).toNat (program.evalE (program.reader E) 0 (.ref 6) j) ∧
      (program.evalE (program.reader E) 0 (.ref 6) j = 0 ∨
        program.evalE (program.reader E) 0 (.ref 6) j = 1) := by
  have h61 := size61 (program := program)
  have h64 := size64 (program := program)
  have hr := readsCells_honest i x c π
  rw [x_eq E]
  by_cases hlo : j < 6144
  · rw [Native.ROMParams.xH_lo i hr (htr_pull i hx) hlo, y_lo E hlo]
    change _ = (interp 0).toNat (rdA E 64 j) ∧ (rdA E 64 j = 0 ∨ rdA E 64 j = 1)
    rw [rdA_honest_fixed (i := i) (x := x) (c := c) (π := π) (by simp) (by rw [h64]; exact hlo),
      aVal_64 _ i hlo]
    have hw : NativeAlgebraCircuit.outputBits (nativeE F0 i).w1A ⟨j / 6, by change j / 6 < 4 * 256; omega⟩
        ⟨j % 6, by change j % 6 < 6; omega⟩ =
        constBit (K := F0.K) (w1Nat i.y (j / 8)) (j % 8) := by
      unfold NativeAlgebraCircuit.outputBits w1Nat
      rw [dif_pos (by omega)]
      change Falcon512.HashCircuit.wiresOfByteVec (K := F0.K)
        (fun p => (Native.honestW1Bytes i.y p).toNat) _ = _
      unfold Falcon512.HashCircuit.wiresOfByteVec
      simp only [show mldsa44.r1_bits * (j / 6) + j % 6 = j by
        change 6 * (j / 6) + j % 6 = j; omega]
    rw [hw]
    unfold constBit
    refine ⟨by rw [Native.ROMParams.toNatH_ite, toNatA_ite], ?_⟩
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < 256, j = 6144 + 2 * k ∨ j = 6144 + (2 * k + 1) :=
      ⟨(j - 6144) / 2, by omega, by omega⟩
    · rw [Native.ROMParams.xH_even i hr hk, y_hi E (by omega)]
      change _ = (interp 0).toNat (rdA E 61 (2 * k)) ∧ (rdA E 61 (2 * k) = 0 ∨ rdA E 61 (2 * k) = 1)
      rw [rdA_honest_fixed (i := i) (x := x) (c := c) (π := π) (by simp) (by rw [h61]; omega),
        aVal_61 _ i (by omega)]
      have hcA : (nativeE F0 i).cA ⟨2 * k / 2, by change 2 * k / 2 < 256; omega⟩
          ⟨2 * k % 2, by omega⟩ =
          (HashCircuit.ternaryBits (K := F0.K) (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).1 := by
        have e1 : 2 * k / 2 = k := by omega
        have e2 : 2 * k % 2 = 0 := by omega
        simp only [e1, e2]
        rfl
      rw [hcA, Native.ROMParams.tern1_H,
        show (HashCircuit.ternaryBits (K := F0.K) (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).1 =
          if i.y.c (Fin.cast cdeg ⟨k, hk⟩) = 0 then 0 else 1 from rfl]
      refine ⟨?_, ?_⟩
      · split_ifs
        · exact toNatE_zero.symm
        · exact toNatE_one.symm
      · split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl
    · rw [Native.ROMParams.xH_odd i hr hk, y_hi E (by omega)]
      change _ = (interp 0).toNat (rdA E 61 (2 * k + 1)) ∧
        (rdA E 61 (2 * k + 1) = 0 ∨ rdA E 61 (2 * k + 1) = 1)
      rw [rdA_honest_fixed (i := i) (x := x) (c := c) (π := π) (by simp) (by rw [h61]; omega),
        aVal_61 _ i (by omega)]
      have hcA : (nativeE F0 i).cA ⟨(2 * k + 1) / 2, by change (2 * k + 1) / 2 < 256; omega⟩
          ⟨(2 * k + 1) % 2, by omega⟩ =
          (HashCircuit.ternaryBits (K := F0.K) (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).2 := by
        have e1 : (2 * k + 1) / 2 = k := by omega
        have e2 : (2 * k + 1) % 2 = 1 := by omega
        simp only [e1, e2]
        rfl
      rw [hcA, Native.ROMParams.tern2_H,
        show (HashCircuit.ternaryBits (K := F0.K) (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).2 =
          if i.y.c (Fin.cast cdeg ⟨k, hk⟩) = -1 then 1 else 0 from rfl]
      refine ⟨?_, ?_⟩
      · split_ifs
        · exact toNatE_one.symm
        · exact toNatE_zero.symm
      · split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl

/-- **`mac.equal` holds** at the honest values. -/
theorem cross_holds (hx : x = hE.stmtOfKey i.y.key) :
    program.HoldsWith (program.reader E) (program.predicate 275).body := by
  rw [hb (program := program)]
  have hl : program.exprLen (.ref 527) = 6656 := (crossData (program := program)).1
  have h1 : program.domainField 1 = 1 := (crossData (program := program)).2.2.2.1
  have h0 : program.domainField 0 = 0 := (crossData (program := program)).2.2.2.2.1
  refine ⟨fun j hj => ?_, fun _ j hj => ?_⟩
  · rw [hl] at hj
    unfold RealizedProgram.evalWith
    rw [h0]
    rcases (cross_coords i hx hj).2 with h | h <;> rw [h]
    · rw [toNatE_zero]
      norm_num
    · rw [toNatE_one]
      norm_num
  · rw [hl] at hj
    unfold RealizedProgram.evalWith
    rw [h0, h1]
    exact (cross_coords i hx hj).1

/-- **Every source predicate other than the MAC's holds** at the source environment of the honest
values, at the key's statement (the realization's predicates `4`, `5`, `10` and `19` are no source
predicates, `MldsaEmulatedHonest.realPreds`). -/
theorem source_holds (hx : x = hE.stmtOfKey i.y.key) {q : ℕ} (hq : q < program.predicates.length)
    (hr : q ∉ macRolePreds) (hsrc : program.inSource (program.predicate q) = true) :
    program.HoldsWith (program.reader E) (program.predicate q).body := by
  have hreal : ∀ q ∈ [4, 5, 10, 19], program.inSource (program.predicate q) = true → False :=
    fun q hq h => by
      rw [MldsaEmulatedHonest.realPreds (program := program) q hq] at h
      cases h
  have hlen := predicates_length (program := program)
  rw [hlen] at hq
  simp only [macRolePreds, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h3, h16, h17, h18, h273⟩ := hr
  by_cases hh : 20 ≤ q ∧ q ≤ 272
  · exact hash_holds i hx hh.1 hh.2
  by_cases h275 : q = 275
  · subst h275
    exact cross_holds i hx
  by_cases h274 : q = 274
  · subst h274
    exact sig274_honest i hx
  have hA : q < 20 := by omega
  interval_cases q
  · exact w1bound_honest i
  · exact decompose_honest i
  · exact interval_honest i
  · exact absurd rfl h3
  · exact (hreal 4 (by decide) hsrc).elim
  · exact (hreal 5 (by decide) hsrc).elim
  · exact bools_honest i (by simp)
  · exact bools_honest i (by simp)
  · exact bools_honest i (by simp)
  · exact bools_honest i (by simp)
  · exact (hreal 10 (by decide) hsrc).elim
  · exact w_honest i
  · exact norm_honest i
  · exact offset_honest i
  · exact slack_honest i
  · exact weight_honest i
  · exact absurd rfl h16
  · exact absurd rfl h17
  · exact absurd rfl h18
  · exact (hreal 19 (by decide) hsrc).elim

/-- The integer reading of a bit of domain `A` that is not a constant is its indicator. -/
theorem intOf_bitA {v j : ℕ} (hc : program.isConstant v = false) (hf : program.valueField v = 0)
    (hb : rdA E v j = 0 ∨ rdA E v j = 1) :
    program.intOf (program.reader E) v j = if rdA E v j = 1 then 1 else 0 := by
  rcases hb with h | h
  · rw [intOf_of_natCast hc hf (k := 0) (by decide) (by rw [h]; simp), if_neg (by rw [h]; simp)]
    rfl
  · rw [intOf_of_natCast hc hf (k := 1) (by decide) (by rw [h]; simp), if_pos h]
    rfl

/-- **The MAC's source facts hold** at the honest values: `mac.equal`, its operands' bits and the A
operand's integer reading. -/
theorem srcMac_holds (hx : x = hE.stmtOfKey i.y.key) :
    hE.mac.Source (program.reader E) := by
  have hl : program.exprLen (.ref 527) = 6656 := (crossData (program := program)).1
  have hl6 := len6 (program := program)
  have h1 : program.domainField 1 = 1 := (crossData (program := program)).2.2.2.1
  have h0 : program.domainField 0 = 0 := (crossData (program := program)).2.2.2.2.1
  have h61 := size61 (program := program)
  have h64 := size64 (program := program)
  obtain ⟨hc64, hc61, hf64, hf61⟩ := cross_vals (program := program)
  obtain ⟨-, -, -, -, -, hf7, -, hc7, he7, -⟩ := crossData (program := program)
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
    rw [h1, x_eq E]
    exact Native.ROMParams.xH_bits i (readsCells_honest i x c π) hj
  · rw [hdy]
    intro j hj
    rw [hl6] at hj
    change program.evalE _ (program.domainField 0) _ j = 0 ∨ program.evalE _ (program.domainField 0) _ j = 1
    rw [h0]
    exact (cross_coords i hx hj).2
  · rw [hdy]
    intro j hj
    rw [hl6] at hj
    change program.evalIntWith _ 0 (.ref 6) j =
      if program.evalE _ (program.domainField 0) (.ref 6) j = 1 then 1 else 0
    rw [h0, RealizedProgram.evalIntWith_ref (refsOrdered (program := program)) _ _
        (crossData (program := program)).2.2.2.2.2.2.1, expr6,
      RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_reindex,
      RealizedProgram.evalIntWith_concat, RealizedProgram.evalIntWith_concat]
    by_cases hlo : j < 6144
    · rw [idx8_lo j hlo, idx9_lo j hlo, (crossData (program := program)).2.1,
        (crossData (program := program)).2.2.1, if_pos hlo,
        if_neg (lt_irrefl _), Nat.sub_self, RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf,
        intOf_constA _ hc7 hf7 (by rw [he7]; norm_num [pGold]), he7, y_lo E hlo]
      change _ = if rdA E 64 j = 1 then 1 else 0
      rw [intOf_bitA i hc64 hf64 (w1Bits_bool i (j / 6) (by omega) (j % 6) (by omega) |>.imp
        (fun h => by rwa [Nat.div_add_mod] at h) (fun h => by rwa [Nat.div_add_mod] at h))]
      simp
    · obtain ⟨k, hk, rfl⟩ : ∃ k < 512, j = 6144 + k := ⟨j - 6144, by omega, by omega⟩
      rw [idx8_hi k hk, idx9_hi k hk, (crossData (program := program)).2.1,
        (crossData (program := program)).2.2.1,
        if_neg (lt_irrefl _), Nat.sub_self, if_pos hk, RealizedProgram.evalIntWith_leaf,
        RealizedProgram.evalIntWith_leaf, intOf_constA _ hc7 hf7 (by rw [he7]; norm_num [pGold]), he7,
        y_hi E hk]
      change _ = if rdA E 61 k = 1 then 1 else 0
      rw [intOf_bitA i hc61 hf61 (h61_bool i k hk)]
      simp

end Src

end GordieHowe.MLDSA44.Emulated
