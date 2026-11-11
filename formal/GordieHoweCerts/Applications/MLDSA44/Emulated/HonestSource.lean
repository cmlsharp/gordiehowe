-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Emulated.HonestValues

@[expose] public section

/-!
# GordieHowe: the source predicates of an emulated ML-DSA program at its honest values

At the source environment of the honest values (`honestVal`) on an honest input at its key's
statement, every predicate of an emulated ML-DSA program other than the MAC's holds
(`source_holds`, by `MldsaEmulatedHonest.coverage`): domain `H`'s predicates are the native
program's `hPredLo … hPredHi`, paired by the embedding data (`MldsaEmbed.held`) and renamed, which
hold in the environment read as the native program's
(`GordieHowe.MLDSA44.hPreds_holds`, `GordieHowe.RealizedProgram.holdsAt_pullEnv`); domain `A`'s
(`GordieHoweCerts/Applications/MLDSA44/Emulated/HonestValues.lean`); the blind's Booleanity and the crossing `mac.equal` (here). This
file also proves that the crossing's operands read bits (`cross_bits`).
-/

namespace GordieHowe.MLDSA44.Emulated

open GordieHowe.Bits RealizedProgram
open MLDSA44 (HonestInput)


set_option linter.unusedSectionVars false

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => MldsaEmbed.nat program

set_option hygiene false in
local notation "σ" => MldsaEmbed.σ program

set_option hygiene false in
local notation "hV" => MldsaEmbed.V program

variable {program : RealizedProgram} [MldsaEAlgebra program] {F0 FH : FieldInterp} [RealizedProgram.PrimeCastField F0 pGold]
  [HField FH] [MldsaHHonest nat] [MldsaHSample nat] [MldsaHSelHonest nat]
  [MldsaHConsts nat FH] [MLDSA44.MldsaHNativeData FH] [MldsaHNodes FH]
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
    (castElt (b := 1) ((pull E).stmt 66 j) : (interp 1).K) = (honestData (K := FH.K) i.y).tr j := by
  intro j hj
  have h67 : (66 : ℕ) ∈ hV := MldsaEmbed.readV
  have hst : (pull E).stmt 66 j = castElt (x 67 j) := by
    change (if (66 : ℕ) ∈ hV then castElt (x ((σ).val 66) j) else 0) = _
    rw [if_pos h67, MldsaEMain.trLink]
  obtain ⟨hn, hf⟩ := MldsaEMain.trFields (program := program)
  rw [hst, castElt_castElt_eq, if_pos (hf.trans hn.symm), hx, stmt68 (program := program) i.y.key j hj]
  change _ = constBit (trNat i.y (j / 8)) (j % 8)
  unfold trNat
  rw [dif_pos (by omega)]

/-- **Domain `H`'s predicates hold** at the honest values: the native program's, renamed. -/
theorem hash_holds (hx : x = hE.stmtOfKey i.y.key) {k : ℕ} (h1 : hPredLo ≤ k) (h2 : k ≤ hPredHi) :
    program.HoldsWith (program.reader E) (program.predicate (MldsaEmbed.pred program k)).body := by
  obtain ⟨hc, -, -⟩ := MldsaEmbed.predCorr (program := program) k h1 h2
  exact (RealizedProgram.holdsAt_pullEnv MldsaEmbed.embedding E hc).2
    (MLDSA44.hPreds_holds i (readsCells_honest i x c π) (htr_pull i hx) h1 h2)

/-! ## The crossing `mac.equal` -/

omit [MldsaHHonest nat] [MldsaHSample nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]
  [MLDSA44.MldsaHNativeData FH] [MldsaHNodes FH] hE in
/-- The integer reading of a bit constant in domain `A`'s field. -/
theorem toNatA_ite (p : Prop) [Decidable p] :
    (interp 0).toNat (if p then (1 : (interp 0).K) else 0) = if p then 1 else 0 := by
  split_ifs
  · exact toNatE_one
  · exact toNatE_zero

/-- **The crossing's coordinates agree** at the honest values: H's `w1` bits and decoded challenge
bits are A's `hint.w1` and challenge bits, read as naturals; A's are bits. -/
theorem cross_coords (hx : x = hE.stmtOfKey i.y.key) {j : ℕ} (hj : j < 6656) :
    (interp 1).toNat (program.evalE (program.reader E) 1 (.ref ((σ).ref 525)) j) =
        (interp 0).toNat (program.evalE (program.reader E) 0 (.ref 6) j) ∧
      (program.evalE (program.reader E) 0 (.ref 6) j = 0 ∨
        program.evalE (program.reader E) 0 (.ref 6) j = 1) := by
  have h61 := size61 (program := program)
  have h64 := size64 (program := program)
  have hr := readsCells_honest i x c π
  rw [x_eq E]
  by_cases hlo : j < 6144
  · rw [MLDSA44.xH_lo i hr (htr_pull i hx) hlo, y_lo E hlo]
    change _ = (interp 0).toNat (rdA E 63 j) ∧ (rdA E 63 j = 0 ∨ rdA E 63 j = 1)
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
    refine ⟨by rw [MLDSA44.toNatH_ite, toNatA_ite], ?_⟩
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < 256, j = 6144 + 2 * k ∨ j = 6144 + (2 * k + 1) :=
      ⟨(j - 6144) / 2, by omega, by omega⟩
    · rw [MLDSA44.xH_even i hr hk, y_hi E (by omega)]
      change _ = (interp 0).toNat (rdA E 60 (2 * k)) ∧ (rdA E 60 (2 * k) = 0 ∨ rdA E 60 (2 * k) = 1)
      rw [rdA_honest_fixed (i := i) (x := x) (c := c) (π := π) (by simp) (by rw [h61]; omega),
        aVal_61 _ i (by omega)]
      have hcA : (nativeE F0 i).cA ⟨2 * k / 2, by change 2 * k / 2 < 256; omega⟩
          ⟨2 * k % 2, by omega⟩ =
          (HashCircuit.ternaryBits (K := F0.K) (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).1 := by
        have e1 : 2 * k / 2 = k := by omega
        have e2 : 2 * k % 2 = 0 := by omega
        simp only [e1, e2]
        rfl
      rw [hcA, MLDSA44.tern1_H,
        show (HashCircuit.ternaryBits (K := F0.K) (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).1 =
          if i.y.c (Fin.cast cdeg ⟨k, hk⟩) = 0 then 0 else 1 from rfl]
      refine ⟨?_, ?_⟩
      · split_ifs
        · exact toNatE_zero.symm
        · exact toNatE_one.symm
      · split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl
    · rw [MLDSA44.xH_odd i hr hk, y_hi E (by omega)]
      change _ = (interp 0).toNat (rdA E 60 (2 * k + 1)) ∧
        (rdA E 60 (2 * k + 1) = 0 ∨ rdA E 60 (2 * k + 1) = 1)
      rw [rdA_honest_fixed (i := i) (x := x) (c := c) (π := π) (by simp) (by rw [h61]; omega),
        aVal_61 _ i (by omega)]
      have hcA : (nativeE F0 i).cA ⟨(2 * k + 1) / 2, by change (2 * k + 1) / 2 < 256; omega⟩
          ⟨(2 * k + 1) % 2, by omega⟩ =
          (HashCircuit.ternaryBits (K := F0.K) (i.y.c (Fin.cast cdeg ⟨k, hk⟩))).2 := by
        have e1 : (2 * k + 1) / 2 = k := by omega
        have e2 : (2 * k + 1) % 2 = 1 := by omega
        simp only [e1, e2]
        rfl
      rw [hcA, MLDSA44.tern2_H,
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
    program.HoldsWith (program.reader E) (program.predicate (MldsaECross.crossPred program)).body := by
  rw [hb (program := program)]
  have hl : program.exprLen (.ref ((σ).ref 525)) = 6656 := (crossData (program := program)).1
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

/-- **Every source predicate holds** at the source environment of the honest values, at the key's
statement (the realization's and the MAC's role predicates are no source predicates,
`MldsaEmulatedHonest.realPreds`). -/
theorem source_holds (hx : x = hE.stmtOfKey i.y.key) {q : ℕ} (hq : q < program.predicates.length)
    (hsrc : program.inSource (program.predicate q) = true) :
    program.HoldsWith (program.reader E) (program.predicate q).body := by
  rcases MldsaEmulatedHonest.coverage (program := program) q hq with ⟨p, hp, rfl, hk⟩ | ho | rfl | hr
  · rw [← MldsaEmbed.pred_held p hp]
    exact hash_holds i hx hk.1 hk.2
  · simp only [algebraPreds, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact w1bound_honest i
    · exact decompose_honest i
    · exact interval_honest i
    · exact bools_honest i (by simp)
    · exact bools_honest i (by simp)
    · exact bools_honest i (by simp)
    · exact bools_honest i (by simp)
    · exact w_honest i
    · exact norm_honest i
    · exact offset_honest i
    · exact slack_honest i
    · exact weight_honest i
    · exact sig274_honest i hx
  · exact cross_holds i hx
  · rw [MldsaEmulatedHonest.realPreds q hr] at hsrc
    cases hsrc

/-- **The crossing's operands read bits** at the honest values: the native operand `525`, renamed, in domain `H` and
`ref 6` in domain `A`. -/
theorem cross_bits (hx : x = hE.stmtOfKey i.y.key) :
    (∀ j < program.exprLen (.ref ((σ).ref 525)),
      program.evalWith (program.reader E) 1 (.ref ((σ).ref 525)) j = 0 ∨
        program.evalWith (program.reader E) 1 (.ref ((σ).ref 525)) j = 1) ∧
    ∀ j < program.exprLen (.ref 6),
      program.evalWith (program.reader E) 0 (.ref 6) j = 0 ∨
        program.evalWith (program.reader E) 0 (.ref 6) j = 1 := by
  have hl : program.exprLen (.ref ((σ).ref 525)) = 6656 := (crossData (program := program)).1
  have hl6 := len6 (program := program)
  have h1 : program.domainField 1 = 1 := (crossData (program := program)).2.2.2.1
  have h0 : program.domainField 0 = 0 := (crossData (program := program)).2.2.2.2.1
  constructor
  · intro j hj
    rw [hl] at hj
    change program.evalE _ (program.domainField 1) _ j = 0 ∨ program.evalE _ (program.domainField 1) _ j = 1
    rw [h1, x_eq E]
    exact MLDSA44.xH_bits i (readsCells_honest i x c π) hj
  · intro j hj
    rw [hl6] at hj
    change program.evalE _ (program.domainField 0) _ j = 0 ∨ program.evalE _ (program.domainField 0) _ j = 1
    rw [h0]
    exact (cross_coords i hx hj).2

end Src

end GordieHowe.MLDSA44.Emulated
