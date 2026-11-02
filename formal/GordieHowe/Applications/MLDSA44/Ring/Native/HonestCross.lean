-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.HonestMember
public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Cross
public import GordieHowe.Applications.MLDSA44.Native.HonestSource

@[expose] public section

/-!
# GordieHowe: the crossing of the native ML-DSA-44 ring programs at the honest values

The crossing `mac.equal` (predicate `248`; `lib/gordiehowe/examples/rings/mldsa_ring.h`,
`ring_crossing`, merged with domain `H`'s copies of `μ` and `w1` by the MAC lowering) at the
source environment of the honest values: domain `H`'s operand (the shared expression `513`:
`μ ‖ w1 ‖` the decoded support and sign alternately) and domain `A`'s (`50`:
`member.mu ‖ hint.w1 ‖ challenge.c`) read the same bits (`xH_*`, `yA_*`), so `mac.equal` holds
(`cross_holds`) and both operands read bits (`crossBits_honest`).
-/

namespace GordieHowe.MLDSA44.Ring.Native

open GordieHowe.Bits GordieHowe.Ring RealizedProgram
open MLDSA44.NativeAlgebraCircuit (outputBits)

set_option linter.unusedSectionVars false

variable {msgLen : ℕ}

set_option hygiene false in
local notation "nat" => MldsaRingEmbed.nat program

set_option hygiene false in
local notation "σ" => MldsaRingEmbed.σ program

variable {program : RealizedProgram} [MldsaRingEmbed program] [MldsaRingRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaRingFront program] [MldsaRingHonest program]
  {F0 FH : FieldInterp} [QField F0] [HField FH] [Native.MldsaAAlgebra nat] [hN : Native.MldsaNativeHonest nat F0 FH]
  [MldsaHHonest nat] [MldsaHShuffle nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]
  [MldsaHNativeData FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

variable (y : RingIn msgLen) (x : program.Valuation interp) (c : ∀ k, (program.layout interp).Ch k)
  (π : (program.layout interp).Pads)

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH y) c π

set_option hygiene false in
local notation "RD" => program.reader E

/-! ## Domain `H`'s operand -/

theorem xH_mu {t : ℕ} (ht : t < 512) :
    program.evalE RD 1 (.leaf (MldsaRingFront.muH program)) t = muBitsR (K := (interp 1).K) y t := by
  rw [← (MldsaRingFront.vals (program := program)).2.2.2.2.2.2,
    ← evalE_pull E (by decide : (120 : ℕ) ∈ ringV) t]
  exact evalE_mu_honest y (readsCells_pull y x c π) (valN_hash y) ht

theorem xH_w1 {t : ℕ} (ht : t < 6144) :
    program.evalE RD 1 (.leaf (MldsaRingFront.w1H program)) t = w1BitsR (K := (interp 1).K) y t := by
  rw [← (MldsaRingFront.vals (program := program)).2.2.2.2.2.1,
    ← evalE_pull E (by decide : (70 : ℕ) ∈ ringV) t]
  exact evalE_w1_honest y (readsCells_pull y x c π) (valN_hash y) ht

theorem chalPair_pull (k : Fin 256) :
    chalPair ((nat).reader (pull E)) k =
      HashCircuit.ternaryBits (K := (interp 1).K) (y.c (Fin.cast cdeg k)) :=
  chalPair_core y (readsCells_pull y x c π) (valN_mem y) k

theorem xH_sup {k : ℕ} (hk : k < 256) :
    program.evalE RD 1 (.ref ((σ).ref 523)) k =
      (HashCircuit.ternaryBits (K := (interp 1).K) (y.c ⟨k, hk⟩)).1 := by
  rw [← evalE_ref_pull E (by decide : (523 : ℕ) ∈ ringR) k]
  exact congrArg Prod.fst (chalPair_pull y x c π ⟨k, hk⟩)

theorem xH_sgn {k : ℕ} (hk : k < 256) :
    program.evalE RD 1 (.ref ((σ).ref 524)) k =
      (HashCircuit.ternaryBits (K := (interp 1).K) (y.c ⟨k, hk⟩)).2 := by
  rw [← evalE_ref_pull E (by decide : (524 : ℕ) ∈ ringR) k,
    evalE_ref MldsaHCross.refsOrdered _ _ MldsaHCross.lt524, MldsaHCross.expr524]
  exact congrArg Prod.snd (chalPair_pull y x c π ⟨k, hk⟩)

/-! ## Domain `A`'s operand -/

theorem yA_mu {t : ℕ} (ht : t < 512) :
    program.evalE RD 0 (.leaf (MldsaRingFront.muA program)) t = ((muBitNat y.mu t : ℕ) : (interp 0).K) :=
  evalE_mu y x c π ht

theorem yA_w1 {t : ℕ} (ht : t < 6144) :
    program.evalE RD 0 (.leaf (MldsaRingFront.w1A program)) t = constBit (w1NatR y (t / 8)) (t % 8) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hs62, -⟩ := Native.MldsaNativeHonest.a_bound (program := nat)
  rw [← (MldsaRingFront.vals (program := program)).2.2.2.2.1,
    evalE_held y x c π (by decide) (by rw [hs62]; exact ht), aValR_62 y _ ht]
  unfold outputBits w1A w1NatR Falcon512.HashCircuit.wiresOfByteVec
  rw [dif_pos (by omega)]
  simp only [show mldsa44.r1_bits * (t / 6) + t % 6 = t by change 6 * (t / 6) + t % 6 = t; omega]

theorem yA_c {k : ℕ} (hk : k < 256) (s : Fin 2) :
    program.evalE RD 0 (.leaf (MldsaRingRelation.c program)) (2 * k + s) =
      cA y (interp 0).K ⟨k, hk⟩ s := by
  obtain ⟨-, -, -, -, -, -, -, -, hs59, -⟩ := Native.MldsaNativeHonest.a_bound (program := nat)
  have hs2 := s.isLt
  rw [← (MldsaRingFront.vals (program := program)).2.2.1,
    evalE_held y x c π (by decide) (by rw [hs59]; omega), aValR_59 y _ (by omega)]
  congr 1
  · exact Fin.ext (by simp only; omega)
  · exact Fin.ext (by simp only; omega)

/-! ## The readings as naturals -/

theorem toNatH_constBit (n b : ℕ) : (interp 1).toNat (constBit (K := (interp 1).K) n b) = n / 2 ^ b % 2 := by
  unfold constBit
  rw [MLDSA44.toNatH_ite]
  split_ifs with h <;> omega

theorem toNatA_constBit (n b : ℕ) : (interp 0).toNat (constBit (K := (interp 0).K) n b) = n / 2 ^ b % 2 := by
  unfold constBit
  rw [MLDSA44.Native.toNatA_ite]
  split_ifs with h <;> omega

theorem toNatA_bit (n b : ℕ) : (interp 0).toNat (((n / 2 ^ b % 2 : ℕ) : ℕ) : (interp 0).K) = n / 2 ^ b % 2 :=
  QField.toNat_natCast ((Nat.mod_lt _ (by norm_num)).trans (by norm_num))

/-- **`mac.equal` holds** at the honest values. -/
theorem cross_holds : program.HoldsAt E (program.predicate 248).body := by
  obtain ⟨-, -, cc, hc⟩ := MldsaRingFront.cross (program := program)
  rw [HoldsAt, hc]
  change (∀ i < program.exprLen (.ref 513),
      (interp (program.domainField 0)).toNat (program.evalE RD (program.domainField 0) (.ref 50) i) < 2 ^ 1) ∧
    ((∀ i < program.exprLen (.ref 513),
      (interp (program.domainField 1)).toNat (program.evalE RD (program.domainField 1) (.ref 513) i) < 2 ^ 1) →
      ∀ i < program.exprLen (.ref 513),
        (interp (program.domainField 1)).toNat (program.evalE RD (program.domainField 1) (.ref 513) i) =
        (interp (program.domainField 0)).toNat (program.evalE RD (program.domainField 0) (.ref 50) i))
  rw [MldsaRingFront.domains.2, MldsaRingFront.domains.1, MldsaRingFront.lens.1]
  -- the coordinates as naturals
  have key : ∀ i < 7168, (interp 1).toNat (program.evalE RD 1 (.ref 513) i) =
      (interp 0).toNat (program.evalE RD 0 (.ref 50) i) ∧
      (interp 0).toNat (program.evalE RD 0 (.ref 50) i) < 2 := by
    intro i hi
    by_cases h1 : i < 512
    · rw [x_mu RD h1, y_mu RD h1, xH_mu y x c π h1, yA_mu y x c π h1]
      unfold muBitsR muBitNat
      rw [dif_pos h1, dif_pos h1, toNatH_constBit, toNatA_bit]
      exact ⟨rfl, Nat.mod_lt _ (by norm_num)⟩
    by_cases h2 : i < 6656
    · obtain ⟨t, ht, rfl⟩ : ∃ t < 6144, i = 512 + t := ⟨i - 512, by omega, by omega⟩
      rw [x_w1 RD ht, y_w1 RD ht, xH_w1 y x c π ht, yA_w1 y x c π ht]
      unfold w1BitsR
      rw [toNatH_constBit, toNatA_constBit]
      exact ⟨rfl, Nat.mod_lt _ (by norm_num)⟩
    · obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < 256, i = 6656 + 2 * k ∨ i = 6656 + (2 * k + 1) :=
        ⟨(i - 6656) / 2, by omega, by omega⟩
      · rw [x_sup RD hk, y_c RD (by omega), xH_sup y x c π hk,
          show 2 * k = 2 * k + ((0 : Fin 2) : ℕ) by simp, yA_c y x c π hk 0]
        unfold cA
        simp only [Matrix.cons_val_zero]
        rw [MLDSA44.tern1_H, MLDSA44.Native.tern1_A]
        refine ⟨rfl, ?_⟩
        split_ifs <;> norm_num
      · rw [x_sgn RD hk, y_c RD (by omega), xH_sgn y x c π hk,
          show 2 * k + 1 = 2 * k + ((1 : Fin 2) : ℕ) by simp, yA_c y x c π hk 1]
        unfold cA
        simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
        rw [MLDSA44.tern2_H, MLDSA44.Native.tern2_A]
        refine ⟨rfl, ?_⟩
        split_ifs <;> norm_num
  exact ⟨fun i hi => by simpa using (key i hi).2, fun _ i hi => (key i hi).1⟩

/-- **The crossing's operands read bits** at the honest values. -/
theorem crossBits_honest :
    (∀ i < 7168, program.evalE RD 1 (.ref 513) i = 0 ∨ program.evalE RD 1 (.ref 513) i = 1) ∧
      ∀ i < 7168, program.evalE RD 0 (.ref 50) i = 0 ∨ program.evalE RD 0 (.ref 50) i = 1 := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · by_cases h1 : i < 512
    · rw [x_mu RD h1, xH_mu y x c π h1]
      unfold muBitsR
      rw [dif_pos h1]
      exact constBit_bool _ _
    by_cases h2 : i < 6656
    · obtain ⟨t, ht, rfl⟩ : ∃ t < 6144, i = 512 + t := ⟨i - 512, by omega, by omega⟩
      rw [x_w1 RD ht, xH_w1 y x c π ht]
      exact constBit_bool _ _
    · obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < 256, i = 6656 + 2 * k ∨ i = 6656 + (2 * k + 1) :=
        ⟨(i - 6656) / 2, by omega, by omega⟩
      · rw [x_sup RD hk, xH_sup y x c π hk]
        exact (MLDSA44.Native.ternaryBits_bool _).1
      · rw [x_sgn RD hk, xH_sgn y x c π hk]
        exact (MLDSA44.Native.ternaryBits_bool _).2
  · by_cases h1 : i < 512
    · rw [y_mu RD h1, yA_mu y x c π h1]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (muBitNat_le y.mu i) with h | h <;> rw [h] <;> simp
    by_cases h2 : i < 6656
    · obtain ⟨t, ht, rfl⟩ : ∃ t < 6144, i = 512 + t := ⟨i - 512, by omega, by omega⟩
      rw [y_w1 RD ht, yA_w1 y x c π ht]
      exact constBit_bool _ _
    · obtain ⟨j, hj, rfl⟩ : ∃ j < 512, i = 6656 + j := ⟨i - 6656, by omega, by omega⟩
      rw [y_c RD hj, show j = 2 * (j / 2) + ((⟨j % 2, by omega⟩ : Fin 2) : ℕ) by simp; omega,
        yA_c y x c π (by omega)]
      unfold cA
      rcases Nat.mod_two_eq_zero_or_one j with h | h
      · simp only [h, Fin.zero_eta, Matrix.cons_val_zero]
        exact (MLDSA44.Native.ternaryBits_bool _).1
      · simp only [h, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
        exact (MLDSA44.Native.ternaryBits_bool _).2

end GordieHowe.MLDSA44.Ring.Native
