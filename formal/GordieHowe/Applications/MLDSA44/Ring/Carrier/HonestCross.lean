-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Carrier.HonestRelation
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Cross
public import GordieHowe.Applications.MLDSA44.Ring.Native.HonestCross

@[expose] public section

/-!
# GordieHowe: the crossing of the ML-DSA-44 ring carriers at the honest values

The crossing `mac.equal` (predicate `247`; `lib/gordiehowe/examples/rings/mldsa_ring.h`,
`ring_crossing`, merged with domain `H`'s copies of `μ` and `w1` by the MAC lowering) at the
source environment of the honest values: domain `H`'s operand (the shared expression `505`:
`μ ‖ w1 ‖` the decoded support and sign alternately, read through domain `H`'s renaming at the
core's honest values) and domain `A`'s (`42`: `member.mu ‖ hint.w1 ‖ challenge.c`) read the same
bits (`xH_*`, `yA_*`), so `mac.equal` holds (`cross_holds`) and both operands read bits
(`crossBits_honest`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

open GordieHowe.Bits GordieHowe.Ring RealizedProgram
open MLDSA44.NativeAlgebraCircuit (outputBits)
open GordieHowe.MLDSA44.Ring.Native (MldsaRingStmt muBitNat muBitNat_le muBitsR w1BitsR w1NatR w1A cA
  evalE_mu_honest evalE_w1_honest chalPair_core)
open MLDSA44.Emulated (MldsaEAlgebra MldsaEmulatedHonest)

set_option linter.unusedSectionVars false

variable {msgLen : ℕ}

variable {program : RealizedProgram} [CarrierHEmbed program] [CarrierAEmbed program]
  [MldsaEAlgebra (CarrierAEmbed.emu program)] [MldsaCarrierHonest program]
  [MldsaCarrierRelation program] [MldsaRingStmt program] [TableSelect program]
  [MldsaCarrierFront program] [MldsaCarrierSelect program] [MldsaCarrierQuot program]
  {F0 FH : FieldInterp} [MLDSA44.AField F0] [HField FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => CarrierHEmbed.nat program

set_option hygiene false in
local notation "emu" => CarrierAEmbed.emu program

variable [MldsaHHonest nat] [MldsaHShuffle nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]
  [MLDSA44.MldsaHNativeData FH]
  [MLDSA44.MldsaHSample (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MLDSA44.MldsaHConsts (MLDSA44.Emulated.MldsaEmbed.nat emu) FH]
  [MldsaHHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MldsaHSelHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)] [MLDSA44.MldsaHNodes FH]
  [hE : MldsaEmulatedHonest emu F0 FH]

variable (y : RingIn msgLen) (x : program.Valuation interp) (c : ∀ k, (program.layout interp).Ch k)
  (π : (program.layout interp).Pads)

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH y) c π

set_option hygiene false in
local notation "RD" => program.reader E

/-! ## Domain `H`'s operand -/

theorem xH_mu {t : ℕ} (ht : t < 512) :
    program.evalE RD 1 (.leaf 71) t = muBitsR (K := (interp 1).K) y t := by
  rw [← σH_val120, ← evalE_pullH E (by decide : (120 : ℕ) ∈ hV) t]
  exact evalE_mu_honest y (readsCells_pullH y x c π) (valH_hash y) ht

theorem xH_w1 {t : ℕ} (ht : t < 6144) :
    program.evalE RD 1 (.leaf 73) t = w1BitsR (K := (interp 1).K) y t := by
  rw [← σH_val70, ← evalE_pullH E (by decide : (70 : ℕ) ∈ hV) t]
  exact evalE_w1_honest y (readsCells_pullH y x c π) (valH_hash y) ht

theorem chalPair_pullH (k : Fin 256) :
    chalPair ((nat).reader (pullH E)) k =
      HashCircuit.ternaryBits (K := (interp 1).K) (y.c (Fin.cast cdeg k)) :=
  chalPair_core y (readsCells_pullH y x c π) (valH_mem y) k

theorem xH_sup {k : ℕ} (hk : k < 256) :
    program.evalE RD 1 (.ref 503) k =
      (HashCircuit.ternaryBits (K := (interp 1).K) (y.c ⟨k, hk⟩)).1 := by
  rw [← σH_ref523, ← evalE_ref_pullH E (by decide : (523 : ℕ) ∈ hR) k]
  exact congrArg Prod.fst (chalPair_pullH y x c π ⟨k, hk⟩)

theorem xH_sgn {k : ℕ} (hk : k < 256) :
    program.evalE RD 1 (.ref 504) k =
      (HashCircuit.ternaryBits (K := (interp 1).K) (y.c ⟨k, hk⟩)).2 := by
  rw [RealizedProgram.evalE_ref MldsaCarrierRelation.refsOrdered _ _
      (by have := MldsaCarrierFront.lt505 (program := program); omega), MldsaCarrierFront.expr504,
    ← σH_ref522, ← evalE_ref_pullH E (by decide : (522 : ℕ) ∈ hR) k]
  exact congrArg Prod.snd (chalPair_pullH y x c π ⟨k, hk⟩)

/-! ## Domain `A`'s operand -/

theorem yA_w1 {t : ℕ} (ht : t < 6144) :
    program.evalE RD 0 (.leaf 66) t = constBit (w1NatR y (t / 8)) (t % 8) := by
  have h := evalE_pullA E (f := 0) (v := 63) (by decide) t
  rw [σA_vals.2.2.2.2] at h
  rw [← h]
  refine (rdAE_fixed (readsAE_pullA y x c π) (v := 63) (by simp)
    (by rw [MldsaEmulatedHonest.size64 (program := emu)]; exact ht)).trans ?_
  rw [aValE_63 y _ _ ht]
  unfold outputBits w1A w1NatR Falcon512.HashCircuit.wiresOfByteVec
  rw [dif_pos (by omega)]
  simp only [show mldsa44.r1_bits * (t / 6) + t % 6 = t by change 6 * (t / 6) + t % 6 = t; omega]

/-! ## The readings as naturals -/

theorem toNat1_constBit (n b : ℕ) :
    (interp 1).toNat (constBit (K := (interp 1).K) n b) = n / 2 ^ b % 2 := by
  unfold constBit
  rw [MLDSA44.toNatH_ite]
  split_ifs with h <;> omega

theorem toNat0_constBit (n b : ℕ) :
    (interp 0).toNat (constBit (K := (interp 0).K) n b) = n / 2 ^ b % 2 := by
  unfold constBit
  rw [toNat0_ite]
  split_ifs with h <;> omega

theorem toNat0_bit (n b : ℕ) :
    (interp 0).toNat (((n / 2 ^ b % 2 : ℕ) : ℕ) : (interp 0).K) = n / 2 ^ b % 2 :=
  toNat_lt0 ((Nat.mod_lt _ (by norm_num)).trans (by norm_num [pGold]))

theorem tern1_A0 (z : ℤ) : (interp 0).toNat (HashCircuit.ternaryBits (K := (interp 0).K) z).1 =
    if z = 0 then 0 else 1 := by
  rw [show (HashCircuit.ternaryBits (K := (interp 0).K) z).1 = if z = 0 then 0 else 1 from rfl]
  split_ifs
  · simpa using toNat_lt0 (I := interp) (k := 0) (by norm_num [pGold])
  · simpa using toNat_lt0 (I := interp) (k := 1) (by norm_num [pGold])

theorem tern2_A0 (z : ℤ) : (interp 0).toNat (HashCircuit.ternaryBits (K := (interp 0).K) z).2 =
    if z = -1 then 1 else 0 := by
  rw [show (HashCircuit.ternaryBits (K := (interp 0).K) z).2 = if z = -1 then 1 else 0 from rfl]
  split_ifs
  · simpa using toNat_lt0 (I := interp) (k := 1) (by norm_num [pGold])
  · simpa using toNat_lt0 (I := interp) (k := 0) (by norm_num [pGold])

/-- **The challenge bits at a coefficient**: the support and the sign of the challenge. -/
theorem yA_c {k : ℕ} (hk : k < 256) (s : Fin 2) :
    program.evalE RD 0 (.leaf 62) (2 * k + s) = cA y (interp 0).K ⟨k, hk⟩ s := by
  have hs2 := s.isLt
  rw [rd_c y x c π (by omega)]
  congr 1
  · exact Fin.ext (by simp only; omega)
  · exact Fin.ext (by simp only; omega)

/-- **`mac.equal` holds** at the honest values. -/
theorem cross_holds : program.HoldsAt E (program.predicate 247).body := by
  obtain ⟨-, -, cc, hc⟩ := MldsaCarrierFront.cross (program := program)
  rw [HoldsAt, hc]
  change (∀ i < program.exprLen (.ref 505),
      (interp (program.domainField 0)).toNat (program.evalE RD (program.domainField 0) (.ref 42) i) <
        2 ^ 1) ∧
    ((∀ i < program.exprLen (.ref 505),
      (interp (program.domainField 1)).toNat (program.evalE RD (program.domainField 1) (.ref 505) i) <
        2 ^ 1) →
      ∀ i < program.exprLen (.ref 505),
        (interp (program.domainField 1)).toNat (program.evalE RD (program.domainField 1) (.ref 505) i) =
        (interp (program.domainField 0)).toNat (program.evalE RD (program.domainField 0) (.ref 42) i))
  rw [MldsaCarrierFront.domains.2, MldsaCarrierFront.domains.1, MldsaCarrierFront.lens.1]
  have key : ∀ i < 7168, (interp 1).toNat (program.evalE RD 1 (.ref 505) i) =
      (interp 0).toNat (program.evalE RD 0 (.ref 42) i) ∧
      (interp 0).toNat (program.evalE RD 0 (.ref 42) i) < 2 := by
    intro i hi
    by_cases h1 : i < 512
    · rw [x_mu RD h1, y_mu RD h1, xH_mu y x c π h1, evalE_mu y x c π h1]
      unfold muBitsR muBitNat
      rw [dif_pos h1, dif_pos h1, toNat1_constBit, toNat0_bit]
      exact ⟨rfl, Nat.mod_lt _ (by norm_num)⟩
    by_cases h2 : i < 6656
    · obtain ⟨t, ht, rfl⟩ : ∃ t < 6144, i = 512 + t := ⟨i - 512, by omega, by omega⟩
      rw [x_w1 RD ht, y_w1 RD ht, xH_w1 y x c π ht, yA_w1 y x c π ht]
      unfold w1BitsR
      rw [toNat1_constBit, toNat0_constBit]
      exact ⟨rfl, Nat.mod_lt _ (by norm_num)⟩
    · obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < 256, i = 6656 + 2 * k ∨ i = 6656 + (2 * k + 1) :=
        ⟨(i - 6656) / 2, by omega, by omega⟩
      · rw [x_sup RD hk, y_c RD (by omega), xH_sup y x c π hk,
          show 2 * k = 2 * k + ((0 : Fin 2) : ℕ) by simp, yA_c y x c π hk 0]
        unfold cA
        simp only [Matrix.cons_val_zero]
        rw [MLDSA44.tern1_H, tern1_A0]
        refine ⟨rfl, ?_⟩
        split_ifs <;> norm_num
      · rw [x_sgn RD hk, y_c RD (by omega), xH_sgn y x c π hk,
          show 2 * k + 1 = 2 * k + ((1 : Fin 2) : ℕ) by simp, yA_c y x c π hk 1]
        unfold cA
        simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
        rw [MLDSA44.tern2_H, tern2_A0]
        refine ⟨rfl, ?_⟩
        split_ifs <;> norm_num
  exact ⟨fun i hi => by simpa using (key i hi).2, fun _ i hi => (key i hi).1⟩

/-- **The crossing's operands read bits** at the honest values. -/
theorem crossBits_honest :
    (∀ i < 7168, program.evalE RD 1 (.ref 505) i = 0 ∨ program.evalE RD 1 (.ref 505) i = 1) ∧
      ∀ i < 7168, program.evalE RD 0 (.ref 42) i = 0 ∨ program.evalE RD 0 (.ref 42) i = 1 := by
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
    · rw [y_mu RD h1, evalE_mu y x c π h1]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (muBitNat_le y.mu i) with h | h <;> rw [h] <;> simp
    by_cases h2 : i < 6656
    · obtain ⟨t, ht, rfl⟩ : ∃ t < 6144, i = 512 + t := ⟨i - 512, by omega, by omega⟩
      rw [y_w1 RD ht, yA_w1 y x c π ht]
      exact constBit_bool _ _
    · obtain ⟨j, hj, rfl⟩ : ∃ j < 512, i = 6656 + j := ⟨i - 6656, by omega, by omega⟩
      rw [y_c RD hj]
      exact rd_c_bool y x c π hj

end GordieHowe.MLDSA44.Ring.Carrier
