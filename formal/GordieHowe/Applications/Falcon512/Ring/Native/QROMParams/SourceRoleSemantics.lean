-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Native.SourceRoles
public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.Facts
public import GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.SourceRoleFacts

public section

/-!
# Native ring witness meanings for checked source roles

Checked role placement and coverage select source coordinates. The lemmas below identify each
role's witness value with the existing honest-value specification.
-/

namespace GordieHowe.Falcon512.Ring.Native.QROMParams
open RealizedProgram _root_.GordieHowe.Falcon512.Ring
open Generated.Falcon512.Ring.Native.QROMParams.Program (program)
open Generated.Falcon512.Ring.Native.QROMParams (interp)
open Generated.Falcon512.Ring.Native.QROMParams.SourceRoleFacts
open Generated.Falcon512.Ring.Native.QROMParams.ShapeFacts
local notation "classifier" => Generated.Falcon512.Ring.Native.QROMParams.SourceRoles.classifier

variable {msgLen : Nat} {G : Native.Signer msgLen}
private theorem role_6 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1, y.normIn.nA, y.normIn.nSq, y.normIn.nCc, y.normIn.nNd, y.normIn.nNc, y.normIn.nD, y.normIn.nDc⟩ : Native.SourceValues (interp 0).K).valuation (program := program) classifier 6 j =
      program.execOf interp (honestVal program interp y) 6 j := by
  rw [Native.SourceValues.valuation_of_lookup _ role_key_2espectrum_lookup]
  rw [RealizedProgram.execOf_of_priv _ value_key_2espectrum_kind]
  exact (honestVal_spec y j).symm
private theorem role_7 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1, y.normIn.nA, y.normIn.nSq, y.normIn.nCc, y.normIn.nNd, y.normIn.nNc, y.normIn.nD, y.normIn.nDc⟩ : Native.SourceValues (interp 0).K).valuation (program := program) classifier 7 j =
      program.execOf interp (honestVal program interp y) 7 j := by
  rw [Native.SourceValues.valuation_of_lookup _ role_member_2esigner_2eindex_lookup]
  rw [RealizedProgram.execOf_of_priv _ value_member_2esigner_2eindex_kind]
  exact (honestVal_bit y j).symm
private theorem role_9 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1, y.normIn.nA, y.normIn.nSq, y.normIn.nCc, y.normIn.nNd, y.normIn.nNc, y.normIn.nD, y.normIn.nDc⟩ : Native.SourceValues (interp 0).K).valuation (program := program) classifier 9 j =
      program.execOf interp (honestVal program interp y) 9 j := by
  rw [Native.SourceValues.valuation_of_lookup _ role_s2_lookup]
  rw [RealizedProgram.execOf_of_priv _ value_s2_kind]
  exact (honestVal_nat (program := program) (I := interp) y (v := 9) (r := .s2) (by change (9, NatRole.s2) ∈ nativeRoles program; decide) j).symm
private theorem role_10 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1, y.normIn.nA, y.normIn.nSq, y.normIn.nCc, y.normIn.nNd, y.normIn.nNc, y.normIn.nD, y.normIn.nDc⟩ : Native.SourceValues (interp 0).K).valuation (program := program) classifier 10 j =
      program.execOf interp (honestVal program interp y) 10 j := by
  rw [Native.SourceValues.valuation_of_lookup _ role_signature_2es1_lookup]
  rw [RealizedProgram.execOf_of_priv _ value_signature_2es1_kind]
  exact (honestVal_nat (program := program) (I := interp) y (v := 10) (r := .s1) (by change (10, NatRole.s1) ∈ nativeRoles program; decide) j).symm
private theorem role_11 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1, y.normIn.nA, y.normIn.nSq, y.normIn.nCc, y.normIn.nNd, y.normIn.nNc, y.normIn.nD, y.normIn.nDc⟩ : Native.SourceValues (interp 0).K).valuation (program := program) classifier 11 j =
      program.execOf interp (honestVal program interp y) 11 j := by
  rw [Native.SourceValues.valuation_of_lookup _ role_norm_2ea_lookup]
  rw [RealizedProgram.execOf_of_priv _ value_norm_2ea_kind]
  exact (honestVal_nat (program := program) (I := interp) y (v := 11) (r := .a) (by change (11, NatRole.a) ∈ nativeRoles program; decide) j).symm
private theorem role_12 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1, y.normIn.nA, y.normIn.nSq, y.normIn.nCc, y.normIn.nNd, y.normIn.nNc, y.normIn.nD, y.normIn.nDc⟩ : Native.SourceValues (interp 0).K).valuation (program := program) classifier 12 j =
      program.execOf interp (honestVal program interp y) 12 j := by
  rw [Native.SourceValues.valuation_of_lookup _ role_norm_2esq_lookup]
  rw [RealizedProgram.execOf_of_priv _ value_norm_2esq_kind]
  exact (honestVal_nat (program := program) (I := interp) y (v := 12) (r := .sq) (by change (12, NatRole.sq) ∈ nativeRoles program; decide) j).symm
private theorem role_13 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1, y.normIn.nA, y.normIn.nSq, y.normIn.nCc, y.normIn.nNd, y.normIn.nNc, y.normIn.nD, y.normIn.nDc⟩ : Native.SourceValues (interp 0).K).valuation (program := program) classifier 13 j =
      program.execOf interp (honestVal program interp y) 13 j := by
  rw [Native.SourceValues.valuation_of_lookup _ role_norm_2ecc_lookup]
  rw [RealizedProgram.execOf_of_priv _ value_norm_2ecc_kind]
  exact (honestVal_nat (program := program) (I := interp) y (v := 13) (r := .cc) (by change (13, NatRole.cc) ∈ nativeRoles program; decide) j).symm
private theorem role_14 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1, y.normIn.nA, y.normIn.nSq, y.normIn.nCc, y.normIn.nNd, y.normIn.nNc, y.normIn.nD, y.normIn.nDc⟩ : Native.SourceValues (interp 0).K).valuation (program := program) classifier 14 j =
      program.execOf interp (honestVal program interp y) 14 j := by
  rw [Native.SourceValues.valuation_of_lookup _ role_norm_2end_lookup]
  rw [RealizedProgram.execOf_of_priv _ value_norm_2end_kind]
  exact (honestVal_nat (program := program) (I := interp) y (v := 14) (r := .nd) (by change (14, NatRole.nd) ∈ nativeRoles program; decide) j).symm
private theorem role_15 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1, y.normIn.nA, y.normIn.nSq, y.normIn.nCc, y.normIn.nNd, y.normIn.nNc, y.normIn.nD, y.normIn.nDc⟩ : Native.SourceValues (interp 0).K).valuation (program := program) classifier 15 j =
      program.execOf interp (honestVal program interp y) 15 j := by
  rw [Native.SourceValues.valuation_of_lookup _ role_norm_2enc_lookup]
  rw [RealizedProgram.execOf_of_priv _ value_norm_2enc_kind]
  exact (honestVal_nat (program := program) (I := interp) y (v := 15) (r := .nc) (by change (15, NatRole.nc) ∈ nativeRoles program; decide) j).symm
private theorem role_16 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1, y.normIn.nA, y.normIn.nSq, y.normIn.nCc, y.normIn.nNd, y.normIn.nNc, y.normIn.nD, y.normIn.nDc⟩ : Native.SourceValues (interp 0).K).valuation (program := program) classifier 16 j =
      program.execOf interp (honestVal program interp y) 16 j := by
  rw [Native.SourceValues.valuation_of_lookup _ role_norm_2eD_lookup]
  rw [RealizedProgram.execOf_of_priv _ value_norm_2eD_kind]
  exact (honestVal_nat (program := program) (I := interp) y (v := 16) (r := .D) (by change (16, NatRole.D) ∈ nativeRoles program; decide) j).symm
private theorem role_17 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1, y.normIn.nA, y.normIn.nSq, y.normIn.nCc, y.normIn.nNd, y.normIn.nNc, y.normIn.nD, y.normIn.nDc⟩ : Native.SourceValues (interp 0).K).valuation (program := program) classifier 17 j =
      program.execOf interp (honestVal program interp y) 17 j := by
  rw [Native.SourceValues.valuation_of_lookup _ role_norm_2eDc_lookup]
  rw [RealizedProgram.execOf_of_priv _ value_norm_2eDc_kind]
  exact (honestVal_nat (program := program) (I := interp) y (v := 17) (r := .Dc) (by change (17, NatRole.Dc) ∈ nativeRoles program; decide) j).symm
/-- **Every checked source execution coordinate reads its existing honest witness value.**
The no-pad-copy premise is supplied by the completion certificate. -/
theorem role_source_coordinates (y : RingIn G) {v j : Nat}
    (hs : program.IsSourceValue v) (hc : program.ExecCoord v j)
    (hpad : ∀ u < program.values.length, program.IsSourceValue u →
      (program.value u).kind.isPadCopy = false) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1, y.normIn.nA, y.normIn.nSq, y.normIn.nCc, y.normIn.nNd, y.normIn.nNc, y.normIn.nD, y.normIn.nDc⟩ : Native.SourceValues (interp 0).K).valuation (program := program) classifier v j =
      program.execOf interp (honestVal program interp y) v j := by
  have hk := hc.source_kind hs hpad
  obtain ⟨r, hr⟩ := rolesOk.exec_covered hc hs hpad
  obtain ⟨hm, hv⟩ := sourceRoleTable_mem hr
  rw [Generated.Falcon512.Ring.Native.QROMParams.SourceRoles.roles_eq] at hm
  simp only [ List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change 4 = v at hv
    subst v
    rw [value_statement_2ering_kind] at hk
    simp only [Kind.isBound, Bool.false_eq_true, reduceCtorEq, or_self] at hk
    exact False.elim hk.2.2
  · change 5 = v at hv
    subst v
    rw [value_statement_2ec_kind] at hk
    simp only [Kind.isBound, Bool.false_eq_true, reduceCtorEq, or_self] at hk
    exact False.elim hk.2.2
  · change 6 = v at hv
    subst v
    exact role_6 y j
  · change 7 = v at hv
    subst v
    exact role_7 y j
  · change 9 = v at hv
    subst v
    exact role_9 y j
  · change 10 = v at hv
    subst v
    exact role_10 y j
  · change 11 = v at hv
    subst v
    exact role_11 y j
  · change 12 = v at hv
    subst v
    exact role_12 y j
  · change 13 = v at hv
    subst v
    exact role_13 y j
  · change 14 = v at hv
    subst v
    exact role_14 y j
  · change 15 = v at hv
    subst v
    exact role_15 y j
  · change 16 = v at hv
    subst v
    exact role_16 y j
  · change 17 = v at hv
    subst v
    exact role_17 y j

end GordieHowe.Falcon512.Ring.Native.QROMParams
