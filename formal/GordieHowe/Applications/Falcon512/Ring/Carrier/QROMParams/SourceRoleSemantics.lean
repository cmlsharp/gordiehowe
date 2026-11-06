-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Carrier.SourceRoles
public import GordieHowe.Applications.Falcon512.Ring.Carrier.QROMParams.Facts
public import GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.SourceRoleFacts

public section

/-!
# Carrier witness meanings for the checked source roles

The metadata checker certifies placement and coverage. These proofs separately connect each
checked tag and slot to the existing honest-value specification, including values bound to
generated digits. No honest predicate, statement check or charged event is changed.
-/

namespace GordieHowe.Falcon512.Ring.Carrier.QROMParams
open RealizedProgram _root_.GordieHowe.Falcon512.Ring
open Generated.Falcon512.Ring.Carrier.QROMParams.Program (program)
open Generated.Falcon512.Ring.Carrier.QROMParams (interp)
open Generated.Falcon512.Ring.Carrier.QROMParams.SourceRoleFacts
variable {msgLen : Nat} {G : Native.Signer msgLen}

local notation "classifier" => Generated.Falcon512.Ring.Carrier.QROMParams.SourceRoles.classifier

private theorem role_spectrum (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1,
      Carrier.quot y.normIn, Carrier.mag1 y.normIn, Carrier.mag2 y.normIn,
      Carrier.squares y.normIn⟩ : Carrier.SourceValues (interp 0).K).valuation (program := program) classifier 6 j =
      program.execOf interp (honestVal program interp y) 6 j := by
  rw [SourceValues.valuation_of_lookup _ role_key_2espectrum_lookup]
  have hp := (FalconRingMember.privKinds (program := program)).1
  change (program.value 6).kind = .priv at hp
  rw [RealizedProgram.execOf_of_priv _ hp]
  exact (honestVal_spec y j).symm

private theorem role_selection (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1,
      Carrier.quot y.normIn, Carrier.mag1 y.normIn, Carrier.mag2 y.normIn,
      Carrier.squares y.normIn⟩ : Carrier.SourceValues (interp 0).K).valuation (program := program) classifier 7 j =
      program.execOf interp (honestVal program interp y) 7 j := by
  rw [SourceValues.valuation_of_lookup _ role_member_2esigner_2eindex_lookup]
  have hp := (FalconRingMember.privKinds (program := program)).2.1
  change (program.value 7).kind = .priv at hp
  rw [RealizedProgram.execOf_of_priv _ hp]
  exact (honestVal_bit y j).symm

private theorem role_s2 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1,
      Carrier.quot y.normIn, Carrier.mag1 y.normIn, Carrier.mag2 y.normIn,
      Carrier.squares y.normIn⟩ : Carrier.SourceValues (interp 0).K).valuation (program := program) classifier 9 j =
      program.execOf interp (honestVal program interp y) 9 j := by
  rw [SourceValues.valuation_of_lookup _ role_s2_lookup]
  have hp := (FalconRingMember.privKinds (program := program)).2.2
  change (program.value 9).kind = .priv at hp
  rw [RealizedProgram.execOf_of_priv _ hp]
  exact (honestVal_nat (program := program) (I := interp) y
    (v := 9) (r := .s2) (by change (9, NatRole.s2) ∈ carrierRoles; decide) j).symm

private theorem role_s1 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1,
      Carrier.quot y.normIn, Carrier.mag1 y.normIn, Carrier.mag2 y.normIn,
      Carrier.squares y.normIn⟩ : Carrier.SourceValues (interp 0).K).valuation (program := program) classifier 10 j =
      program.execOf interp (honestVal program interp y) 10 j := by
  rw [SourceValues.valuation_of_lookup _ role_signature_2es1_lookup]
  have hp := (FalconCarrierBase.privKinds (program := program)).1
  change (program.value 10).kind = .priv at hp
  rw [RealizedProgram.execOf_of_priv _ hp]
  exact (honestVal_nat (program := program) (I := interp) y
    (v := 10) (r := .s1) (by change (10, NatRole.s1) ∈ carrierRoles; decide) j).symm

private theorem role_mag2 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1,
      Carrier.quot y.normIn, Carrier.mag1 y.normIn, Carrier.mag2 y.normIn,
      Carrier.squares y.normIn⟩ : Carrier.SourceValues (interp 0).K).valuation (program := program) classifier 13 j =
      program.execOf interp (honestVal program interp y) 13 j := by
  rw [SourceValues.valuation_of_lookup _ role_magnitudes_2emag2_lookup]
  have hp := (FalconCarrierBase.privKinds (program := program)).2.1
  change (program.value 13).kind = .priv at hp
  rw [RealizedProgram.execOf_of_priv _ hp]
  exact (honestVal_nat (program := program) (I := interp) y
    (v := 13) (r := .mag2) (by change (13, NatRole.mag2) ∈ carrierRoles; decide) j).symm

private theorem role_low2 (y : RingIn G) (j : Nat) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1,
      Carrier.quot y.normIn, Carrier.mag1 y.normIn, Carrier.mag2 y.normIn,
      Carrier.squares y.normIn⟩ : Carrier.SourceValues (interp 0).K).valuation (program := program) classifier 14 j =
      program.execOf interp (honestVal program interp y) 14 j := by
  rw [SourceValues.valuation_of_lookup _ role_encoding_2elow2_lookup]
  have hp := (FalconCarrierBase.privKinds (program := program)).2.2
  change (program.value 14).kind = .priv at hp
  rw [RealizedProgram.execOf_of_priv _ hp]
  exact (honestVal_nat (program := program) (I := interp) y
    (v := 14) (r := .low2) (by change (14, NatRole.low2) ∈ carrierRoles; decide) j).symm

private theorem role_quotient (y : RingIn G) {j : Nat} (hj : j < 512) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1,
      Carrier.quot y.normIn, Carrier.mag1 y.normIn, Carrier.mag2 y.normIn,
      Carrier.squares y.normIn⟩ : Carrier.SourceValues (interp 0).K).valuation (program := program) classifier 11 j =
      program.execOf interp (honestVal program interp y) 11 j := by
  rw [SourceValues.valuation_of_lookup _ role_signature_2eequation_2eq_lookup]
  have hf := FalconCarrierHonest.fields (program := program) 11 (by simp)
  apply (castElt_inj_of_eq hf).1
  rw [castElt_castElt_of_eq hf.symm, carrier_execOf_quot (program := program) (I := interp) y hj]
  rfl

private theorem role_mag1 (y : RingIn G) {j : Nat} (hj : j < 512) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1,
      Carrier.quot y.normIn, Carrier.mag1 y.normIn, Carrier.mag2 y.normIn,
      Carrier.squares y.normIn⟩ : Carrier.SourceValues (interp 0).K).valuation (program := program) classifier 12 j =
      program.execOf interp (honestVal program interp y) 12 j := by
  rw [SourceValues.valuation_of_lookup _ role_magnitudes_2emag1_lookup]
  have hf := FalconCarrierHonest.fields (program := program) 12 (by simp)
  apply (castElt_inj_of_eq hf).1
  rw [castElt_castElt_of_eq hf.symm, carrier_execOf_mag1 (program := program) (I := interp) y hj]
  rfl

private theorem role_squares (y : RingIn G) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1,
      Carrier.quot y.normIn, Carrier.mag1 y.normIn, Carrier.mag2 y.normIn,
      Carrier.squares y.normIn⟩ : Carrier.SourceValues (interp 0).K).valuation (program := program) classifier 16 0 =
      program.execOf interp (honestVal program interp y) 16 0 := by
  rw [SourceValues.valuation_of_lookup _ role_norm_2esquares_lookup]
  have hf := FalconCarrierHonest.fields (program := program) 16 (by simp)
  apply (castElt_inj_of_eq hf).1
  rw [castElt_castElt_of_eq hf.symm, carrier_execOf_squares (program := program) (I := interp) y]
  rfl

/-- **Every source execution coordinate reads its unchanged honest witness value.**
The no-pad-copy premise is supplied by the existing completion certificate. -/
theorem role_source_coordinates (y : RingIn G) {v j : Nat}
    (hs : program.IsSourceValue v) (hc : program.ExecCoord v j)
    (hpad : ∀ u < program.values.length, program.IsSourceValue u →
      (program.value u).kind.isPadCopy = false) :
    (⟨specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1,
      Carrier.quot y.normIn, Carrier.mag1 y.normIn, Carrier.mag2 y.normIn,
      Carrier.squares y.normIn⟩ : Carrier.SourceValues (interp 0).K).valuation (program := program) classifier v j =
      program.execOf interp (honestVal program interp y) v j := by
  have hk := hc.source_kind hs hpad
  obtain ⟨r, hr⟩ := rolesOk.exec_covered hc hs hpad
  obtain ⟨hm, hv⟩ := sourceRoleTable_mem hr
  rw [Generated.Falcon512.Ring.Carrier.QROMParams.SourceRoles.roles_eq] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change 4 = v at hv
    subst v
    rw [Generated.Falcon512.Ring.Carrier.QROMParams.ShapeFacts.value_statement_2ering_kind] at hk
    simp only [Kind.isBound, Bool.false_eq_true, reduceCtorEq, or_self] at hk
    exact False.elim hk.2.2
  · change 5 = v at hv
    subst v
    rw [Generated.Falcon512.Ring.Carrier.QROMParams.ShapeFacts.value_statement_2ec_kind] at hk
    simp only [Kind.isBound, Bool.false_eq_true, reduceCtorEq, or_self] at hk
    exact False.elim hk.2.2
  · change 6 = v at hv
    subst v
    exact role_spectrum y j
  · change 7 = v at hv
    subst v
    exact role_selection y j
  · change 9 = v at hv
    subst v
    exact role_s2 y j
  · change 10 = v at hv
    subst v
    exact role_s1 y j
  · change 11 = v at hv
    subst v
    exact role_quotient y (by simpa only [(FalconCarrierBase.sizes (program := program)).2.1] using hk.2.1)
  · change 12 = v at hv
    subst v
    exact role_mag1 y (by simpa only [(FalconCarrierBase.sizes (program := program)).2.2.1] using hk.2.1)
  · change 13 = v at hv
    subst v
    exact role_mag2 y j
  · change 14 = v at hv
    subst v
    exact role_low2 y j
  · change 16 = v at hv
    subst v
    have hj : j < 1 := by
      simpa only [(FalconCarrierBase.sizes (program := program)).2.2.2.2.2] using hk.2.1
    have : j = 0 := by omega
    subst j
    exact role_squares y

end GordieHowe.Falcon512.Ring.Carrier.QROMParams
