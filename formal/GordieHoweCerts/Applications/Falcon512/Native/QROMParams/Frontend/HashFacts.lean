-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.Falcon512.Frontend.Hash
public import GordieHoweCerts.Applications.Falcon512.Native.QROMParams.Frontend.Facts

@[expose] public section

/-!
# GordieHowe frontend: the Keccak trace's facts of `Falcon512.Native.QROMParams`

The program facts of `h2p.shake` (`FalconHHashData`, `FalconHHash`) for
`GordieHowe.Generated.Falcon512.Native.QROMParams.Program.program` read through its checked shape facts.
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open Generated.Falcon512.Native.QROMParams.Program
open Generated.Falcon512.Native.QROMParams.ShapeFacts
open RealizedProgram
open HashShapeFacts
open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

/-- The constant states: all ones (`const2`), all zeros (`const4`). -/
theorem const_states :
    program.constEntries 1 = List.replicate 1600 1 ∧
    program.constEntries 3 = List.replicate 1600 0 ∧ program.isConstant 1 = true ∧
    program.isConstant 3 = true ∧ program.valueField 1 = 0 ∧ program.valueField 3 = 0 := by
  refine ⟨?_, ?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er0_2econstant_2eleft_2esecond_2efirst_2esecond_2efirst_2efirst_kind, isConstant_of_kind value_h2p_2eshake_2eblocks_2er0_2econstant_2eright_kind, valueShape_field value_h2p_2eshake_2eblocks_2er0_2econstant_2eleft_2esecond_2efirst_2esecond_2efirst_2efirst_header.2, valueShape_field value_h2p_2eshake_2eblocks_2er0_2econstant_2eright_header.2⟩
  · rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er0_2econstant_2eleft_2esecond_2efirst_2esecond_2efirst_2efirst_kind]; decide +kernel
  · rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er0_2econstant_2eright_kind]; decide +kernel

/-- The round constants' states: the bits of `rc t` in lane `(0, 0)`. -/
theorem const_rc :
    ∀ t : Fin 24, program.constEntries (rcLeaf t) =
    List.ofFn (fun j : Fin 1600 => if (j : ℕ) < 64 ∧ (rc t).testBit j then 1 else 0) ∧
    program.isConstant (rcLeaf t) = true ∧ program.valueField (rcLeaf t) = 0 := by
  intro t
  fin_cases t
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er0_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er0_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 2 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er0_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er1_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er1_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 4 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er1_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er2_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er2_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 5 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er2_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er3_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er3_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 6 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er3_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er4_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er4_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 7 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er4_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er5_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er5_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 8 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er5_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er6_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er6_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 9 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er6_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er7_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er7_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 10 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er7_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er8_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er8_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 11 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er8_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er9_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er9_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 12 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er9_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er10_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er10_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 13 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er10_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er11_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er11_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 14 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er11_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er12_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er12_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 15 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er12_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er13_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er13_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 16 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er13_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er14_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er14_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 17 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er14_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er15_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er15_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 18 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er15_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er16_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er16_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 19 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er16_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er17_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er17_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 20 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er17_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er18_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er18_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 21 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er18_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er19_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er19_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 22 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er19_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er6_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er6_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 9 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er6_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er21_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er21_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 23 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er21_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er5_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er5_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 8 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er5_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel
  · refine ⟨?_, isConstant_of_kind value_h2p_2eshake_2eblocks_2er23_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er23_2econstant_2eleft_2esecond_2esecond_header.2⟩
    change program.constEntries 24 = _
    rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er23_2econstant_2eleft_2esecond_2esecond_kind]
    decide +kernel

/-- The `h2p.shake` facts of the program of `Falcon512.Native.QROMParams`, decided over the tables. -/
instance : FalconHHashData program where
  roundShapes := roundShapes
  round_facts := round_facts
  const_states := const_states
  const_rc := const_rc

/-- The predicates of `h2p.shake` are source predicates, decided. -/
theorem shake_source :
    ∀ q < 270, q < program.predicates.length ∧
    program.inSource (program.predicate q) = true := by
  intro q hq
  by_cases h1 : q < 24
  · have h := round_facts 0 ⟨q, h1⟩
    have e : roundPred 0 ⟨q, h1⟩ = q := by simp [roundPred]
    rw [e] at h
    exact ⟨h.1, h.2.1⟩
  by_cases h2 : 30 ≤ q
  · have ht : (q - 30) % 24 < 24 := Nat.mod_lt _ (by decide)
    have hp : (q - 30) / 24 + 1 < 11 := by omega
    have h := round_facts ⟨(q - 30) / 24 + 1, hp⟩ ⟨(q - 30) % 24, ht⟩
    have e : roundPred ⟨(q - 30) / 24 + 1, hp⟩ ⟨(q - 30) % 24, ht⟩ = q := by
      simp only [roundPred, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
        Nat.add_sub_cancel]
      omega
    rw [e] at h
    exact ⟨h.1, h.2.1⟩
  have hq' : q = 24 ∨ q = 25 ∨ q = 26 ∨ q = 27 ∨ q = 28 ∨ q = 29 := by omega
  rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨predicate_h2p_2eshake_2epadding_2emonotone_role.1, program.inSource_of_source predicate_h2p_2eshake_2epadding_2emonotone_role.2⟩
  · exact ⟨predicate_h2p_2eshake_2epadding_2emax_role.1, program.inSource_of_source predicate_h2p_2eshake_2epadding_2emax_role.2⟩
  · exact ⟨predicate_h2p_2eshake_2epadding_2emin_role.1, program.inSource_of_source predicate_h2p_2eshake_2epadding_2emin_role.2⟩
  · exact ⟨predicate_h2p_2eshake_2epadding_2esuffix_role.1, program.inSource_of_source predicate_h2p_2eshake_2epadding_2esuffix_role.2⟩
  · exact ⟨predicate_h2p_2eshake_2epadding_2ezeros_role.1, program.inSource_of_source predicate_h2p_2eshake_2epadding_2ezeros_role.2⟩
  · exact ⟨predicate_h2p_2eshake_2epadding_2eoutput_role.1, program.inSource_of_source predicate_h2p_2eshake_2epadding_2eoutput_role.2⟩

/-- Facts of the absorbed block's selector and the squeezes' inputs, decided. -/
theorem squeezeIn_facts :
    idx22.entry 0 = 0 ∧ idx22.entry 1 = 1 ∧ idx23.entry 0 = 0 ∧
    idx24.entry 0 = 1 ∧ (∀ j < 1600, idx25.entry j = 0) ∧ (∀ j < 1600, idx5.entry j = j) ∧
    idx25.size = 1600 ∧ (program.value 25).size = 1 ∧ program.isConstant 25 = true ∧
    program.isConstant 27 = true ∧ program.valueField 25 = 0 ∧ program.valueField 27 = 0 ∧
    (program.constEntries 25).getD 0 0 = 1 ∧ (program.constEntries 27).getD 0 0 = 0 ∧
    29 < program.predicates.length ∧ program.inSource (program.predicate 29) = true ∧
    56 < program.exprs.length := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    valueShape_size value_h2p_2eshake_2epadding_2emin_2econstant_2eleft_2esecond_header.2, isConstant_of_kind value_h2p_2eshake_2epadding_2emin_2econstant_2eleft_2esecond_kind, isConstant_of_kind value_h2p_2eshake_2epadding_2emax_2econstant_2eright_kind,
    valueShape_field value_h2p_2eshake_2epadding_2emin_2econstant_2eleft_2esecond_header.2, valueShape_field value_h2p_2eshake_2epadding_2emax_2econstant_2eright_header.2, ?_, ?_, predicate_h2p_2eshake_2epadding_2eoutput_role.1, program.inSource_of_source predicate_h2p_2eshake_2epadding_2eoutput_role.2,
    expr_lt_of_ne_default (by rw [expr_h2p_2eshake_2esqueeze_2er0_2eshape_2eleft_2esecond_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_eq]; intro hc; cases hc)⟩
  · rw [constEntries_of_kind value_h2p_2eshake_2epadding_2emin_2econstant_2eleft_2esecond_kind]; rfl
  · rw [constEntries_of_kind value_h2p_2eshake_2epadding_2emax_2econstant_2eright_kind]; rfl

/-- Facts of the flags and the padding predicates, decided. -/
theorem flag_facts :
    (47 < program.values.length ∧ program.IsSourceValue 47 ∧
    (program.value 47).typeSource = .node ∧ (program.value 47).type = .bit) ∧
    (program.value 47).size = 136 ∧
    (∀ i < 135, idx14.entry i = i + 1) ∧ (∀ i < 135, idx15.entry i = i) ∧
    (∀ i < 135, idx16.entry i = 0) ∧ idx17.entry 0 = 72 ∧ idx18.entry 0 = 39 ∧
    idx14.size = 135 ∧ idx17.size = 1 ∧ idx18.size = 1 ∧
    program.isConstant 26 = true ∧ program.valueField 26 = 0 ∧
    (∀ i < 135, (program.constEntries 26).getD i 0 = 0) ∧
    (∀ p ∈ [24, 25, 26, 27, 28], p < program.predicates.length ∧
    program.inSource (program.predicate p) = true) := by
  refine ⟨⟨value_message_2ein_5fmessage_header.1, valueShape_role value_message_2ein_5fmessage_header.2, valueShape_typeSource value_message_2ein_5fmessage_header.2,
      value_message_2ein_5fmessage_type.2⟩, valueShape_size value_message_2ein_5fmessage_header.2, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, isConstant_of_kind value_h2p_2eshake_2epadding_2emonotone_2econstant_2eright_kind, valueShape_field value_h2p_2eshake_2epadding_2emonotone_2econstant_2eright_header.2, ?_, ?_⟩
  · rw [constEntries_of_kind value_h2p_2eshake_2epadding_2emonotone_2econstant_2eright_kind]; decide +kernel
  · intro p hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact ⟨predicate_h2p_2eshake_2epadding_2emonotone_role.1, program.inSource_of_source predicate_h2p_2eshake_2epadding_2emonotone_role.2⟩
    · exact ⟨predicate_h2p_2eshake_2epadding_2emax_role.1, program.inSource_of_source predicate_h2p_2eshake_2epadding_2emax_role.2⟩
    · exact ⟨predicate_h2p_2eshake_2epadding_2emin_role.1, program.inSource_of_source predicate_h2p_2eshake_2epadding_2emin_role.2⟩
    · exact ⟨predicate_h2p_2eshake_2epadding_2esuffix_role.1, program.inSource_of_source predicate_h2p_2eshake_2epadding_2esuffix_role.2⟩
    · exact ⟨predicate_h2p_2eshake_2epadding_2ezeros_role.1, program.inSource_of_source predicate_h2p_2eshake_2epadding_2ezeros_role.2⟩

/-- Facts of the absorbed block and the padding's constants, decided. -/
theorem absorb_facts :
    (∀ j < 1088, idx4.entry j = j) ∧ idx4.size = 1088 ∧
    (∀ i < 136, idx19.entry i = i) ∧ (∀ i < 136, ∀ t < 8, idx20.entry (i * 8 + t) = t) ∧
    (∀ i < 136, idx21.entry i = 0) ∧ idx19.size = 136 ∧ idx15.size = 135 ∧
    (program.value 45).size = 320 ∧ (program.value 46).size = 768 ∧ (program.value 27).size = 1 ∧
    program.constEntries 0 = List.replicate 512 0 ∧
    (∀ t < 8, (program.constEntries 28).getD t 0 = (program.constEntries 39).getD t 0) ∧
    (∀ i < 135, (program.constEntries 29).getD i 0 =
    (program.constEntries 39).getD 0 0 ^^^ (program.constEntries 39).getD 1 0 ^^^
    (program.constEntries 39).getD 2 0 ^^^ (program.constEntries 39).getD 3 0 ^^^
    (program.constEntries 39).getD 4 0) ∧
    (∀ i < 136, (program.constEntries 30).getD i 0 = 0) ∧
    (∀ i < 135, (program.constEntries 31).getD i 0 = 0) ∧
    (program.constEntries 31).getD 135 0 = (program.constEntries 39).getD 7 0 ∧
    (∀ v ∈ [0, 28, 29, 30, 31], program.isConstant v = true ∧ program.valueField v = 0) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    valueShape_size value_nonce_header.2, valueShape_size value_message_header.2, valueShape_size value_h2p_2eshake_2epadding_2emax_2econstant_2eright_header.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [constEntries_of_kind value_h2p_2eshake_2eblocks_2er0_2econstant_2eleft_2esecond_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2esecond_kind]; decide +kernel
  · rw [constEntries_of_kind value_h2p_2eshake_2epadding_2esuffix_2econstant_2eleft_2esecond_2efirst_2eshared_2efirst_2esecond_2efirst_kind, constEntries_of_kind value_h2p_2eselect_2eroute_2econstant_2eleft_2esecond_2efirst_2esecond_2efirst_kind]; decide +kernel
  · rw [constEntries_of_kind value_h2p_2eshake_2epadding_2esuffix_2econstant_2eleft_2esecond_2esecond_kind, constEntries_of_kind value_h2p_2eselect_2eroute_2econstant_2eleft_2esecond_2efirst_2esecond_2efirst_kind]; decide +kernel
  · rw [constEntries_of_kind value_h2p_2eshake_2epadding_2esuffix_2econstant_2eright_kind]; decide +kernel
  · rw [constEntries_of_kind value_h2p_2eshake_2epadding_2ezeros_2econstant_2eleft_2esecond_2esecond_2esecond_kind]; decide +kernel
  · rw [constEntries_of_kind value_h2p_2eshake_2epadding_2ezeros_2econstant_2eleft_2esecond_2esecond_2esecond_kind, constEntries_of_kind value_h2p_2eselect_2eroute_2econstant_2eleft_2esecond_2efirst_2esecond_2efirst_kind]; decide +kernel
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact ⟨isConstant_of_kind value_h2p_2eshake_2eblocks_2er0_2econstant_2eleft_2esecond_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2esecond_kind, valueShape_field value_h2p_2eshake_2eblocks_2er0_2econstant_2eleft_2esecond_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2esecond_header.2⟩
    · exact ⟨isConstant_of_kind value_h2p_2eshake_2epadding_2esuffix_2econstant_2eleft_2esecond_2efirst_2eshared_2efirst_2esecond_2efirst_kind, valueShape_field value_h2p_2eshake_2epadding_2esuffix_2econstant_2eleft_2esecond_2efirst_2eshared_2efirst_2esecond_2efirst_header.2⟩
    · exact ⟨isConstant_of_kind value_h2p_2eshake_2epadding_2esuffix_2econstant_2eleft_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2epadding_2esuffix_2econstant_2eleft_2esecond_2esecond_header.2⟩
    · exact ⟨isConstant_of_kind value_h2p_2eshake_2epadding_2esuffix_2econstant_2eright_kind, valueShape_field value_h2p_2eshake_2epadding_2esuffix_2econstant_2eright_header.2⟩
    · exact ⟨isConstant_of_kind value_h2p_2eshake_2epadding_2ezeros_2econstant_2eleft_2esecond_2esecond_2esecond_kind, valueShape_field value_h2p_2eshake_2epadding_2ezeros_2econstant_2eleft_2esecond_2esecond_2esecond_header.2⟩

/-- The views' sizes, decided. -/
theorem view_sizes :
    (program.value 97).size = 1600 ∧ (program.value 146).size = 1088 ∧
    (program.value 195).size = 1088 ∧ (program.value 244).size = 1088 ∧
    (program.value 293).size = 1088 ∧ (program.value 342).size = 1088 ∧
    (program.value 391).size = 1088 ∧ (program.value 440).size = 1088 ∧
    (program.value 489).size = 1088 ∧ (program.value 538).size = 1088 ∧
    (program.value 587).size = 592 ∧ 537 < program.exprs.length := by
  exact ⟨valueShape_size value_h2p_2eshake_2estate_header.2, valueShape_size value_h2p_2eshake_2eout_2ep1_header.2, valueShape_size value_h2p_2eshake_2eout_2ep2_header.2, valueShape_size value_h2p_2eshake_2eout_2ep3_header.2, valueShape_size value_h2p_2eshake_2eout_2ep4_header.2, valueShape_size value_h2p_2eshake_2eout_2ep5_header.2, valueShape_size value_h2p_2eshake_2eout_2ep6_header.2, valueShape_size value_h2p_2eshake_2eout_2ep7_header.2, valueShape_size value_h2p_2eshake_2eout_2ep8_header.2, valueShape_size value_h2p_2eshake_2eout_2ep9_header.2, valueShape_size value_h2p_2eshake_2eout_2ep10_header.2,
    expr_lt_of_ne_default (by rw [expr_h2p_2eselect_2eroute_2eshape_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2eargument_2e0_eq]; intro hc; cases hc)⟩

/-- Facts of the views' selections, decided. -/
theorem view_sel :
    idx0.size = 100 ∧ idx1.size = 68 ∧ idx2.size = 37 ∧
    (∀ j < 100, idx0.entry j = j) ∧ (∀ j < 68, idx1.entry j = j) ∧ (∀ j < 37, idx2.entry j = j) ∧
    ∀ k : Fin 10, program.valueField (viewVal (k + 1)) = 0 ∧
    program.valueField (outVal (k + 1) 23) = 0 ∧ (program.value (outVal (k + 1) 23)).size = 1600 ∧
    (program.value (viewVal (k + 1))).size = zslot (k + 1) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fun k => ?_⟩
  fin_cases k
  · have h := word_facts 1 23
    exact ⟨valueShape_field value_h2p_2eshake_2eout_2ep1_header.2, h.2.2.2.2.1, h.2.2.2.2.2.2.1, valueShape_size value_h2p_2eshake_2eout_2ep1_header.2⟩
  · have h := word_facts 2 23
    exact ⟨valueShape_field value_h2p_2eshake_2eout_2ep2_header.2, h.2.2.2.2.1, h.2.2.2.2.2.2.1, valueShape_size value_h2p_2eshake_2eout_2ep2_header.2⟩
  · have h := word_facts 3 23
    exact ⟨valueShape_field value_h2p_2eshake_2eout_2ep3_header.2, h.2.2.2.2.1, h.2.2.2.2.2.2.1, valueShape_size value_h2p_2eshake_2eout_2ep3_header.2⟩
  · have h := word_facts 4 23
    exact ⟨valueShape_field value_h2p_2eshake_2eout_2ep4_header.2, h.2.2.2.2.1, h.2.2.2.2.2.2.1, valueShape_size value_h2p_2eshake_2eout_2ep4_header.2⟩
  · have h := word_facts 5 23
    exact ⟨valueShape_field value_h2p_2eshake_2eout_2ep5_header.2, h.2.2.2.2.1, h.2.2.2.2.2.2.1, valueShape_size value_h2p_2eshake_2eout_2ep5_header.2⟩
  · have h := word_facts 6 23
    exact ⟨valueShape_field value_h2p_2eshake_2eout_2ep6_header.2, h.2.2.2.2.1, h.2.2.2.2.2.2.1, valueShape_size value_h2p_2eshake_2eout_2ep6_header.2⟩
  · have h := word_facts 7 23
    exact ⟨valueShape_field value_h2p_2eshake_2eout_2ep7_header.2, h.2.2.2.2.1, h.2.2.2.2.2.2.1, valueShape_size value_h2p_2eshake_2eout_2ep7_header.2⟩
  · have h := word_facts 8 23
    exact ⟨valueShape_field value_h2p_2eshake_2eout_2ep8_header.2, h.2.2.2.2.1, h.2.2.2.2.2.2.1, valueShape_size value_h2p_2eshake_2eout_2ep8_header.2⟩
  · have h := word_facts 9 23
    exact ⟨valueShape_field value_h2p_2eshake_2eout_2ep9_header.2, h.2.2.2.2.1, h.2.2.2.2.2.2.1, valueShape_size value_h2p_2eshake_2eout_2ep9_header.2⟩
  · have h := word_facts 10 23
    exact ⟨valueShape_field value_h2p_2eshake_2eout_2ep10_header.2, h.2.2.2.2.1, h.2.2.2.2.2.2.1, valueShape_size value_h2p_2eshake_2eout_2ep10_header.2⟩

/-- Facts of the nonce and the message part, decided: bit-typed source values. -/
theorem buf_facts :
    (45 < program.values.length ∧ program.IsSourceValue 45 ∧
    (program.value 45).typeSource = .node ∧ (program.value 45).type = .bit) ∧
    (46 < program.values.length ∧ program.IsSourceValue 46 ∧
    (program.value 46).typeSource = .node ∧ (program.value 46).type = .bit) := by
  exact ⟨⟨value_nonce_header.1, valueShape_role value_nonce_header.2, valueShape_typeSource value_nonce_header.2, value_nonce_type.2⟩,
    ⟨value_message_header.1, valueShape_role value_message_header.2, valueShape_typeSource value_message_header.2, value_message_type.2⟩⟩

/-- expr_squeezeIn. -/
theorem expr_squeezeIn :
    program.expr 53 = .reindex idx22 (.concat (.leaf 25) (.leaf 27)) ∧
    program.expr 54 = .add (.reindex idx23 (.ref 53)) (.reindex idx24 (.ref 53)) ∧
    program.expr 55 = .reindex idx5 (.leaf 95) ∧ program.expr 56 = .reindex idx5 (.leaf 97) ∧
    program.predicate 29 = «p.h2p.shake.padding.output» :=
  ⟨expr_h2p_2eshake_2epadding_2eoutput_2eshape_2eleft_2efirst_2efirst_2eshared_2efirst_2efirst_eq, expr_h2p_2eshake_2epadding_2eoutput_2eshape_2eleft_2efirst_2efirst_eq, expr_h2p_2eshake_2epadding_2eoutput_2eshape_2eleft_2esecond_2esecond_2efirst_eq, expr_h2p_2eshake_2esqueeze_2er0_2eshape_2eleft_2esecond_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_eq, RealizedProgram.Predicate.eq_of_equalParts predicate_h2p_2eshake_2epadding_2eoutput_body ⟨_, rfl⟩ predicate_h2p_2eshake_2epadding_2eoutput_header⟩

/-- pred_padding. -/
theorem pred_padding :
    program.predicate 24 = «p.h2p.shake.padding.monotone» ∧
    program.predicate 25 = «p.h2p.shake.padding.max» ∧
    program.predicate 26 = «p.h2p.shake.padding.min» ∧
    program.predicate 27 = «p.h2p.shake.padding.suffix» ∧
    program.predicate 28 = «p.h2p.shake.padding.zeros» :=
  ⟨RealizedProgram.Predicate.eq_of_equalParts predicate_h2p_2eshake_2epadding_2emonotone_body ⟨_, rfl⟩ predicate_h2p_2eshake_2epadding_2emonotone_header,
    RealizedProgram.Predicate.eq_of_equalParts predicate_h2p_2eshake_2epadding_2emax_body ⟨_, rfl⟩ predicate_h2p_2eshake_2epadding_2emax_header,
    RealizedProgram.Predicate.eq_of_equalParts predicate_h2p_2eshake_2epadding_2emin_body ⟨_, rfl⟩ predicate_h2p_2eshake_2epadding_2emin_header,
    RealizedProgram.Predicate.eq_of_equalParts predicate_h2p_2eshake_2epadding_2esuffix_body ⟨_, rfl⟩ predicate_h2p_2eshake_2epadding_2esuffix_header,
    RealizedProgram.Predicate.eq_of_equalParts predicate_h2p_2eshake_2epadding_2ezeros_body ⟨_, rfl⟩ predicate_h2p_2eshake_2epadding_2ezeros_header⟩

/-- expr_absorb. -/
theorem expr_absorb :
    program.expr 0 =
    .reindex idx4 (.concat (.leaf 45) (.leaf 46)) ∧
    program.expr 1 = .reindex idx4 (.ref 0) ∧
    program.expr 2 =
    .reindex idx5 (.reindex idx5 (.concat (.reindex idx4 (.reindex idx4 (.ref 1))) (.leaf 0))) ∧
    program.expr 51 = .reindex idx19 (.concat (.leaf 25) (.reindex idx15 (.leaf 47))) ∧
    program.expr 52 = .apply (.sum 8) (.mul (.reindex idx4 (.reindex idx4 (.ref 1)))
    (.reindex idx20 (.leaf 28))) :=
  ⟨expr_h2p_2eshake_2epadding_2esuffix_2eshape_2eleft_2esecond_2efirst_2eshared_2efirst_2efirst_2efirst_2efirst_2eshared_2efirst_eq, expr_h2p_2eshake_2epadding_2esuffix_2eshape_2eleft_2esecond_2efirst_2eshared_2efirst_2efirst_2efirst_2efirst_eq, expr_h2p_2eshake_2eblocks_2er0_2eshape_2eleft_2esecond_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_eq, expr_h2p_2eshake_2epadding_2esuffix_2eshape_2eleft_2efirst_2efirst_eq, expr_h2p_2eshake_2epadding_2esuffix_2eshape_2eleft_2esecond_2efirst_eq⟩

/-- The stream's expression. -/
theorem expr537 :
    program.expr 537 =
    .reindex idx28 (RealizedProgram.concatR (.leaf 97)
      [.leaf 146, .leaf 195, .leaf 244, .leaf 293, .leaf 342, .leaf 391, .leaf 440, .leaf 489,
        .leaf 538, .leaf 587]) :=
  expr_h2p_2eselect_2eroute_2eshape_2eleft_2efirst_2efirst_2efirst_2eshared_2efirst_2efirst_2efirst_2eshared_2eargument_2e0_eq

/-- The stream's index map, decided. -/
theorem idx28_entry : ∀ i < 717, ∀ b < 16, idx28.entry (16 * i + b) =
    (if i < 68 then 0 else 1600 + 1088 * (i / 68 - 1)) +
      (16 * (i % 68) + if b < 8 then b + 8 else b - 8) :=
  idx_stream_entry rfl

/-- The view kinds of the output views. -/
theorem view_kinds : ∀ k : Fin 10,
    (program.value (viewVal (k + 1))).kind =
        .bits (outVal (k + 1) 23 - 1) (if (k : ℕ) + 1 = 10 then idx2 else idx1) ∧
      (program.value (outVal (k + 1) 23)).kind = .bits (outVal (k + 1) 23 - 1) idx0 ∧
      (program.value (outVal (k + 1) 23 - 1)).kind = .priv := by
  intro k
  fin_cases k
  · exact ⟨value_h2p_2eshake_2eout_2ep1_kind, (word_facts 1 23).1, (word_facts 1 23).2.1⟩
  · exact ⟨value_h2p_2eshake_2eout_2ep2_kind, (word_facts 2 23).1, (word_facts 2 23).2.1⟩
  · exact ⟨value_h2p_2eshake_2eout_2ep3_kind, (word_facts 3 23).1, (word_facts 3 23).2.1⟩
  · exact ⟨value_h2p_2eshake_2eout_2ep4_kind, (word_facts 4 23).1, (word_facts 4 23).2.1⟩
  · exact ⟨value_h2p_2eshake_2eout_2ep5_kind, (word_facts 5 23).1, (word_facts 5 23).2.1⟩
  · exact ⟨value_h2p_2eshake_2eout_2ep6_kind, (word_facts 6 23).1, (word_facts 6 23).2.1⟩
  · exact ⟨value_h2p_2eshake_2eout_2ep7_kind, (word_facts 7 23).1, (word_facts 7 23).2.1⟩
  · exact ⟨value_h2p_2eshake_2eout_2ep8_kind, (word_facts 8 23).1, (word_facts 8 23).2.1⟩
  · exact ⟨value_h2p_2eshake_2eout_2ep9_kind, (word_facts 9 23).1, (word_facts 9 23).2.1⟩
  · exact ⟨value_h2p_2eshake_2eout_2ep10_kind, (word_facts 10 23).1, (word_facts 10 23).2.1⟩

/-- The `h2p.shake` facts of the program of `Falcon512.Native.QROMParams`. -/
instance : FalconHHash program where
  shake_source := shake_source
  expr_squeezeIn := expr_squeezeIn
  squeezeIn_facts := squeezeIn_facts
  pred_padding := pred_padding
  flag_facts := flag_facts
  absorb_facts := absorb_facts
  expr_absorb := expr_absorb
  expr537 := expr537
  idx28_entry := idx28_entry
  view_sizes := view_sizes
  view_kinds := view_kinds
  view_sel := view_sel
  buf_facts := buf_facts

end GordieHowe.Falcon512.Native.QROMParams
