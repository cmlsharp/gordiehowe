-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Frontend.Hash
public import GordieHowe.Language.Honest.Source
public import GordieHowe.Generated.MLDSA44.Native.ROMParams.Core
public import GordieHowe.Generated.MLDSA44.Native.ROMParams.ShapeFacts

public section

/-! Honest hash word facts from the checked value kinds, metadata, and declared types.
Each permutation is proved separately; no program or plan table is evaluated here. -/

namespace GordieHowe.MLDSA44.Native.ROMParams.HonestWordFacts
open RealizedProgram
open _root_.GordieHowe.Generated.MLDSA44.Native.ROMParams
open Program (program)
open _root_.GordieHowe.Generated.MLDSA44.Native.ROMParams.Program (idx0 idx1 idx2 idx5)
open ShapeFacts
attribute [local irreducible] Program.idx0 Program.idx1 Program.idx2 Program.idx5

private theorem wordsChecks0 (t : Fin 24) :
    program.isBitsB (outVal (0 : Fin 10) t) ((outVal (0 : Fin 10) t - 1)) idx1 = true ∧
    program.privCellB ((outVal (0 : Fin 10) t - 1)) = true ∧ program.valueField (outVal (0 : Fin 10) t) = 1 ∧
    program.valueField ((outVal (0 : Fin 10) t - 1)) = 1 ∧ (program.value (outVal (0 : Fin 10) t)).size = 1600 ∧
    (program.value ((outVal (0 : Fin 10) t - 1))).size = 100 ∧
    (program.value ((outVal (0 : Fin 10) t - 1))).type.nodeName = some "GF(2^16)" := by
  fin_cases t
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er0_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er0_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er0_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er0_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er0_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er0_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er0_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er0_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er1_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er1_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er1_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er1_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er1_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er1_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er1_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er1_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er2_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er2_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er2_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er2_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er2_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er2_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er2_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er2_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er3_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er3_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er3_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er3_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er3_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er3_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er3_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er3_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er4_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er4_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er4_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er4_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er4_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er4_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er4_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er4_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er5_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er5_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er5_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er5_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er5_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er5_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er5_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er5_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er6_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er6_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er6_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er6_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er6_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er6_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er6_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er6_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er7_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er7_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er7_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er7_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er7_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er7_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er7_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er7_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er8_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er8_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er8_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er8_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er8_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er8_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er8_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er8_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er9_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er9_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er9_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er9_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er9_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er9_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er9_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er9_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er10_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er10_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er10_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er10_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er10_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er10_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er10_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er10_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er11_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er11_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er11_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er11_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er11_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er11_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er11_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er11_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er12_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er12_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er12_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er12_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er12_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er12_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er12_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er12_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er13_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er13_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er13_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er13_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er13_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er13_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er13_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er13_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er14_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er14_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er14_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er14_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er14_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er14_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er14_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er14_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er15_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er15_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er15_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er15_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er15_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er15_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er15_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er15_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er16_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er16_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er16_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er16_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er16_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er16_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er16_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er16_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er17_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er17_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er17_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er17_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er17_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er17_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er17_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er17_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er18_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er18_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er18_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er18_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er18_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er18_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er18_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er18_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er19_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er19_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er19_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er19_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er19_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er19_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er19_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er19_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er20_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er20_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er20_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er20_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er20_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er20_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er20_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er20_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er21_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er21_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er21_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er21_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er21_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er21_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er21_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er21_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er22_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er22_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er22_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er22_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er22_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er22_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er22_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er22_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2emu_2eblocks_2er23_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eblocks_2er23_2evalue_2ewords_header.1 value_h2c_2emu_2eblocks_2er23_2evalue_2ewords_kind,
      valueShape_field value_h2c_2emu_2eblocks_2er23_2evalue_header.2, valueShape_field value_h2c_2emu_2eblocks_2er23_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2emu_2eblocks_2er23_2evalue_header.2, valueShape_size value_h2c_2emu_2eblocks_2er23_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2emu_2eblocks_2er23_2evalue_2ewords_type.2⟩

private theorem wordsChecks1 (t : Fin 24) :
    program.isBitsB (outVal (1 : Fin 10) t) ((outVal (1 : Fin 10) t - 1)) idx1 = true ∧
    program.privCellB ((outVal (1 : Fin 10) t - 1)) = true ∧ program.valueField (outVal (1 : Fin 10) t) = 1 ∧
    program.valueField ((outVal (1 : Fin 10) t - 1)) = 1 ∧ (program.value (outVal (1 : Fin 10) t)).size = 1600 ∧
    (program.value ((outVal (1 : Fin 10) t - 1))).size = 100 ∧
    (program.value ((outVal (1 : Fin 10) t - 1))).type.nodeName = some "GF(2^16)" := by
  fin_cases t
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er0_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er0_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er0_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er0_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er0_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er0_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er0_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er0_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er1_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er1_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er1_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er1_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er1_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er1_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er1_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er1_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er2_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er2_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er2_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er2_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er2_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er2_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er2_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er2_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er3_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er3_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er3_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er3_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er3_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er3_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er3_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er3_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er4_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er4_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er4_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er4_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er4_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er4_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er4_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er4_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er5_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er5_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er5_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er5_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er5_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er5_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er5_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er5_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er6_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er6_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er6_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er6_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er6_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er6_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er6_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er6_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er7_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er7_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er7_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er7_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er7_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er7_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er7_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er7_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er8_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er8_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er8_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er8_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er8_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er8_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er8_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er8_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er9_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er9_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er9_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er9_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er9_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er9_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er9_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er9_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er10_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er10_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er10_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er10_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er10_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er10_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er10_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er10_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er11_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er11_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er11_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er11_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er11_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er11_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er11_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er11_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er12_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er12_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er12_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er12_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er12_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er12_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er12_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er12_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er13_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er13_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er13_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er13_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er13_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er13_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er13_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er13_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er14_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er14_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er14_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er14_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er14_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er14_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er14_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er14_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er15_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er15_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er15_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er15_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er15_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er15_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er15_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er15_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er16_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er16_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er16_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er16_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er16_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er16_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er16_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er16_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er17_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er17_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er17_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er17_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er17_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er17_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er17_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er17_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er18_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er18_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er18_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er18_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er18_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er18_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er18_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er18_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er19_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er19_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er19_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er19_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er19_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er19_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er19_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er19_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er20_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er20_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er20_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er20_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er20_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er20_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er20_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er20_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er21_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er21_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er21_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er21_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er21_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er21_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er21_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er21_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er22_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er22_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er22_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er22_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er22_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er22_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er22_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er22_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er23_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er23_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er23_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er23_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er23_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er23_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er23_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er23_2evalue_2ewords_type.2⟩

private theorem wordsChecks2 (t : Fin 24) :
    program.isBitsB (outVal (2 : Fin 10) t) ((outVal (2 : Fin 10) t - 1)) idx1 = true ∧
    program.privCellB ((outVal (2 : Fin 10) t - 1)) = true ∧ program.valueField (outVal (2 : Fin 10) t) = 1 ∧
    program.valueField ((outVal (2 : Fin 10) t - 1)) = 1 ∧ (program.value (outVal (2 : Fin 10) t)).size = 1600 ∧
    (program.value ((outVal (2 : Fin 10) t - 1))).size = 100 ∧
    (program.value ((outVal (2 : Fin 10) t - 1))).type.nodeName = some "GF(2^16)" := by
  fin_cases t
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er24_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er24_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er24_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er24_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er24_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er24_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er24_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er24_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er25_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er25_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er25_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er25_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er25_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er25_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er25_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er25_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er26_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er26_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er26_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er26_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er26_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er26_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er26_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er26_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er27_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er27_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er27_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er27_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er27_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er27_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er27_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er27_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er28_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er28_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er28_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er28_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er28_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er28_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er28_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er28_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er29_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er29_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er29_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er29_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er29_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er29_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er29_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er29_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er30_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er30_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er30_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er30_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er30_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er30_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er30_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er30_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er31_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er31_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er31_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er31_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er31_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er31_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er31_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er31_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er32_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er32_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er32_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er32_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er32_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er32_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er32_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er32_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er33_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er33_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er33_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er33_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er33_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er33_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er33_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er33_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er34_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er34_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er34_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er34_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er34_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er34_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er34_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er34_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er35_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er35_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er35_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er35_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er35_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er35_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er35_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er35_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er36_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er36_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er36_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er36_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er36_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er36_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er36_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er36_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er37_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er37_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er37_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er37_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er37_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er37_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er37_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er37_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er38_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er38_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er38_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er38_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er38_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er38_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er38_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er38_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er39_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er39_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er39_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er39_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er39_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er39_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er39_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er39_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er40_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er40_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er40_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er40_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er40_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er40_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er40_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er40_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er41_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er41_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er41_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er41_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er41_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er41_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er41_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er41_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er42_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er42_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er42_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er42_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er42_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er42_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er42_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er42_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er43_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er43_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er43_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er43_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er43_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er43_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er43_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er43_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er44_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er44_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er44_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er44_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er44_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er44_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er44_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er44_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er45_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er45_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er45_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er45_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er45_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er45_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er45_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er45_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er46_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er46_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er46_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er46_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er46_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er46_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er46_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er46_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er47_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er47_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er47_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er47_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er47_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er47_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er47_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er47_2evalue_2ewords_type.2⟩

private theorem wordsChecks3 (t : Fin 24) :
    program.isBitsB (outVal (3 : Fin 10) t) ((outVal (3 : Fin 10) t - 1)) idx1 = true ∧
    program.privCellB ((outVal (3 : Fin 10) t - 1)) = true ∧ program.valueField (outVal (3 : Fin 10) t) = 1 ∧
    program.valueField ((outVal (3 : Fin 10) t - 1)) = 1 ∧ (program.value (outVal (3 : Fin 10) t)).size = 1600 ∧
    (program.value ((outVal (3 : Fin 10) t - 1))).size = 100 ∧
    (program.value ((outVal (3 : Fin 10) t - 1))).type.nodeName = some "GF(2^16)" := by
  fin_cases t
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er48_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er48_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er48_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er48_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er48_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er48_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er48_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er48_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er49_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er49_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er49_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er49_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er49_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er49_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er49_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er49_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er50_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er50_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er50_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er50_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er50_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er50_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er50_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er50_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er51_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er51_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er51_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er51_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er51_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er51_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er51_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er51_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er52_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er52_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er52_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er52_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er52_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er52_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er52_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er52_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er53_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er53_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er53_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er53_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er53_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er53_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er53_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er53_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er54_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er54_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er54_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er54_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er54_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er54_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er54_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er54_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er55_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er55_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er55_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er55_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er55_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er55_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er55_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er55_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er56_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er56_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er56_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er56_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er56_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er56_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er56_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er56_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er57_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er57_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er57_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er57_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er57_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er57_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er57_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er57_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er58_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er58_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er58_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er58_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er58_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er58_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er58_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er58_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er59_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er59_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er59_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er59_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er59_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er59_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er59_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er59_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er60_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er60_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er60_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er60_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er60_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er60_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er60_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er60_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er61_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er61_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er61_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er61_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er61_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er61_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er61_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er61_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er62_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er62_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er62_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er62_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er62_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er62_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er62_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er62_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er63_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er63_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er63_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er63_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er63_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er63_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er63_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er63_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er64_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er64_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er64_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er64_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er64_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er64_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er64_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er64_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er65_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er65_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er65_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er65_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er65_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er65_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er65_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er65_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er66_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er66_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er66_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er66_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er66_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er66_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er66_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er66_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er67_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er67_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er67_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er67_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er67_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er67_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er67_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er67_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er68_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er68_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er68_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er68_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er68_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er68_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er68_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er68_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er69_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er69_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er69_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er69_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er69_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er69_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er69_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er69_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er70_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er70_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er70_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er70_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er70_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er70_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er70_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er70_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er71_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er71_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er71_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er71_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er71_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er71_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er71_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er71_2evalue_2ewords_type.2⟩

private theorem wordsChecks4 (t : Fin 24) :
    program.isBitsB (outVal (4 : Fin 10) t) ((outVal (4 : Fin 10) t - 1)) idx1 = true ∧
    program.privCellB ((outVal (4 : Fin 10) t - 1)) = true ∧ program.valueField (outVal (4 : Fin 10) t) = 1 ∧
    program.valueField ((outVal (4 : Fin 10) t - 1)) = 1 ∧ (program.value (outVal (4 : Fin 10) t)).size = 1600 ∧
    (program.value ((outVal (4 : Fin 10) t - 1))).size = 100 ∧
    (program.value ((outVal (4 : Fin 10) t - 1))).type.nodeName = some "GF(2^16)" := by
  fin_cases t
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er72_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er72_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er72_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er72_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er72_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er72_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er72_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er72_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er73_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er73_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er73_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er73_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er73_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er73_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er73_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er73_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er74_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er74_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er74_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er74_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er74_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er74_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er74_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er74_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er75_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er75_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er75_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er75_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er75_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er75_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er75_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er75_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er76_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er76_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er76_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er76_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er76_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er76_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er76_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er76_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er77_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er77_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er77_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er77_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er77_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er77_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er77_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er77_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er78_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er78_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er78_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er78_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er78_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er78_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er78_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er78_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er79_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er79_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er79_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er79_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er79_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er79_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er79_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er79_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er80_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er80_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er80_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er80_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er80_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er80_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er80_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er80_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er81_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er81_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er81_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er81_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er81_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er81_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er81_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er81_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er82_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er82_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er82_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er82_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er82_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er82_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er82_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er82_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er83_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er83_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er83_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er83_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er83_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er83_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er83_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er83_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er84_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er84_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er84_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er84_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er84_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er84_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er84_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er84_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er85_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er85_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er85_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er85_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er85_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er85_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er85_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er85_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er86_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er86_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er86_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er86_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er86_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er86_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er86_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er86_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er87_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er87_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er87_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er87_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er87_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er87_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er87_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er87_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er88_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er88_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er88_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er88_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er88_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er88_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er88_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er88_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er89_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er89_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er89_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er89_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er89_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er89_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er89_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er89_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er90_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er90_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er90_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er90_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er90_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er90_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er90_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er90_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er91_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er91_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er91_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er91_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er91_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er91_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er91_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er91_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er92_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er92_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er92_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er92_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er92_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er92_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er92_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er92_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er93_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er93_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er93_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er93_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er93_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er93_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er93_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er93_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er94_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er94_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er94_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er94_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er94_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er94_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er94_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er94_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er95_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er95_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er95_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er95_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er95_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er95_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er95_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er95_2evalue_2ewords_type.2⟩

private theorem wordsChecks5 (t : Fin 24) :
    program.isBitsB (outVal (5 : Fin 10) t) ((outVal (5 : Fin 10) t - 1)) idx1 = true ∧
    program.privCellB ((outVal (5 : Fin 10) t - 1)) = true ∧ program.valueField (outVal (5 : Fin 10) t) = 1 ∧
    program.valueField ((outVal (5 : Fin 10) t - 1)) = 1 ∧ (program.value (outVal (5 : Fin 10) t)).size = 1600 ∧
    (program.value ((outVal (5 : Fin 10) t - 1))).size = 100 ∧
    (program.value ((outVal (5 : Fin 10) t - 1))).type.nodeName = some "GF(2^16)" := by
  fin_cases t
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er96_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er96_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er96_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er96_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er96_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er96_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er96_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er96_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er97_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er97_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er97_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er97_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er97_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er97_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er97_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er97_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er98_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er98_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er98_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er98_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er98_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er98_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er98_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er98_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er99_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er99_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er99_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er99_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er99_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er99_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er99_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er99_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er100_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er100_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er100_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er100_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er100_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er100_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er100_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er100_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er101_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er101_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er101_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er101_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er101_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er101_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er101_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er101_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er102_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er102_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er102_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er102_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er102_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er102_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er102_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er102_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er103_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er103_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er103_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er103_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er103_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er103_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er103_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er103_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er104_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er104_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er104_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er104_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er104_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er104_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er104_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er104_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er105_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er105_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er105_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er105_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er105_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er105_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er105_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er105_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er106_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er106_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er106_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er106_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er106_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er106_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er106_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er106_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er107_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er107_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er107_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er107_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er107_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er107_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er107_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er107_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er108_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er108_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er108_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er108_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er108_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er108_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er108_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er108_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er109_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er109_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er109_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er109_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er109_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er109_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er109_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er109_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er110_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er110_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er110_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er110_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er110_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er110_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er110_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er110_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er111_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er111_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er111_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er111_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er111_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er111_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er111_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er111_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er112_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er112_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er112_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er112_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er112_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er112_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er112_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er112_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er113_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er113_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er113_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er113_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er113_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er113_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er113_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er113_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er114_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er114_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er114_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er114_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er114_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er114_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er114_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er114_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er115_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er115_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er115_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er115_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er115_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er115_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er115_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er115_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er116_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er116_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er116_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er116_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er116_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er116_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er116_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er116_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er117_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er117_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er117_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er117_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er117_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er117_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er117_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er117_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er118_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er118_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er118_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er118_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er118_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er118_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er118_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er118_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er119_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er119_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er119_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er119_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er119_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er119_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er119_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er119_2evalue_2ewords_type.2⟩

private theorem wordsChecks6 (t : Fin 24) :
    program.isBitsB (outVal (6 : Fin 10) t) ((outVal (6 : Fin 10) t - 1)) idx1 = true ∧
    program.privCellB ((outVal (6 : Fin 10) t - 1)) = true ∧ program.valueField (outVal (6 : Fin 10) t) = 1 ∧
    program.valueField ((outVal (6 : Fin 10) t - 1)) = 1 ∧ (program.value (outVal (6 : Fin 10) t)).size = 1600 ∧
    (program.value ((outVal (6 : Fin 10) t - 1))).size = 100 ∧
    (program.value ((outVal (6 : Fin 10) t - 1))).type.nodeName = some "GF(2^16)" := by
  fin_cases t
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er120_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er120_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er120_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er120_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er120_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er120_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er120_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er120_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er121_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er121_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er121_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er121_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er121_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er121_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er121_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er121_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er122_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er122_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er122_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er122_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er122_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er122_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er122_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er122_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er123_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er123_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er123_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er123_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er123_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er123_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er123_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er123_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er124_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er124_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er124_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er124_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er124_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er124_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er124_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er124_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er125_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er125_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er125_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er125_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er125_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er125_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er125_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er125_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er126_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er126_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er126_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er126_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er126_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er126_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er126_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er126_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er127_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er127_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er127_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er127_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er127_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er127_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er127_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er127_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er128_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er128_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er128_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er128_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er128_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er128_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er128_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er128_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er129_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er129_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er129_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er129_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er129_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er129_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er129_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er129_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er130_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er130_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er130_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er130_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er130_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er130_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er130_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er130_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er131_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er131_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er131_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er131_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er131_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er131_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er131_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er131_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er132_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er132_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er132_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er132_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er132_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er132_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er132_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er132_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er133_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er133_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er133_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er133_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er133_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er133_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er133_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er133_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er134_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er134_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er134_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er134_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er134_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er134_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er134_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er134_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er135_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er135_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er135_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er135_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er135_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er135_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er135_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er135_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er136_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er136_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er136_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er136_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er136_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er136_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er136_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er136_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er137_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er137_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er137_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er137_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er137_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er137_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er137_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er137_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er138_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er138_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er138_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er138_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er138_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er138_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er138_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er138_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er139_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er139_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er139_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er139_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er139_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er139_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er139_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er139_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er140_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er140_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er140_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er140_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er140_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er140_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er140_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er140_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er141_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er141_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er141_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er141_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er141_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er141_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er141_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er141_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er142_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er142_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er142_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er142_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er142_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er142_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er142_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er142_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er143_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er143_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er143_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er143_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er143_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er143_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er143_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er143_2evalue_2ewords_type.2⟩

private theorem wordsChecks7 (t : Fin 24) :
    program.isBitsB (outVal (7 : Fin 10) t) ((outVal (7 : Fin 10) t - 1)) idx1 = true ∧
    program.privCellB ((outVal (7 : Fin 10) t - 1)) = true ∧ program.valueField (outVal (7 : Fin 10) t) = 1 ∧
    program.valueField ((outVal (7 : Fin 10) t - 1)) = 1 ∧ (program.value (outVal (7 : Fin 10) t)).size = 1600 ∧
    (program.value ((outVal (7 : Fin 10) t - 1))).size = 100 ∧
    (program.value ((outVal (7 : Fin 10) t - 1))).type.nodeName = some "GF(2^16)" := by
  fin_cases t
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er144_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er144_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er144_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er144_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er144_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er144_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er144_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er144_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er145_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er145_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er145_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er145_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er145_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er145_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er145_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er145_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er146_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er146_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er146_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er146_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er146_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er146_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er146_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er146_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er147_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er147_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er147_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er147_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er147_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er147_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er147_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er147_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er148_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er148_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er148_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er148_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er148_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er148_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er148_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er148_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er149_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er149_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er149_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er149_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er149_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er149_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er149_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er149_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er150_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er150_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er150_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er150_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er150_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er150_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er150_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er150_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er151_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er151_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er151_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er151_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er151_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er151_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er151_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er151_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er152_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er152_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er152_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er152_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er152_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er152_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er152_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er152_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er153_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er153_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er153_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er153_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er153_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er153_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er153_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er153_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er154_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er154_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er154_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er154_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er154_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er154_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er154_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er154_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er155_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er155_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er155_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er155_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er155_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er155_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er155_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er155_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er156_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er156_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er156_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er156_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er156_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er156_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er156_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er156_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er157_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er157_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er157_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er157_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er157_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er157_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er157_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er157_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er158_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er158_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er158_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er158_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er158_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er158_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er158_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er158_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er159_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er159_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er159_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er159_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er159_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er159_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er159_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er159_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er160_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er160_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er160_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er160_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er160_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er160_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er160_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er160_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er161_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er161_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er161_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er161_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er161_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er161_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er161_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er161_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er162_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er162_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er162_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er162_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er162_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er162_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er162_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er162_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er163_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er163_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er163_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er163_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er163_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er163_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er163_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er163_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er164_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er164_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er164_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er164_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er164_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er164_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er164_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er164_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er165_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er165_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er165_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er165_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er165_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er165_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er165_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er165_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er166_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er166_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er166_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er166_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er166_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er166_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er166_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er166_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2ec_5ftilde_2er167_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2ec_5ftilde_2er167_2evalue_2ewords_header.1 value_h2c_2ec_5ftilde_2er167_2evalue_2ewords_kind,
      valueShape_field value_h2c_2ec_5ftilde_2er167_2evalue_header.2, valueShape_field value_h2c_2ec_5ftilde_2er167_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2ec_5ftilde_2er167_2evalue_header.2, valueShape_size value_h2c_2ec_5ftilde_2er167_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2ec_5ftilde_2er167_2evalue_2ewords_type.2⟩

private theorem wordsChecks8 (t : Fin 24) :
    program.isBitsB (outVal (8 : Fin 10) t) ((outVal (8 : Fin 10) t - 1)) idx1 = true ∧
    program.privCellB ((outVal (8 : Fin 10) t - 1)) = true ∧ program.valueField (outVal (8 : Fin 10) t) = 1 ∧
    program.valueField ((outVal (8 : Fin 10) t - 1)) = 1 ∧ (program.value (outVal (8 : Fin 10) t)).size = 1600 ∧
    (program.value ((outVal (8 : Fin 10) t - 1))).size = 100 ∧
    (program.value ((outVal (8 : Fin 10) t - 1))).type.nodeName = some "GF(2^16)" := by
  fin_cases t
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er0_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er0_2evalue_2ewords_header.1 value_h2c_2esib_2er0_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er0_2evalue_header.2, valueShape_field value_h2c_2esib_2er0_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er0_2evalue_header.2, valueShape_size value_h2c_2esib_2er0_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er0_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er1_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er1_2evalue_2ewords_header.1 value_h2c_2esib_2er1_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er1_2evalue_header.2, valueShape_field value_h2c_2esib_2er1_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er1_2evalue_header.2, valueShape_size value_h2c_2esib_2er1_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er1_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er2_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er2_2evalue_2ewords_header.1 value_h2c_2esib_2er2_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er2_2evalue_header.2, valueShape_field value_h2c_2esib_2er2_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er2_2evalue_header.2, valueShape_size value_h2c_2esib_2er2_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er2_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er3_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er3_2evalue_2ewords_header.1 value_h2c_2esib_2er3_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er3_2evalue_header.2, valueShape_field value_h2c_2esib_2er3_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er3_2evalue_header.2, valueShape_size value_h2c_2esib_2er3_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er3_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er4_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er4_2evalue_2ewords_header.1 value_h2c_2esib_2er4_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er4_2evalue_header.2, valueShape_field value_h2c_2esib_2er4_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er4_2evalue_header.2, valueShape_size value_h2c_2esib_2er4_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er4_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er5_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er5_2evalue_2ewords_header.1 value_h2c_2esib_2er5_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er5_2evalue_header.2, valueShape_field value_h2c_2esib_2er5_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er5_2evalue_header.2, valueShape_size value_h2c_2esib_2er5_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er5_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er6_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er6_2evalue_2ewords_header.1 value_h2c_2esib_2er6_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er6_2evalue_header.2, valueShape_field value_h2c_2esib_2er6_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er6_2evalue_header.2, valueShape_size value_h2c_2esib_2er6_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er6_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er7_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er7_2evalue_2ewords_header.1 value_h2c_2esib_2er7_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er7_2evalue_header.2, valueShape_field value_h2c_2esib_2er7_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er7_2evalue_header.2, valueShape_size value_h2c_2esib_2er7_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er7_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er8_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er8_2evalue_2ewords_header.1 value_h2c_2esib_2er8_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er8_2evalue_header.2, valueShape_field value_h2c_2esib_2er8_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er8_2evalue_header.2, valueShape_size value_h2c_2esib_2er8_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er8_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er9_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er9_2evalue_2ewords_header.1 value_h2c_2esib_2er9_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er9_2evalue_header.2, valueShape_field value_h2c_2esib_2er9_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er9_2evalue_header.2, valueShape_size value_h2c_2esib_2er9_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er9_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er10_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er10_2evalue_2ewords_header.1 value_h2c_2esib_2er10_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er10_2evalue_header.2, valueShape_field value_h2c_2esib_2er10_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er10_2evalue_header.2, valueShape_size value_h2c_2esib_2er10_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er10_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er11_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er11_2evalue_2ewords_header.1 value_h2c_2esib_2er11_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er11_2evalue_header.2, valueShape_field value_h2c_2esib_2er11_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er11_2evalue_header.2, valueShape_size value_h2c_2esib_2er11_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er11_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er12_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er12_2evalue_2ewords_header.1 value_h2c_2esib_2er12_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er12_2evalue_header.2, valueShape_field value_h2c_2esib_2er12_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er12_2evalue_header.2, valueShape_size value_h2c_2esib_2er12_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er12_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er13_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er13_2evalue_2ewords_header.1 value_h2c_2esib_2er13_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er13_2evalue_header.2, valueShape_field value_h2c_2esib_2er13_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er13_2evalue_header.2, valueShape_size value_h2c_2esib_2er13_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er13_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er14_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er14_2evalue_2ewords_header.1 value_h2c_2esib_2er14_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er14_2evalue_header.2, valueShape_field value_h2c_2esib_2er14_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er14_2evalue_header.2, valueShape_size value_h2c_2esib_2er14_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er14_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er15_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er15_2evalue_2ewords_header.1 value_h2c_2esib_2er15_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er15_2evalue_header.2, valueShape_field value_h2c_2esib_2er15_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er15_2evalue_header.2, valueShape_size value_h2c_2esib_2er15_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er15_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er16_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er16_2evalue_2ewords_header.1 value_h2c_2esib_2er16_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er16_2evalue_header.2, valueShape_field value_h2c_2esib_2er16_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er16_2evalue_header.2, valueShape_size value_h2c_2esib_2er16_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er16_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er17_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er17_2evalue_2ewords_header.1 value_h2c_2esib_2er17_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er17_2evalue_header.2, valueShape_field value_h2c_2esib_2er17_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er17_2evalue_header.2, valueShape_size value_h2c_2esib_2er17_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er17_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er18_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er18_2evalue_2ewords_header.1 value_h2c_2esib_2er18_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er18_2evalue_header.2, valueShape_field value_h2c_2esib_2er18_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er18_2evalue_header.2, valueShape_size value_h2c_2esib_2er18_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er18_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er19_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er19_2evalue_2ewords_header.1 value_h2c_2esib_2er19_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er19_2evalue_header.2, valueShape_field value_h2c_2esib_2er19_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er19_2evalue_header.2, valueShape_size value_h2c_2esib_2er19_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er19_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er20_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er20_2evalue_2ewords_header.1 value_h2c_2esib_2er20_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er20_2evalue_header.2, valueShape_field value_h2c_2esib_2er20_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er20_2evalue_header.2, valueShape_size value_h2c_2esib_2er20_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er20_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er21_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er21_2evalue_2ewords_header.1 value_h2c_2esib_2er21_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er21_2evalue_header.2, valueShape_field value_h2c_2esib_2er21_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er21_2evalue_header.2, valueShape_size value_h2c_2esib_2er21_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er21_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er22_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er22_2evalue_2ewords_header.1 value_h2c_2esib_2er22_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er22_2evalue_header.2, valueShape_field value_h2c_2esib_2er22_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er22_2evalue_header.2, valueShape_size value_h2c_2esib_2er22_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er22_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er23_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er23_2evalue_2ewords_header.1 value_h2c_2esib_2er23_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er23_2evalue_header.2, valueShape_field value_h2c_2esib_2er23_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er23_2evalue_header.2, valueShape_size value_h2c_2esib_2er23_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er23_2evalue_2ewords_type.2⟩

private theorem wordsChecks9 (t : Fin 24) :
    program.isBitsB (outVal (9 : Fin 10) t) ((outVal (9 : Fin 10) t - 1)) idx1 = true ∧
    program.privCellB ((outVal (9 : Fin 10) t - 1)) = true ∧ program.valueField (outVal (9 : Fin 10) t) = 1 ∧
    program.valueField ((outVal (9 : Fin 10) t - 1)) = 1 ∧ (program.value (outVal (9 : Fin 10) t)).size = 1600 ∧
    (program.value ((outVal (9 : Fin 10) t - 1))).size = 100 ∧
    (program.value ((outVal (9 : Fin 10) t - 1))).type.nodeName = some "GF(2^16)" := by
  fin_cases t
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er24_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er24_2evalue_2ewords_header.1 value_h2c_2esib_2er24_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er24_2evalue_header.2, valueShape_field value_h2c_2esib_2er24_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er24_2evalue_header.2, valueShape_size value_h2c_2esib_2er24_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er24_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er25_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er25_2evalue_2ewords_header.1 value_h2c_2esib_2er25_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er25_2evalue_header.2, valueShape_field value_h2c_2esib_2er25_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er25_2evalue_header.2, valueShape_size value_h2c_2esib_2er25_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er25_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er26_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er26_2evalue_2ewords_header.1 value_h2c_2esib_2er26_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er26_2evalue_header.2, valueShape_field value_h2c_2esib_2er26_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er26_2evalue_header.2, valueShape_size value_h2c_2esib_2er26_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er26_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er27_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er27_2evalue_2ewords_header.1 value_h2c_2esib_2er27_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er27_2evalue_header.2, valueShape_field value_h2c_2esib_2er27_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er27_2evalue_header.2, valueShape_size value_h2c_2esib_2er27_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er27_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er28_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er28_2evalue_2ewords_header.1 value_h2c_2esib_2er28_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er28_2evalue_header.2, valueShape_field value_h2c_2esib_2er28_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er28_2evalue_header.2, valueShape_size value_h2c_2esib_2er28_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er28_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er29_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er29_2evalue_2ewords_header.1 value_h2c_2esib_2er29_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er29_2evalue_header.2, valueShape_field value_h2c_2esib_2er29_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er29_2evalue_header.2, valueShape_size value_h2c_2esib_2er29_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er29_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er30_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er30_2evalue_2ewords_header.1 value_h2c_2esib_2er30_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er30_2evalue_header.2, valueShape_field value_h2c_2esib_2er30_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er30_2evalue_header.2, valueShape_size value_h2c_2esib_2er30_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er30_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er31_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er31_2evalue_2ewords_header.1 value_h2c_2esib_2er31_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er31_2evalue_header.2, valueShape_field value_h2c_2esib_2er31_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er31_2evalue_header.2, valueShape_size value_h2c_2esib_2er31_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er31_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er32_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er32_2evalue_2ewords_header.1 value_h2c_2esib_2er32_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er32_2evalue_header.2, valueShape_field value_h2c_2esib_2er32_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er32_2evalue_header.2, valueShape_size value_h2c_2esib_2er32_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er32_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er33_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er33_2evalue_2ewords_header.1 value_h2c_2esib_2er33_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er33_2evalue_header.2, valueShape_field value_h2c_2esib_2er33_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er33_2evalue_header.2, valueShape_size value_h2c_2esib_2er33_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er33_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er34_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er34_2evalue_2ewords_header.1 value_h2c_2esib_2er34_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er34_2evalue_header.2, valueShape_field value_h2c_2esib_2er34_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er34_2evalue_header.2, valueShape_size value_h2c_2esib_2er34_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er34_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er35_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er35_2evalue_2ewords_header.1 value_h2c_2esib_2er35_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er35_2evalue_header.2, valueShape_field value_h2c_2esib_2er35_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er35_2evalue_header.2, valueShape_size value_h2c_2esib_2er35_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er35_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er36_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er36_2evalue_2ewords_header.1 value_h2c_2esib_2er36_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er36_2evalue_header.2, valueShape_field value_h2c_2esib_2er36_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er36_2evalue_header.2, valueShape_size value_h2c_2esib_2er36_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er36_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er37_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er37_2evalue_2ewords_header.1 value_h2c_2esib_2er37_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er37_2evalue_header.2, valueShape_field value_h2c_2esib_2er37_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er37_2evalue_header.2, valueShape_size value_h2c_2esib_2er37_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er37_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er38_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er38_2evalue_2ewords_header.1 value_h2c_2esib_2er38_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er38_2evalue_header.2, valueShape_field value_h2c_2esib_2er38_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er38_2evalue_header.2, valueShape_size value_h2c_2esib_2er38_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er38_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er39_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er39_2evalue_2ewords_header.1 value_h2c_2esib_2er39_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er39_2evalue_header.2, valueShape_field value_h2c_2esib_2er39_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er39_2evalue_header.2, valueShape_size value_h2c_2esib_2er39_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er39_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er40_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er40_2evalue_2ewords_header.1 value_h2c_2esib_2er40_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er40_2evalue_header.2, valueShape_field value_h2c_2esib_2er40_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er40_2evalue_header.2, valueShape_size value_h2c_2esib_2er40_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er40_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er41_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er41_2evalue_2ewords_header.1 value_h2c_2esib_2er41_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er41_2evalue_header.2, valueShape_field value_h2c_2esib_2er41_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er41_2evalue_header.2, valueShape_size value_h2c_2esib_2er41_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er41_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er42_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er42_2evalue_2ewords_header.1 value_h2c_2esib_2er42_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er42_2evalue_header.2, valueShape_field value_h2c_2esib_2er42_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er42_2evalue_header.2, valueShape_size value_h2c_2esib_2er42_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er42_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er43_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er43_2evalue_2ewords_header.1 value_h2c_2esib_2er43_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er43_2evalue_header.2, valueShape_field value_h2c_2esib_2er43_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er43_2evalue_header.2, valueShape_size value_h2c_2esib_2er43_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er43_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er44_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er44_2evalue_2ewords_header.1 value_h2c_2esib_2er44_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er44_2evalue_header.2, valueShape_field value_h2c_2esib_2er44_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er44_2evalue_header.2, valueShape_size value_h2c_2esib_2er44_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er44_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er45_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er45_2evalue_2ewords_header.1 value_h2c_2esib_2er45_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er45_2evalue_header.2, valueShape_field value_h2c_2esib_2er45_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er45_2evalue_header.2, valueShape_size value_h2c_2esib_2er45_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er45_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er46_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er46_2evalue_2ewords_header.1 value_h2c_2esib_2er46_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er46_2evalue_header.2, valueShape_field value_h2c_2esib_2er46_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er46_2evalue_header.2, valueShape_size value_h2c_2esib_2er46_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er46_2evalue_2ewords_type.2⟩
  · exact ⟨isBitsB_of_kind value_h2c_2esib_2er47_2evalue_kind,
      checked.wellFormed.privCellB_of_kind_priv value_h2c_2esib_2er47_2evalue_2ewords_header.1 value_h2c_2esib_2er47_2evalue_2ewords_kind,
      valueShape_field value_h2c_2esib_2er47_2evalue_header.2, valueShape_field value_h2c_2esib_2er47_2evalue_2ewords_header.2,
      valueShape_size value_h2c_2esib_2er47_2evalue_header.2, valueShape_size value_h2c_2esib_2er47_2evalue_2ewords_header.2,
      valueType_nodeName value_h2c_2esib_2er47_2evalue_2ewords_type.2⟩

/-- The 240 round outputs are bit views of committed words of the stated field, size, and type. -/
theorem wordsChecks : ∀ p : Fin 10, ∀ t : Fin 24,
    program.isBitsB (outVal p t) ((outVal p t - 1)) idx1 = true ∧
    program.privCellB ((outVal p t - 1)) = true ∧ program.valueField (outVal p t) = 1 ∧
    program.valueField ((outVal p t - 1)) = 1 ∧ (program.value (outVal p t)).size = 1600 ∧
    (program.value ((outVal p t - 1))).size = 100 ∧
    (program.value ((outVal p t - 1))).type.nodeName = some "GF(2^16)" := by
  intro p t
  fin_cases p
  · exact wordsChecks0 t
  · exact wordsChecks1 t
  · exact wordsChecks2 t
  · exact wordsChecks3 t
  · exact wordsChecks4 t
  · exact wordsChecks5 t
  · exact wordsChecks6 t
  · exact wordsChecks7 t
  · exact wordsChecks8 t
  · exact wordsChecks9 t

/-- The identity word map has its stated length and entries. -/
private theorem idx0_entry : IndexMap.size idx0 = 384 ∧ ∀ i < 384, idx0.entry i = i := by
  rw [GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.idx0_eq]
  rw [IndexMap.ofSegs_eq]
  refine ⟨rfl, ?_⟩
  intro i hi
  change IndexMap.entry [(0, 1, 384)] i = i
  simpa only [Nat.zero_add] using (IndexMap.entry_step_one (s := 0) hi)

/-- The identity word map has its stated length and entries. -/
theorem idx1_entry : IndexMap.size idx1 = 100 ∧ ∀ i < 100, idx1.entry i = i := by
  rw [GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.idx1_eq]
  rw [IndexMap.ofSegs_eq]
  refine ⟨rfl, ?_⟩
  intro i hi
  change IndexMap.entry [(0, 1, 100)] i = i
  simpa only [Nat.zero_add] using (IndexMap.entry_step_one (s := 0) hi)

/-- The identity word map has its stated length and entries. -/
private theorem idx2_entry : IndexMap.size idx2 = 32 ∧ ∀ i < 32, idx2.entry i = i := by
  rw [GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.idx2_eq]
  rw [IndexMap.ofSegs_eq]
  refine ⟨rfl, ?_⟩
  intro i hi
  change IndexMap.entry [(0, 1, 32)] i = i
  simpa only [Nat.zero_add] using (IndexMap.entry_step_one (s := 0) hi)

/-- The identity word map has its stated length and entries. -/
private theorem idx5_entry : IndexMap.size idx5 = 99 ∧ ∀ i < 99, idx5.entry i = i := by
  rw [GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.idx5_eq]
  rw [IndexMap.ofSegs_eq]
  refine ⟨rfl, ?_⟩
  intro i hi
  change IndexMap.entry [(0, 1, 99)] i = i
  simpa only [Nat.zero_add] using (IndexMap.entry_step_one (s := 0) hi)

/-- The named bit view and its committed word input have the checked metadata. -/
theorem view121 : program.isBitsB 120 119 idx2 = true ∧ program.privCellB 119 = true ∧
    program.valueField 120 = 1 ∧ program.valueField 119 = 1 ∧ (program.value 120).size = 512 ∧
    (program.value 119).size = 32 ∧ (program.value 119).type.nodeName = some "GF(2^16)" ∧
    RealizedProgram.IndexMap.size idx2 = 32 ∧ ∀ i < 32, idx2.entry i = i :=
  ⟨isBitsB_of_kind value_h2c_2emu_2eout_kind,
    checked.wellFormed.privCellB_of_kind_priv value_h2c_2emu_2eout_2ewords_header.1 value_h2c_2emu_2eout_2ewords_kind,
    valueShape_field value_h2c_2emu_2eout_header.2,
    valueShape_field value_h2c_2emu_2eout_2ewords_header.2,
    valueShape_size value_h2c_2emu_2eout_header.2,
    valueShape_size value_h2c_2emu_2eout_2ewords_header.2,
    valueType_nodeName value_h2c_2emu_2eout_2ewords_type.2,
    idx2_entry⟩

/-- The named bit view and its committed word input have the checked metadata. -/
theorem view71 : program.isBitsB 70 69 idx0 = true ∧ program.privCellB 69 = true ∧
    program.valueField 70 = 1 ∧ program.valueField 69 = 1 ∧ (program.value 70).size = 6144 ∧
    (program.value 69).size = 384 ∧ (program.value 69).type.nodeName = some "GF(2^16)" ∧
    RealizedProgram.IndexMap.size idx0 = 384 ∧ ∀ i < 384, idx0.entry i = i :=
  ⟨isBitsB_of_kind value_w1_kind,
    checked.wellFormed.privCellB_of_kind_priv value_w1_2ewords_header.1 value_w1_2ewords_kind,
    valueShape_field value_w1_header.2,
    valueShape_field value_w1_2ewords_header.2,
    valueShape_size value_w1_header.2,
    valueShape_size value_w1_2ewords_header.2,
    valueType_nodeName value_w1_2ewords_type.2,
    idx0_entry⟩

/-- The message buffer and flags are checked private cells of the hash field. -/
theorem priv6869 : program.privCellB 67 = true ∧ program.valueField 67 = 1 ∧
    program.privCellB 68 = true ∧ program.valueField 68 = 1 :=
  ⟨checked.wellFormed.privCellB_of_kind_priv value_msg_header.1 value_msg_kind,
    valueShape_field value_msg_header.2,
    checked.wellFormed.privCellB_of_kind_priv value_msg_2ein_5fmessage_header.1 value_msg_2ein_5fmessage_kind,
    valueShape_field value_msg_2ein_5fmessage_header.2⟩

/-- The selection cells and threshold view follow from checked named facts. -/
theorem sel_cells : program.isBitsB 558 557 idx5 = true ∧ program.privCellB 557 = true ∧
    program.valueField 558 = 1 ∧ program.valueField 557 = 1 ∧ (program.value 558).size = 1584 ∧
    (program.value 557).size = 99 ∧ (program.value 557).type.nodeName = some "GF(2^16)" ∧
    RealizedProgram.IndexMap.size idx5 = 99 ∧ (∀ i < 99, idx5.entry i = i) ∧ program.privCellB 556 = true ∧
    program.valueField 556 = 1 ∧ (program.value 556).size = 312 :=
  ⟨isBitsB_of_kind value_h2c_2esample_2eselect_2ethreshold_kind,
    checked.wellFormed.privCellB_of_kind_priv value_h2c_2esample_2eselect_2ethreshold_2ewords_header.1 value_h2c_2esample_2eselect_2ethreshold_2ewords_kind,
    valueShape_field value_h2c_2esample_2eselect_2ethreshold_header.2,
    valueShape_field value_h2c_2esample_2eselect_2ethreshold_2ewords_header.2,
    valueShape_size value_h2c_2esample_2eselect_2ethreshold_header.2,
    valueShape_size value_h2c_2esample_2eselect_2ethreshold_2ewords_header.2,
    valueType_nodeName value_h2c_2esample_2eselect_2ethreshold_2ewords_type.2,
    idx5_entry.1,
    idx5_entry.2,
    checked.wellFormed.privCellB_of_kind_priv value_h2c_2esample_2eselect_2ej_header.1 value_h2c_2esample_2eselect_2ej_kind,
    valueShape_field value_h2c_2esample_2eselect_2ej_header.2,
    valueShape_size value_h2c_2esample_2eselect_2ej_header.2⟩

/-- The six named memory-shuffle cells have their checked fields and sizes. -/
theorem mem_cells : (∀ v ∈ [560, 561, 562, 563, 564, 565], program.privCellB v = true ∧
    program.valueField v = 1) ∧ (program.value 560).size = 39 ∧ (program.value 561).size = 234 ∧
    (program.value 562).size = 256 ∧ (program.value 563).size = 256 ∧
    (program.value 564).size = 39 ∧ (program.value 565).size = 39 := by
  refine ⟨?_, valueShape_size value_h2c_2esample_2emem_2eread_5fvalue_header.2, valueShape_size value_h2c_2esample_2emem_2eread_5forigin_header.2, valueShape_size value_h2c_2esample_2emem_2ec_5fenc_header.2, valueShape_size value_h2c_2esample_2emem_2efinal_5forigin_header.2, valueShape_size value_h2c_2esample_2emem_2eunit_header.2, valueShape_size value_h2c_2esample_2emem_2eorigin_header.2⟩
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨checked.wellFormed.privCellB_of_kind_priv value_h2c_2esample_2emem_2eread_5fvalue_header.1 value_h2c_2esample_2emem_2eread_5fvalue_kind, valueShape_field value_h2c_2esample_2emem_2eread_5fvalue_header.2⟩
  · exact ⟨checked.wellFormed.privCellB_of_kind_priv value_h2c_2esample_2emem_2eread_5forigin_header.1 value_h2c_2esample_2emem_2eread_5forigin_kind, valueShape_field value_h2c_2esample_2emem_2eread_5forigin_header.2⟩
  · exact ⟨checked.wellFormed.privCellB_of_kind_priv value_h2c_2esample_2emem_2ec_5fenc_header.1 value_h2c_2esample_2emem_2ec_5fenc_kind, valueShape_field value_h2c_2esample_2emem_2ec_5fenc_header.2⟩
  · exact ⟨checked.wellFormed.privCellB_of_kind_priv value_h2c_2esample_2emem_2efinal_5forigin_header.1 value_h2c_2esample_2emem_2efinal_5forigin_kind, valueShape_field value_h2c_2esample_2emem_2efinal_5forigin_header.2⟩
  · exact ⟨checked.wellFormed.privCellB_of_kind_priv value_h2c_2esample_2emem_2eunit_header.1 value_h2c_2esample_2emem_2eunit_kind, valueShape_field value_h2c_2esample_2emem_2eunit_header.2⟩
  · exact ⟨checked.wellFormed.privCellB_of_kind_priv value_h2c_2esample_2emem_2eorigin_header.1 value_h2c_2esample_2emem_2eorigin_kind, valueShape_field value_h2c_2esample_2emem_2eorigin_header.2⟩

end GordieHowe.MLDSA44.Native.ROMParams.HonestWordFacts
