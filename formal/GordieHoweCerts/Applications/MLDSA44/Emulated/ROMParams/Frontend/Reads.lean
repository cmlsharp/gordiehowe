-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.MLDSA44.Emulated.ROMParams.Certified
public import GordieHoweCerts.Generated.MLDSA44.Emulated.ROMParams.ShapeFacts
public import GordieHowe.Language.RealizedProgram.ShapeReads

public section

/-!
# Reads of the realized program of `MLDSA44.Emulated.ROMParams`

One rewrite per part of a value or predicate the frontend reads, each from a checked shape fact.
`shape_decide` rewrites a goal over the program with them and decides the closed goal that is left,
which reads no program table.
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams.Reads

open RealizedProgram
open Generated.MLDSA44.Emulated.ROMParams
open Generated.MLDSA44.Emulated.ROMParams.Program (program)
open ShapeFacts

@[shape_reads] theorem lt0 : 0 < program.values.length :=
  value_hint_2ew1_5fbound_2eshape_2eleft_2eargument1_2efirst_header.1

@[shape_reads] theorem size0 : (program.value 0).size = 6 :=
  valueShape_size value_hint_2ew1_5fbound_2eshape_2eleft_2eargument1_2efirst_header.2

@[shape_reads] theorem field0 : program.valueField 0 = 0 :=
  valueShape_field value_hint_2ew1_5fbound_2eshape_2eleft_2eargument1_2efirst_header.2

@[shape_reads] theorem ts0 : (program.value 0).typeSource = .none :=
  valueShape_typeSource value_hint_2ew1_5fbound_2eshape_2eleft_2eargument1_2efirst_header.2

@[shape_reads] theorem src0 : program.IsSourceValue 0 :=
  valueShape_role value_hint_2ew1_5fbound_2eshape_2eleft_2eargument1_2efirst_header.2

@[shape_reads] theorem type0 : (program.value 0).type = .field :=
  value_hint_2ew1_5fbound_2eshape_2eleft_2eargument1_2efirst_type.2

@[shape_reads] theorem lt1 : 1 < program.values.length :=
  value_hint_2ew1_5fbound_2eshape_2eright_header.1

@[shape_reads] theorem size1 : (program.value 1).size = 1024 :=
  valueShape_size value_hint_2ew1_5fbound_2eshape_2eright_header.2

@[shape_reads] theorem field1 : program.valueField 1 = 0 :=
  valueShape_field value_hint_2ew1_5fbound_2eshape_2eright_header.2

@[shape_reads] theorem ts1 : (program.value 1).typeSource = .none :=
  valueShape_typeSource value_hint_2ew1_5fbound_2eshape_2eright_header.2

@[shape_reads] theorem src1 : program.IsSourceValue 1 :=
  valueShape_role value_hint_2ew1_5fbound_2eshape_2eright_header.2

@[shape_reads] theorem type1 : (program.value 1).type = .field :=
  value_hint_2ew1_5fbound_2eshape_2eright_type.2

@[shape_reads] theorem lt2 : 2 < program.values.length :=
  value_hint_2einterval_2eshape_2eright_2efirst_2eshared_2efirst_2esecond_2eshared_2eargument1_2efirst_header.1

@[shape_reads] theorem size2 : (program.value 2).size = 6 :=
  valueShape_size value_hint_2einterval_2eshape_2eright_2efirst_2eshared_2efirst_2esecond_2eshared_2eargument1_2efirst_header.2

@[shape_reads] theorem field2 : program.valueField 2 = 0 :=
  valueShape_field value_hint_2einterval_2eshape_2eright_2efirst_2eshared_2efirst_2esecond_2eshared_2eargument1_2efirst_header.2

@[shape_reads] theorem ts2 : (program.value 2).typeSource = .none :=
  valueShape_typeSource value_hint_2einterval_2eshape_2eright_2efirst_2eshared_2efirst_2esecond_2eshared_2eargument1_2efirst_header.2

@[shape_reads] theorem src2 : program.IsSourceValue 2 :=
  valueShape_role value_hint_2einterval_2eshape_2eright_2efirst_2eshared_2efirst_2esecond_2eshared_2eargument1_2efirst_header.2

@[shape_reads] theorem type2 : (program.value 2).type = .field :=
  value_hint_2einterval_2eshape_2eright_2efirst_2eshared_2efirst_2esecond_2eshared_2eargument1_2efirst_type.2

@[shape_reads] theorem lt3 : 3 < program.values.length :=
  value_hint_2edecompose_2eshape_2eleft_2efirst_2eshared_2efirst_2esecond_2efirst_2efirst_2esecond_2efirst_header.1

@[shape_reads] theorem size3 : (program.value 3).size = 1 :=
  valueShape_size value_hint_2edecompose_2eshape_2eleft_2efirst_2eshared_2efirst_2esecond_2efirst_2efirst_2esecond_2efirst_header.2

@[shape_reads] theorem field3 : program.valueField 3 = 0 :=
  valueShape_field value_hint_2edecompose_2eshape_2eleft_2efirst_2eshared_2efirst_2esecond_2efirst_2efirst_2esecond_2efirst_header.2

@[shape_reads] theorem ts3 : (program.value 3).typeSource = .none :=
  valueShape_typeSource value_hint_2edecompose_2eshape_2eleft_2efirst_2eshared_2efirst_2esecond_2efirst_2efirst_2esecond_2efirst_header.2

@[shape_reads] theorem src3 : program.IsSourceValue 3 :=
  valueShape_role value_hint_2edecompose_2eshape_2eleft_2efirst_2eshared_2efirst_2esecond_2efirst_2efirst_2esecond_2efirst_header.2

@[shape_reads] theorem type3 : (program.value 3).type = .field :=
  value_hint_2edecompose_2eshape_2eleft_2efirst_2eshared_2efirst_2esecond_2efirst_2efirst_2esecond_2efirst_type.2

@[shape_reads] theorem lt4 : 4 < program.values.length :=
  value_hint_2edecompose_2eshape_2eleft_2esecond_2esecond_2efirst_header.1

@[shape_reads] theorem size4 : (program.value 4).size = 1 :=
  valueShape_size value_hint_2edecompose_2eshape_2eleft_2esecond_2esecond_2efirst_header.2

@[shape_reads] theorem field4 : program.valueField 4 = 0 :=
  valueShape_field value_hint_2edecompose_2eshape_2eleft_2esecond_2esecond_2efirst_header.2

@[shape_reads] theorem ts4 : (program.value 4).typeSource = .none :=
  valueShape_typeSource value_hint_2edecompose_2eshape_2eleft_2esecond_2esecond_2efirst_header.2

@[shape_reads] theorem src4 : program.IsSourceValue 4 :=
  valueShape_role value_hint_2edecompose_2eshape_2eleft_2esecond_2esecond_2efirst_header.2

@[shape_reads] theorem type4 : (program.value 4).type = .field :=
  value_hint_2edecompose_2eshape_2eleft_2esecond_2esecond_2efirst_type.2

@[shape_reads] theorem lt5 : 5 < program.values.length :=
  value_hint_2edecompose_2eshape_2eright_header.1

@[shape_reads] theorem size5 : (program.value 5).size = 1024 :=
  valueShape_size value_hint_2edecompose_2eshape_2eright_header.2

@[shape_reads] theorem field5 : program.valueField 5 = 0 :=
  valueShape_field value_hint_2edecompose_2eshape_2eright_header.2

@[shape_reads] theorem ts5 : (program.value 5).typeSource = .none :=
  valueShape_typeSource value_hint_2edecompose_2eshape_2eright_header.2

@[shape_reads] theorem src5 : program.IsSourceValue 5 :=
  valueShape_role value_hint_2edecompose_2eshape_2eright_header.2

@[shape_reads] theorem type5 : (program.value 5).type = .field :=
  value_hint_2edecompose_2eshape_2eright_type.2

@[shape_reads] theorem lt6 : 6 < program.values.length :=
  value_hint_2einterval_2eshape_2eright_2esecond_2efirst_header.1

@[shape_reads] theorem size6 : (program.value 6).size = 1 :=
  valueShape_size value_hint_2einterval_2eshape_2eright_2esecond_2efirst_header.2

@[shape_reads] theorem field6 : program.valueField 6 = 0 :=
  valueShape_field value_hint_2einterval_2eshape_2eright_2esecond_2efirst_header.2

@[shape_reads] theorem ts6 : (program.value 6).typeSource = .none :=
  valueShape_typeSource value_hint_2einterval_2eshape_2eright_2esecond_2efirst_header.2

@[shape_reads] theorem src6 : program.IsSourceValue 6 :=
  valueShape_role value_hint_2einterval_2eshape_2eright_2esecond_2efirst_header.2

@[shape_reads] theorem type6 : (program.value 6).type = .field :=
  value_hint_2einterval_2eshape_2eright_2esecond_2efirst_type.2

@[shape_reads] theorem lt56 : 56 < program.values.length :=
  value_key_2ea_header.1

@[shape_reads] theorem size56 : (program.value 56).size = 4096 :=
  valueShape_size value_key_2ea_header.2

@[shape_reads] theorem field56 : program.valueField 56 = 0 :=
  valueShape_field value_key_2ea_header.2

@[shape_reads] theorem ts56 : (program.value 56).typeSource = .none :=
  valueShape_typeSource value_key_2ea_header.2

@[shape_reads] theorem src56 : program.IsSourceValue 56 :=
  valueShape_role value_key_2ea_header.2

@[shape_reads] theorem type56 : (program.value 56).type = .sub "GF(p^1)" :=
  value_key_2ea_type.2

@[shape_reads] theorem lt57 : 57 < program.values.length :=
  value_key_2et1_header.1

@[shape_reads] theorem size57 : (program.value 57).size = 1024 :=
  valueShape_size value_key_2et1_header.2

@[shape_reads] theorem field57 : program.valueField 57 = 0 :=
  valueShape_field value_key_2et1_header.2

@[shape_reads] theorem ts57 : (program.value 57).typeSource = .none :=
  valueShape_typeSource value_key_2et1_header.2

@[shape_reads] theorem src57 : program.IsSourceValue 57 :=
  valueShape_role value_key_2et1_header.2

@[shape_reads] theorem type57 : (program.value 57).type = .sub "GF(p^1)" :=
  value_key_2et1_type.2

@[shape_reads] theorem lt58 : 58 < program.values.length :=
  value_z_header.1

@[shape_reads] theorem size58 : (program.value 58).size = 1024 :=
  valueShape_size value_z_header.2

@[shape_reads] theorem field58 : program.valueField 58 = 0 :=
  valueShape_field value_z_header.2

@[shape_reads] theorem ts58 : (program.value 58).typeSource = .none :=
  valueShape_typeSource value_z_header.2

@[shape_reads] theorem src58 : program.IsSourceValue 58 :=
  valueShape_role value_z_header.2

@[shape_reads] theorem type58 : (program.value 58).type = .sub "GF(p^1)" :=
  value_z_type.2

@[shape_reads] theorem lt59 : 59 < program.values.length :=
  value_h_header.1

@[shape_reads] theorem size59 : (program.value 59).size = 1024 :=
  valueShape_size value_h_header.2

@[shape_reads] theorem field59 : program.valueField 59 = 0 :=
  valueShape_field value_h_header.2

@[shape_reads] theorem ts59 : (program.value 59).typeSource = .pred 6 :=
  valueShape_typeSource value_h_header.2

@[shape_reads] theorem src59 : program.IsSourceValue 59 :=
  valueShape_role value_h_header.2

@[shape_reads] theorem type59 : (program.value 59).type = .bit :=
  value_h_type.2

@[shape_reads] theorem lt60 : 60 < program.values.length :=
  value_challenge_2ec_header.1

@[shape_reads] theorem size60 : (program.value 60).size = 512 :=
  valueShape_size value_challenge_2ec_header.2

@[shape_reads] theorem field60 : program.valueField 60 = 0 :=
  valueShape_field value_challenge_2ec_header.2

@[shape_reads] theorem ts60 : (program.value 60).typeSource = .pred 7 :=
  valueShape_typeSource value_challenge_2ec_header.2

@[shape_reads] theorem src60 : program.IsSourceValue 60 :=
  valueShape_role value_challenge_2ec_header.2

@[shape_reads] theorem type60 : (program.value 60).type = .bit :=
  value_challenge_2ec_type.2

@[shape_reads] theorem lt61 : 61 < program.values.length :=
  value_signature_2ew_header.1

@[shape_reads] theorem size61 : (program.value 61).size = 1024 :=
  valueShape_size value_signature_2ew_header.2

@[shape_reads] theorem field61 : program.valueField 61 = 0 :=
  valueShape_field value_signature_2ew_header.2

@[shape_reads] theorem ts61 : (program.value 61).typeSource = .none :=
  valueShape_typeSource value_signature_2ew_header.2

@[shape_reads] theorem src61 : program.IsSourceValue 61 :=
  valueShape_role value_signature_2ew_header.2

@[shape_reads] theorem type61 : (program.value 61).type = .sub "GF(p^1)" :=
  value_signature_2ew_type.2

@[shape_reads] theorem lt62 : 62 < program.values.length :=
  value_norm_2ez_2eoffset_header.1

@[shape_reads] theorem size62 : (program.value 62).size = 1024 :=
  valueShape_size value_norm_2ez_2eoffset_header.2

@[shape_reads] theorem field62 : program.valueField 62 = 0 :=
  valueShape_field value_norm_2ez_2eoffset_header.2

@[shape_reads] theorem ts62 : (program.value 62).typeSource = .none :=
  valueShape_typeSource value_norm_2ez_2eoffset_header.2

@[shape_reads] theorem src62 : program.IsSourceValue 62 :=
  valueShape_role value_norm_2ez_2eoffset_header.2

@[shape_reads] theorem type62 : (program.value 62).type = .field :=
  value_norm_2ez_2eoffset_type.2

@[shape_reads] theorem lt63 : 63 < program.values.length :=
  value_hint_2ew1_header.1

@[shape_reads] theorem size63 : (program.value 63).size = 6144 :=
  valueShape_size value_hint_2ew1_header.2

@[shape_reads] theorem field63 : program.valueField 63 = 0 :=
  valueShape_field value_hint_2ew1_header.2

@[shape_reads] theorem ts63 : (program.value 63).typeSource = .pred 8 :=
  valueShape_typeSource value_hint_2ew1_header.2

@[shape_reads] theorem src63 : program.IsSourceValue 63 :=
  valueShape_role value_hint_2ew1_header.2

@[shape_reads] theorem type63 : (program.value 63).type = .bit :=
  value_hint_2ew1_type.2

@[shape_reads] theorem lt64 : 64 < program.values.length :=
  value_hint_2enonpositive_header.1

@[shape_reads] theorem size64 : (program.value 64).size = 1024 :=
  valueShape_size value_hint_2enonpositive_header.2

@[shape_reads] theorem field64 : program.valueField 64 = 0 :=
  valueShape_field value_hint_2enonpositive_header.2

@[shape_reads] theorem ts64 : (program.value 64).typeSource = .pred 9 :=
  valueShape_typeSource value_hint_2enonpositive_header.2

@[shape_reads] theorem src64 : program.IsSourceValue 64 :=
  valueShape_role value_hint_2enonpositive_header.2

@[shape_reads] theorem type64 : (program.value 64).type = .bit :=
  value_hint_2enonpositive_type.2

@[shape_reads] theorem lt65 : 65 < program.values.length :=
  value_hint_2eoffset_header.1

@[shape_reads] theorem size65 : (program.value 65).size = 1024 :=
  valueShape_size value_hint_2eoffset_header.2

@[shape_reads] theorem field65 : program.valueField 65 = 0 :=
  valueShape_field value_hint_2eoffset_header.2

@[shape_reads] theorem ts65 : (program.value 65).typeSource = .none :=
  valueShape_typeSource value_hint_2eoffset_header.2

@[shape_reads] theorem src65 : program.IsSourceValue 65 :=
  valueShape_role value_hint_2eoffset_header.2

@[shape_reads] theorem type65 : (program.value 65).type = .sub "GF(p^1)" :=
  value_hint_2eoffset_type.2

@[shape_reads] theorem lt66 : 66 < program.values.length :=
  value_hint_2eslack_header.1

@[shape_reads] theorem size66 : (program.value 66).size = 1024 :=
  valueShape_size value_hint_2eslack_header.2

@[shape_reads] theorem field66 : program.valueField 66 = 0 :=
  valueShape_field value_hint_2eslack_header.2

@[shape_reads] theorem ts66 : (program.value 66).typeSource = .none :=
  valueShape_typeSource value_hint_2eslack_header.2

@[shape_reads] theorem src66 : program.IsSourceValue 66 :=
  valueShape_role value_hint_2eslack_header.2

@[shape_reads] theorem type66 : (program.value 66).type = .sub "GF(p^1)" :=
  value_hint_2eslack_type.2

@[shape_reads] theorem lt67 : 67 < program.values.length :=
  value_tr_header.1

@[shape_reads] theorem size67 : (program.value 67).size = 512 :=
  valueShape_size value_tr_header.2

@[shape_reads] theorem field67 : program.valueField 67 = 1 :=
  valueShape_field value_tr_header.2

@[shape_reads] theorem ts67 : (program.value 67).typeSource = .none :=
  valueShape_typeSource value_tr_header.2

@[shape_reads] theorem src67 : program.IsSourceValue 67 :=
  valueShape_role value_tr_header.2

@[shape_reads] theorem type67 : (program.value 67).type = .bit :=
  value_tr_type.2

@[shape_reads] theorem lt68 : 68 < program.values.length :=
  value_msg_header.1

@[shape_reads] theorem size68 : (program.value 68).size = 560 :=
  valueShape_size value_msg_header.2

@[shape_reads] theorem field68 : program.valueField 68 = 1 :=
  valueShape_field value_msg_header.2

@[shape_reads] theorem ts68 : (program.value 68).typeSource = .node :=
  valueShape_typeSource value_msg_header.2

@[shape_reads] theorem src68 : program.IsSourceValue 68 :=
  valueShape_role value_msg_header.2

@[shape_reads] theorem type68 : (program.value 68).type = .bit :=
  value_msg_type.2

@[shape_reads] theorem lt69 : 69 < program.values.length :=
  value_msg_2ein_5fmessage_header.1

@[shape_reads] theorem size69 : (program.value 69).size = 136 :=
  valueShape_size value_msg_2ein_5fmessage_header.2

@[shape_reads] theorem field69 : program.valueField 69 = 1 :=
  valueShape_field value_msg_2ein_5fmessage_header.2

@[shape_reads] theorem ts69 : (program.value 69).typeSource = .node :=
  valueShape_typeSource value_msg_2ein_5fmessage_header.2

@[shape_reads] theorem src69 : program.IsSourceValue 69 :=
  valueShape_role value_msg_2ein_5fmessage_header.2

@[shape_reads] theorem type69 : (program.value 69).type = .bit :=
  value_msg_2ein_5fmessage_type.2

@[shape_reads] theorem lt457 : 457 < program.values.length :=
  value_h2c_2ec_5ftilde_2er167_2evalue_header.1

@[shape_reads] theorem size457 : (program.value 457).size = 1600 :=
  valueShape_size value_h2c_2ec_5ftilde_2er167_2evalue_header.2

@[shape_reads] theorem field457 : program.valueField 457 = 1 :=
  valueShape_field value_h2c_2ec_5ftilde_2er167_2evalue_header.2

@[shape_reads] theorem ts457 : (program.value 457).typeSource = .node :=
  valueShape_typeSource value_h2c_2ec_5ftilde_2er167_2evalue_header.2

@[shape_reads] theorem src457 : program.IsSourceValue 457 :=
  valueShape_role value_h2c_2ec_5ftilde_2er167_2evalue_header.2

@[shape_reads] theorem type457 : (program.value 457).type = .bit :=
  value_h2c_2ec_5ftilde_2er167_2evalue_type.2

@[shape_reads] theorem lt557 : 557 < program.values.length :=
  value_h2c_2esample_2eselect_2ej_header.1

@[shape_reads] theorem size557 : (program.value 557).size = 312 :=
  valueShape_size value_h2c_2esample_2eselect_2ej_header.2

@[shape_reads] theorem field557 : program.valueField 557 = 1 :=
  valueShape_field value_h2c_2esample_2eselect_2ej_header.2

@[shape_reads] theorem ts557 : (program.value 557).typeSource = .node :=
  valueShape_typeSource value_h2c_2esample_2eselect_2ej_header.2

@[shape_reads] theorem src557 : program.IsSourceValue 557 :=
  valueShape_role value_h2c_2esample_2eselect_2ej_header.2

@[shape_reads] theorem type557 : (program.value 557).type = .bit :=
  value_h2c_2esample_2eselect_2ej_type.2

@[shape_reads] theorem lt559 : 559 < program.values.length :=
  value_h2c_2esample_2eselect_2ethreshold_header.1

@[shape_reads] theorem size559 : (program.value 559).size = 1584 :=
  valueShape_size value_h2c_2esample_2eselect_2ethreshold_header.2

@[shape_reads] theorem field559 : program.valueField 559 = 1 :=
  valueShape_field value_h2c_2esample_2eselect_2ethreshold_header.2

@[shape_reads] theorem ts559 : (program.value 559).typeSource = .node :=
  valueShape_typeSource value_h2c_2esample_2eselect_2ethreshold_header.2

@[shape_reads] theorem src559 : program.IsSourceValue 559 :=
  valueShape_role value_h2c_2esample_2eselect_2ethreshold_header.2

@[shape_reads] theorem type559 : (program.value 559).type = .bit :=
  value_h2c_2esample_2eselect_2ethreshold_type.2

@[shape_reads] theorem lt561 : 561 < program.values.length :=
  value_h2c_2esample_2emem_2eread_5fvalue_header.1

@[shape_reads] theorem size561 : (program.value 561).size = 39 :=
  valueShape_size value_h2c_2esample_2emem_2eread_5fvalue_header.2

@[shape_reads] theorem field561 : program.valueField 561 = 1 :=
  valueShape_field value_h2c_2esample_2emem_2eread_5fvalue_header.2

@[shape_reads] theorem ts561 : (program.value 561).typeSource = .node :=
  valueShape_typeSource value_h2c_2esample_2emem_2eread_5fvalue_header.2

@[shape_reads] theorem src561 : program.IsSourceValue 561 :=
  valueShape_role value_h2c_2esample_2emem_2eread_5fvalue_header.2

@[shape_reads] theorem type561 : (program.value 561).type = .sub "GF(2^16)" :=
  value_h2c_2esample_2emem_2eread_5fvalue_type.2

@[shape_reads] theorem lt562 : 562 < program.values.length :=
  value_h2c_2esample_2emem_2eread_5forigin_header.1

@[shape_reads] theorem size562 : (program.value 562).size = 234 :=
  valueShape_size value_h2c_2esample_2emem_2eread_5forigin_header.2

@[shape_reads] theorem field562 : program.valueField 562 = 1 :=
  valueShape_field value_h2c_2esample_2emem_2eread_5forigin_header.2

@[shape_reads] theorem ts562 : (program.value 562).typeSource = .node :=
  valueShape_typeSource value_h2c_2esample_2emem_2eread_5forigin_header.2

@[shape_reads] theorem src562 : program.IsSourceValue 562 :=
  valueShape_role value_h2c_2esample_2emem_2eread_5forigin_header.2

@[shape_reads] theorem type562 : (program.value 562).type = .bit :=
  value_h2c_2esample_2emem_2eread_5forigin_type.2

@[shape_reads] theorem lt563 : 563 < program.values.length :=
  value_h2c_2esample_2emem_2ec_5fenc_header.1

@[shape_reads] theorem size563 : (program.value 563).size = 256 :=
  valueShape_size value_h2c_2esample_2emem_2ec_5fenc_header.2

@[shape_reads] theorem field563 : program.valueField 563 = 1 :=
  valueShape_field value_h2c_2esample_2emem_2ec_5fenc_header.2

@[shape_reads] theorem ts563 : (program.value 563).typeSource = .node :=
  valueShape_typeSource value_h2c_2esample_2emem_2ec_5fenc_header.2

@[shape_reads] theorem src563 : program.IsSourceValue 563 :=
  valueShape_role value_h2c_2esample_2emem_2ec_5fenc_header.2

@[shape_reads] theorem type563 : (program.value 563).type = .sub "GF(2^16)" :=
  value_h2c_2esample_2emem_2ec_5fenc_type.2

@[shape_reads] theorem lt564 : 564 < program.values.length :=
  value_h2c_2esample_2emem_2efinal_5forigin_header.1

@[shape_reads] theorem size564 : (program.value 564).size = 256 :=
  valueShape_size value_h2c_2esample_2emem_2efinal_5forigin_header.2

@[shape_reads] theorem field564 : program.valueField 564 = 1 :=
  valueShape_field value_h2c_2esample_2emem_2efinal_5forigin_header.2

@[shape_reads] theorem ts564 : (program.value 564).typeSource = .node :=
  valueShape_typeSource value_h2c_2esample_2emem_2efinal_5forigin_header.2

@[shape_reads] theorem src564 : program.IsSourceValue 564 :=
  valueShape_role value_h2c_2esample_2emem_2efinal_5forigin_header.2

@[shape_reads] theorem type564 : (program.value 564).type = .sub "GF(2^16)" :=
  value_h2c_2esample_2emem_2efinal_5forigin_type.2

@[shape_reads] theorem lt565 : 565 < program.values.length :=
  value_h2c_2esample_2emem_2eunit_header.1

@[shape_reads] theorem size565 : (program.value 565).size = 39 :=
  valueShape_size value_h2c_2esample_2emem_2eunit_header.2

@[shape_reads] theorem field565 : program.valueField 565 = 1 :=
  valueShape_field value_h2c_2esample_2emem_2eunit_header.2

@[shape_reads] theorem ts565 : (program.value 565).typeSource = .node :=
  valueShape_typeSource value_h2c_2esample_2emem_2eunit_header.2

@[shape_reads] theorem src565 : program.IsSourceValue 565 :=
  valueShape_role value_h2c_2esample_2emem_2eunit_header.2

@[shape_reads] theorem type565 : (program.value 565).type = .sub "GF(2^16)" :=
  value_h2c_2esample_2emem_2eunit_type.2

@[shape_reads] theorem lt566 : 566 < program.values.length :=
  value_h2c_2esample_2emem_2eorigin_header.1

@[shape_reads] theorem size566 : (program.value 566).size = 39 :=
  valueShape_size value_h2c_2esample_2emem_2eorigin_header.2

@[shape_reads] theorem field566 : program.valueField 566 = 1 :=
  valueShape_field value_h2c_2esample_2emem_2eorigin_header.2

@[shape_reads] theorem ts566 : (program.value 566).typeSource = .node :=
  valueShape_typeSource value_h2c_2esample_2emem_2eorigin_header.2

@[shape_reads] theorem src566 : program.IsSourceValue 566 :=
  valueShape_role value_h2c_2esample_2emem_2eorigin_header.2

@[shape_reads] theorem type566 : (program.value 566).type = .sub "GF(2^16)" :=
  value_h2c_2esample_2emem_2eorigin_type.2

@[shape_reads] theorem plt0 : 0 < program.predicates.length :=
  predicate_hint_2ew1_5fbound_role.1

@[shape_reads] theorem psrc0 : program.inSource (program.predicate 0) = true :=
  program.inSource_of_source predicate_hint_2ew1_5fbound_role.2

@[shape_reads] theorem plt1 : 1 < program.predicates.length :=
  predicate_hint_2edecompose_role.1

@[shape_reads] theorem psrc1 : program.inSource (program.predicate 1) = true :=
  program.inSource_of_source predicate_hint_2edecompose_role.2

@[shape_reads] theorem plt2 : 2 < program.predicates.length :=
  predicate_hint_2einterval_role.1

@[shape_reads] theorem psrc2 : program.inSource (program.predicate 2) = true :=
  program.inSource_of_source predicate_hint_2einterval_role.2

@[shape_reads] theorem plt3 : 3 < program.predicates.length :=
  predicate_mac_2eA_role.1

@[shape_reads] theorem psrc3 : program.inSource (program.predicate 3) = false :=
  program.inSource_of_realization predicate_mac_2eA_role.2

@[shape_reads] theorem plt4 : 4 < program.predicates.length :=
  predicate_signature_2erelation_2erealized_role.1

@[shape_reads] theorem psrc4 : program.inSource (program.predicate 4) = false :=
  program.inSource_of_realization predicate_signature_2erelation_2erealized_role.2

@[shape_reads] theorem plt5 : 5 < program.predicates.length :=
  predicate_range_2enorm_2ez_2etop_role.1

@[shape_reads] theorem psrc5 : program.inSource (program.predicate 5) = false :=
  program.inSource_of_realization predicate_range_2enorm_2ez_2etop_role.2

@[shape_reads] theorem plt6 : 6 < program.predicates.length :=
  predicate_h_2eboolean_role.1

@[shape_reads] theorem psrc6 : program.inSource (program.predicate 6) = true :=
  program.inSource_of_type predicate_h_2eboolean_role.2 (valueShape_role value_h_header.2)

@[shape_reads] theorem bool6 : (program.predicate 6).body.boolCheck? = some ⟨0, 59⟩ :=
  by
    obtain ⟨t, ht⟩ := predicate_h_2eboolean_body
    rw [ht]
    simp [PredBody.boolCheck?]

@[shape_reads] theorem plt7 : 7 < program.predicates.length :=
  predicate_challenge_2ec_2eboolean_role.1

@[shape_reads] theorem psrc7 : program.inSource (program.predicate 7) = true :=
  program.inSource_of_type predicate_challenge_2ec_2eboolean_role.2 (valueShape_role value_challenge_2ec_header.2)

@[shape_reads] theorem bool7 : (program.predicate 7).body.boolCheck? = some ⟨0, 60⟩ :=
  by
    obtain ⟨t, ht⟩ := predicate_challenge_2ec_2eboolean_body
    rw [ht]
    simp [PredBody.boolCheck?]

@[shape_reads] theorem plt8 : 8 < program.predicates.length :=
  predicate_hint_2ew1_2eboolean_role.1

@[shape_reads] theorem psrc8 : program.inSource (program.predicate 8) = true :=
  program.inSource_of_type predicate_hint_2ew1_2eboolean_role.2 (valueShape_role value_hint_2ew1_header.2)

@[shape_reads] theorem bool8 : (program.predicate 8).body.boolCheck? = some ⟨0, 63⟩ :=
  by
    obtain ⟨t, ht⟩ := predicate_hint_2ew1_2eboolean_body
    rw [ht]
    simp [PredBody.boolCheck?]

@[shape_reads] theorem plt9 : 9 < program.predicates.length :=
  predicate_hint_2enonpositive_2eboolean_role.1

@[shape_reads] theorem psrc9 : program.inSource (program.predicate 9) = true :=
  program.inSource_of_type predicate_hint_2enonpositive_2eboolean_role.2 (valueShape_role value_hint_2enonpositive_header.2)

@[shape_reads] theorem bool9 : (program.predicate 9).body.boolCheck? = some ⟨0, 64⟩ :=
  by
    obtain ⟨t, ht⟩ := predicate_hint_2enonpositive_2eboolean_body
    rw [ht]
    simp [PredBody.boolCheck?]

@[shape_reads] theorem plt10 : 10 < program.predicates.length :=
  predicate_mac_2eblind_2eboolean_role.1

@[shape_reads] theorem psrc10 : program.inSource (program.predicate 10) = false :=
  program.inSource_of_type_realization predicate_mac_2eblind_2eboolean_role.2 (valueShape_role value_mac_2eblind_header.2)

@[shape_reads] theorem bool10 : (program.predicate 10).body.boolCheck? = some ⟨0, 568⟩ :=
  by
    obtain ⟨t, ht⟩ := predicate_mac_2eblind_2eboolean_body
    rw [ht]
    simp [PredBody.boolCheck?]

@[shape_reads] theorem plt11 : 11 < program.predicates.length :=
  predicate_signature_2ew_role.1

@[shape_reads] theorem psrc11 : program.inSource (program.predicate 11) = true :=
  program.inSource_of_source predicate_signature_2ew_role.2

@[shape_reads] theorem plt12 : 12 < program.predicates.length :=
  predicate_norm_2ez_role.1

@[shape_reads] theorem psrc12 : program.inSource (program.predicate 12) = true :=
  program.inSource_of_source predicate_norm_2ez_role.2

@[shape_reads] theorem plt13 : 13 < program.predicates.length :=
  predicate_hint_2eoffset_role.1

@[shape_reads] theorem psrc13 : program.inSource (program.predicate 13) = true :=
  program.inSource_of_source predicate_hint_2eoffset_role.2

@[shape_reads] theorem plt14 : 14 < program.predicates.length :=
  predicate_hint_2eslack_role.1

@[shape_reads] theorem psrc14 : program.inSource (program.predicate 14) = true :=
  program.inSource_of_source predicate_hint_2eslack_role.2

@[shape_reads] theorem plt15 : 15 < program.predicates.length :=
  predicate_hint_5fweight_2eweight_role.1

@[shape_reads] theorem psrc15 : program.inSource (program.predicate 15) = true :=
  program.inSource_of_source predicate_hint_5fweight_2eweight_role.2

@[shape_reads] theorem plt16 : 16 < program.predicates.length :=
  predicate_mac_2elow_role.1

@[shape_reads] theorem psrc16 : program.inSource (program.predicate 16) = false :=
  program.inSource_of_realization predicate_mac_2elow_role.2

@[shape_reads] theorem plt17 : 17 < program.predicates.length :=
  predicate_mac_2ehigh_role.1

@[shape_reads] theorem psrc17 : program.inSource (program.predicate 17) = false :=
  program.inSource_of_realization predicate_mac_2ehigh_role.2

@[shape_reads] theorem plt18 : 18 < program.predicates.length :=
  predicate_mac_2enowrap_role.1

@[shape_reads] theorem psrc18 : program.inSource (program.predicate 18) = false :=
  program.inSource_of_realization predicate_mac_2enowrap_role.2

@[shape_reads] theorem plt19 : 19 < program.predicates.length :=
  predicate_signature_2erelation_2eq_role.1

@[shape_reads] theorem psrc19 : program.inSource (program.predicate 19) = false :=
  program.inSource_of_realization predicate_signature_2erelation_2eq_role.2

@[shape_reads] theorem plt273 : 273 < program.predicates.length :=
  predicate_mac_role.1

@[shape_reads] theorem psrc273 : program.inSource (program.predicate 273) = false :=
  program.inSource_of_realization predicate_mac_role.2

@[shape_reads] theorem plt274 : 274 < program.predicates.length :=
  predicate_signature_2erelation_2esource_role.1

@[shape_reads] theorem psrc274 : program.inSource (program.predicate 274) = true :=
  program.inSource_of_source predicate_signature_2erelation_2esource_role.2

@[shape_reads] theorem plt275 : 275 < program.predicates.length :=
  predicate_mac_2eequal_role.1

@[shape_reads] theorem psrc275 : program.inSource (program.predicate 275) = true :=
  program.inSource_of_source predicate_mac_2eequal_role.2

@[shape_reads] theorem elt0 : 0 < program.exprs.length :=
  expr_lt_of_ne_default (by rw [expr_hint_2einterval_2eshape_2eright_2efirst_2eshared_2esecond_2eshared_2efirst_eq]; decide)

@[shape_reads] theorem elt1 : 1 < program.exprs.length :=
  expr_lt_of_ne_default (by rw [expr_hint_2edecompose_2eshape_2eleft_2efirst_2eshared_2efirst_2efirst_2esecond_2efirst_2efirst_2efirst_2efirst_2esecond_2efirst_eq]; decide)

@[shape_reads] theorem elt2 : 2 < program.exprs.length :=
  expr_lt_of_ne_default (by rw [expr_hint_2einterval_2eshape_2eright_2efirst_2eshared_2efirst_2esecond_eq]; decide)

@[shape_reads] theorem elt3 : 3 < program.exprs.length :=
  expr_lt_of_ne_default (by rw [expr_hint_2einterval_2eshape_2eright_2efirst_2eshared_2esecond_eq]; decide)

@[shape_reads] theorem elt4 : 4 < program.exprs.length :=
  expr_lt_of_ne_default (by rw [expr_hint_2einterval_2eshape_2eright_2efirst_eq]; decide)

@[shape_reads] theorem elt5 : 5 < program.exprs.length :=
  expr_lt_of_ne_default (by rw [expr_hint_2edecompose_2eshape_2eleft_2efirst_eq]; decide)

@[shape_reads] theorem elt6 : 6 < program.exprs.length :=
  expr_lt_of_ne_default (by rw [expr_mac_2eequal_2eshape_2eright_eq]; decide)

@[shape_reads] theorem elt7 : 7 < program.exprs.length :=
  expr_lt_of_ne_default (by rw [expr_signature_2erelation_2eshape_2eleft_2efirst_2esecond_2efirst_2efirst_eq]; decide)

@[shape_reads] theorem elt8 : 8 < program.exprs.length :=
  expr_lt_of_ne_default (by rw [expr_signature_2erelation_2eshape_2eleft_2esecond_2efirst_2efirst_eq]; decide)

@[shape_reads] theorem elt527 : 527 < program.exprs.length :=
  expr_lt_of_ne_default (by rw [expr_mac_2eequal_2eshape_2eleft_eq]; decide)

@[shape_reads] theorem domainField0 : program.domainField 0 = 0 :=
  Generated.MLDSA44.Emulated.ROMParams.conditions.fieldTable.domainField_eq 0 (by decide)

@[shape_reads] theorem domainField1 : program.domainField 1 = 1 :=
  Generated.MLDSA44.Emulated.ROMParams.conditions.fieldTable.domainField_eq 1 (by decide)

@[shape_reads] theorem exprs_len : program.exprs.length = 528 :=
  exprs_length

@[shape_reads] theorem chalField0 : program.chalField 0 = 1 :=
  challenge_h2c_2esample_2eselect_2edelta_full.2.2.1

@[shape_reads] theorem chalField1 : program.chalField 1 = 1 :=
  challenge_h2c_2esample_2emem_2edelta_full.2.2.1

@[shape_reads] theorem chalSize0 : (program.challenge 0).size = 1 :=
  challenge_h2c_2esample_2eselect_2edelta_full.2.2.2

@[shape_reads] theorem chalSize1 : (program.challenge 1).size = 1 :=
  challenge_h2c_2esample_2emem_2edelta_full.2.2.2

@[shape_reads] theorem chalSampler0 : (program.challenge 0).sampler = .full :=
  challenge_h2c_2esample_2eselect_2edelta_full.2.1

@[shape_reads] theorem chalSampler1 : (program.challenge 1).sampler = .full :=
  challenge_h2c_2esample_2emem_2edelta_full.2.1

@[shape_reads] theorem phases : program.phases = 2 :=
  phases_count

@[shape_reads] theorem predicates_len : program.predicates.length = 276 :=
  predicates_length

@[shape_reads] theorem lenRef527 : program.exprLen (.ref 527) = 6656 :=
  by
    rw [exprLen_ref Generated.MLDSA44.Emulated.ROMParams.conditions.wellFormed.refsOrdered elt527, expr_mac_2eequal_2eshape_2eleft_eq]
    shape_decide

@[shape_reads] theorem lenRef5 : program.exprLen (.ref 5) = 1024 :=
  by
    rw [exprLen_ref Generated.MLDSA44.Emulated.ROMParams.conditions.wellFormed.refsOrdered elt5, expr_hint_2edecompose_2eshape_2eleft_2efirst_eq]
    shape_decide

@[shape_reads] theorem lenRef6 : program.exprLen (.ref 6) = 6656 :=
  by
    rw [exprLen_ref Generated.MLDSA44.Emulated.ROMParams.conditions.wellFormed.refsOrdered elt6, expr_mac_2eequal_2eshape_2eright_eq]
    shape_decide

attribute [shape_reads] value_hint_2ew1_5fbound_2eshape_2eleft_2eargument1_2efirst_kind
attribute [shape_reads] value_hint_2ew1_5fbound_2eshape_2eright_kind
attribute [shape_reads] value_hint_2einterval_2eshape_2eright_2efirst_2eshared_2efirst_2esecond_2eshared_2eargument1_2efirst_kind
attribute [shape_reads] value_hint_2edecompose_2eshape_2eleft_2efirst_2eshared_2efirst_2esecond_2efirst_2efirst_2esecond_2efirst_kind
attribute [shape_reads] value_hint_2edecompose_2eshape_2eleft_2esecond_2esecond_2efirst_kind
attribute [shape_reads] value_hint_2edecompose_2eshape_2eright_kind
attribute [shape_reads] value_hint_2einterval_2eshape_2eright_2esecond_2efirst_kind
attribute [shape_reads] value_key_2ea_kind
attribute [shape_reads] value_key_2et1_kind
attribute [shape_reads] value_z_kind
attribute [shape_reads] value_h_kind
attribute [shape_reads] value_challenge_2ec_kind
attribute [shape_reads] value_signature_2ew_kind
attribute [shape_reads] value_norm_2ez_2eoffset_kind
attribute [shape_reads] value_hint_2ew1_kind
attribute [shape_reads] value_hint_2enonpositive_kind
attribute [shape_reads] value_hint_2eoffset_kind
attribute [shape_reads] value_hint_2eslack_kind
attribute [shape_reads] value_tr_kind
attribute [shape_reads] value_msg_kind
attribute [shape_reads] value_msg_2ein_5fmessage_kind
attribute [shape_reads] value_h2c_2ec_5ftilde_2er167_2evalue_kind
attribute [shape_reads] value_h2c_2esample_2eselect_2ej_kind
attribute [shape_reads] value_h2c_2esample_2eselect_2ethreshold_kind
attribute [shape_reads] value_h2c_2esample_2emem_2eread_5fvalue_kind
attribute [shape_reads] value_h2c_2esample_2emem_2eread_5forigin_kind
attribute [shape_reads] value_h2c_2esample_2emem_2ec_5fenc_kind
attribute [shape_reads] value_h2c_2esample_2emem_2efinal_5forigin_kind
attribute [shape_reads] value_h2c_2esample_2emem_2eunit_kind
attribute [shape_reads] value_h2c_2esample_2emem_2eorigin_kind

end GordieHowe.MLDSA44.Emulated.ROMParams.Reads
