-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.SelectionCheck
public import GordieHowe.Applications.Falcon512.Ring.Frontend.Basic
public import GordieHowe.Applications.Falcon512.Ring.Honest
public import GordieHoweCerts.Generated.Falcon512.Ring.Native.QROMParams.Structure
public import GordieHoweCerts.Generated.Falcon512.Ring.Native.QROMParams.SourceRoleFacts
public import GordieHowe.Language.RealizedProgram.MemberValues
public import GordieHowe.Language.Honest.SourceRoles
public import GordieHoweCerts.Generated.Falcon512.Ring.Native.QROMParams.ShapeFacts
public import GordieHoweCerts.Generated.Falcon512.Ring.Native.QROMParams.Certified
public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.ProofSystem.Program.FieldProofSystem
public import GordieHowe.Language.RealizedProgram.Placement

public section

/-!
# GordieHowe frontend: the program facts of `Falcon512.Ring.Native.QROMParams`

The native Falcon ring frontend's program facts (the table's selection `GordieHowe.Falcon512.Ring.FalconRingPowers`,
`GordieHowe.Falcon512.Ring.FalconRingSelect`, `GordieHowe.Falcon512.Ring.FalconRingBase`) and the generic norm's
(`GordieHowe.Falcon512.Norm.FalconNorm`) for `GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Program.program`
through the generated shape facts for value kinds, predicate bodies and shared expressions,
and domain `A`'s field `F_q^20` (`GordieHowe.Falcon512.AField`).
-/

namespace GordieHowe.Falcon512.Ring.Native.QROMParams

open Generated.Falcon512.Ring.Native.QROMParams.Program
open Generated.Falcon512.Ring.Native.QROMParams (interp)
open Norm Ring RealizedProgram
open Generated.Falcon512.Ring.Native.QROMParams.ShapeFacts


/-- Domain zero has the field recorded by the checked field table. -/
theorem domainField0_checked : program.domainField 0 = 0 :=
  Generated.Falcon512.Ring.Native.QROMParams.conditions.fieldTable.domainField_eq 0 (by decide)

@[expose] instance : AField (interp 0) := inferInstanceAs (AField RealizedProgram.fq20)

/-- **The table's selection** (`member.signer`): the program check's certificate
(`GordieHowe.RealizedProgram.TableSelect.ofSelections` at `Generated.Falcon512.Ring.Native.QROMParams.selections`): the
record `key.spectrum`, the rows `statement.ring`, the natural-order transform of length `512`. -/
@[expose] instance : FalconRingPowers program where
  toTableSelect := TableSelect.ofSelections (ir := program) (cs := Generated.Falcon512.Ring.Native.QROMParams.selections)
    Generated.Falcon512.Ring.Native.QROMParams.core.wellFormed
    Generated.Falcon512.Ring.Native.QROMParams.checked.selections ⟨0, by decide⟩

/-- The selection's identifiers. -/
instance : FalconRingSelect program := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩⟩

set_option maxRecDepth 4096 in
theorem ring_member : ∃ t, (program.predicate 0).body = .equal 0 (.add (.apply (.sum 512)
    (.mul (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.leaf 6))) (.reindex [(0, 1, 512)] (.leaf 20))))
    (.scale (.const 12288) (.mux (.reindex [(5, 0, 1)] (.leaf 7)) (.reindex [(1, 0, 1)] (.ref 20))
      (.reindex [(0, 0, 1)] (.ref 20))))) (.leaf 1) t := predicate_member_2esigner_body

set_option maxRecDepth 4096 in
theorem ring_sig : ∃ t, (program.predicate 1).body = .equal 0 (.add (.apply (.ntt 512 10302 .natural)
    (.add (.leaf 5) (.scale (.const 12288) (.leaf 10)))) (.scale (.const 12288)
      (.mul (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.leaf 6)))
        (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.apply (.ntt 512 10302 .natural)
          (.leaf 9))))))) (.leaf 2) t := predicate_signature_2eequation_body

set_option maxRecDepth 4096 in
theorem ring_idxBool :
    ∃ t, (program.predicate 14).body = .equal 0 (.mul (.leaf 7) (.leaf 7)) (.leaf 7) t := predicate_member_2esigner_2eindex_2eboolean_body

set_option maxRecDepth 4096 in
/-- The membership's facts: the ring `4`, the spectrum `6`, the powers `20`, the zero constant `1`,
`ψ = 10302`, `−1 = 12288`, the index bits' check `14`. -/
@[expose] instance : FalconRingMember program where
  ring := 4
  spec := 6
  pow := 20
  zero := 1
  psi := 10302
  mOne := 12288
  idxPred := 14
  chal := 5
  s2 := 9
  domainField0 := domainField0_checked
  member := ring_member
  idxBool := ring_idxBool
  inSource := by
    intro q hq
    change q ∈ [0, 14] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨predicate_member_2esigner_role.1, program.inSource_of_source predicate_member_2esigner_role.2⟩
    · exact ⟨predicate_member_2esigner_2eindex_2eboolean_role.1, program.inSource_of_type predicate_member_2esigner_2eindex_2eboolean_role.2 (RealizedProgram.valueShape_role value_member_2esigner_2eindex_header.2)⟩
  consts := by
    exact ⟨RealizedProgram.isConstant_of_kind value_member_2ezero_kind,
      by change (program.constEntries 1).getD 0 0 = 0; rw [RealizedProgram.constEntries_of_kind value_member_2ezero_kind]; rfl⟩
  table := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ringKind := value_statement_2ering_kind
  chalKind := value_statement_2ec_kind
  chal_ne_ring := by decide
  fields := by
    intro v hv
    change v ∈ [0, 1, 4, 6, 7, 8, 20, 21, 5, 9] at hv
    change program.valueField v = 0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact RealizedProgram.valueShape_field value_member_2eone_header.2
    · exact RealizedProgram.valueShape_field value_member_2ezero_header.2
    · exact RealizedProgram.valueShape_field value_statement_2ering_header.2
    · exact RealizedProgram.valueShape_field value_key_2espectrum_header.2
    · exact RealizedProgram.valueShape_field value_member_2esigner_2eindex_header.2
    · exact RealizedProgram.valueShape_field value_member_2ering_2egamma_header.2
    · exact RealizedProgram.valueShape_field value_member_2ering_2epowers_header.2
    · exact RealizedProgram.valueShape_field value_member_2ering_2edigests_header.2
    · exact RealizedProgram.valueShape_field value_statement_2ec_header.2
    · exact RealizedProgram.valueShape_field value_s2_header.2
  sizes := ⟨RealizedProgram.valueShape_size value_member_2esigner_2eindex_header.2, RealizedProgram.valueShape_size value_key_2espectrum_header.2, RealizedProgram.valueShape_size value_statement_2ering_header.2, RealizedProgram.valueShape_size value_statement_2ec_header.2, RealizedProgram.valueShape_size value_s2_header.2⟩
  chal0 := ⟨challenge_member_2ering_2egamma_full.2.2.2,
    challenge_member_2ering_2egamma_full.2.1, challenge_member_2ering_2egamma_full.2.2.1⟩
  isSourceChal_iff := fun j => by
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed,
      source_challenges, List.mem_singleton]
  values_length := value_member_2eone_header.1
  privKinds := ⟨value_key_2espectrum_kind, value_member_2esigner_2eindex_kind, value_s2_kind⟩

set_option maxRecDepth 4096 in
/-- The native ring's facts outside the membership. -/
instance : FalconRingBase program where
  ids := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  sig := ring_sig
  inSource1 := ⟨predicate_signature_2eequation_role.1, program.inSource_of_source predicate_signature_2eequation_role.2⟩
  const2 := ⟨isConstant_of_kind value_signature_2ezero_kind, by rw [constEntries_of_kind value_signature_2ezero_kind]; rfl⟩
  chalKind := value_statement_2ec_kind
  fields := by
    intro v hv
    change v ∈ [2, 5, 9, 10] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact valueShape_field value_signature_2ezero_header.2
    · exact valueShape_field value_statement_2ec_header.2
    · exact valueShape_field value_s2_header.2
    · exact valueShape_field value_signature_2es1_header.2
  sizes := ⟨valueShape_size value_s2_header.2, valueShape_size value_signature_2es1_header.2, valueShape_size value_statement_2ec_header.2⟩
  values_length := value_signature_2es1_header.1
  primeVals := by
    intro v hv
    change v ∈ [9, 10] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨valueShape_role value_s2_header.2, valueShape_typeSource value_s2_header.2, value_s2_type.2⟩
    · exact ⟨valueShape_role value_signature_2es1_header.2, valueShape_typeSource value_signature_2es1_header.2, value_signature_2es1_type.2⟩
  privKinds := ⟨value_s2_kind, value_signature_2es1_kind⟩

set_option maxRecDepth 4096 in
theorem norm_center : ∃ t, (program.predicate 2).body = .equal 0 (.add (.mul (.ref 21) (.ref 21))
    (.scale (.const 12288) (.mul (.add (.add (.ref 22) (.scale (.const 64) (.ref 23)))
      (.scale (.const 4096) (.ref 24))) (.add (.add (.ref 22) (.scale (.const 64) (.ref 23)))
        (.scale (.const 4096) (.ref 24)))))) (.leaf 3) t := predicate_norm_2ecenter_body
set_option maxRecDepth 4096 in
theorem norm_top : ∃ t, (program.predicate 3).body = .equal 0 (.ref 25) (.leaf 1) t := predicate_norm_2etop_body
set_option maxRecDepth 4096 in
theorem norm_col0 : ∃ real, (program.predicate 4).body = .mod 0 0 (.mul (.ref 26) (.ref 26))
    (.add (.ref 27) (.scale (.const 64) (.ref 28))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn0_body
  exact ⟨real, h⟩
set_option maxRecDepth 4096 in
theorem norm_col1 : ∃ real, (program.predicate 5).body = .mod 0 0
    (.add (.scale (.const 2) (.mul (.ref 26) (.ref 29))) (.ref 30))
    (.add (.ref 31) (.scale (.const 64) (.ref 32))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn1_body
  exact ⟨real, h⟩
set_option maxRecDepth 4096 in
theorem norm_col2 : ∃ real, (program.predicate 6).body = .mod 0 0
    (.add (.add (.scale (.const 2) (.mul (.ref 26) (.ref 33))) (.mul (.ref 29) (.ref 29)))
      (.ref 34)) (.add (.ref 35) (.scale (.const 64) (.ref 36))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn2_body
  exact ⟨real, h⟩
set_option maxRecDepth 4096 in
theorem norm_col3 : ∃ real, (program.predicate 7).body = .mod 0 0
    (.add (.scale (.const 2) (.mul (.ref 29) (.ref 33))) (.ref 37))
    (.add (.ref 38) (.scale (.const 64) (.ref 39))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn3_body
  exact ⟨real, h⟩
set_option maxRecDepth 4096 in
theorem norm_col4 : ∃ real, (program.predicate 8).body = .mod 0 0
    (.add (.mul (.ref 33) (.ref 33)) (.ref 40)) (.add (.ref 41) (.scale (.const 64) (.ref 42)))
    real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn4_body
  exact ⟨real, h⟩
set_option maxRecDepth 4096 in
theorem norm_col5 : ∃ real, (program.predicate 9).body = .mod 0 0 (.ref 43) (.ref 44) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn5_body
  exact ⟨real, h⟩
set_option maxRecDepth 4096 in
theorem norm_normalize : ∃ real, (program.predicate 10).body = .mod 0 0
    (.add (.add (.ref 45) (.apply (.batched 102 (.sum 63)) (.ref 46))) (.ref 47))
    (.add (.leaf 14) (.scale (.const 64) (.ref 48))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2enormalize_body
  exact ⟨real, h⟩
set_option maxRecDepth 4096 in
theorem norm_complement : ∃ real, (program.predicate 11).body = .mod 0 0
    (.add (.add (.ref 49) (.leaf 16)) (.ref 50)) (.add (.leaf 18) (.scale (.const 64) (.leaf 17)))
    real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecomplement_body
  exact ⟨real, h⟩
set_option maxRecDepth 4096 in
theorem norm_dcBool : ∃ t, (program.predicate 15).body =
    .equal 0 (.mul (.leaf 17) (.leaf 17)) (.leaf 17) t := predicate_norm_2eDc_2eboolean_body
set_option maxRecDepth 4096 in
theorem norm_encB : ∃ t, (program.predicate 16).body =
    .equal 0 (.mul (.ref 54) (.ref 54)) (.ref 54) t := predicate_enc_2eb_2eboolean_body
set_option maxRecDepth 4096 in
theorem norm_rangeA : ∃ real, (program.predicate 17).body = .mem 0 [.leaf 11] (.range 64) real := predicate_norm_2ea_body
set_option maxRecDepth 4096 in
theorem norm_rangeSq : ∃ real, (program.predicate 18).body = .mem 0 [.leaf 12] (.range 64) real := predicate_norm_2esq_body
set_option maxRecDepth 4096 in
theorem norm_rangeCc : ∃ real, (program.predicate 19).body = .mem 0 [.leaf 13] (.range 189) real := predicate_norm_2ecc_body
set_option maxRecDepth 4096 in
theorem norm_rangeNd : ∃ real, (program.predicate 20).body = .mem 0 [.leaf 14] (.range 64) real := predicate_norm_2end_body
set_option maxRecDepth 4096 in
theorem norm_rangeNc : ∃ real, (program.predicate 21).body = .mem 0 [.leaf 15] (.range 64) real := predicate_norm_2enc_body
set_option maxRecDepth 4096 in
theorem norm_rangeD : ∃ real, (program.predicate 22).body = .mem 0 [.leaf 16] (.range 64) real := predicate_norm_2eD_body
set_option maxRecDepth 4096 in
theorem norm_high : ∃ real, (program.predicate 23).body = .mem 0 [.ref 51] (.range 16) real := predicate_enc_2ehigh_body
set_option maxRecDepth 4096 in
theorem norm_slack : ∃ real, (program.predicate 24).body =
    .mem 0 [.add (.scale (.const 12288) (.apply (.sum 512) (.ref 51))) (.leaf 19)] (.range 393)
      real := predicate_enc_2eslack_body

/-- The norm's index maps of the batches (`6426` entries, decided coordinate by coordinate). -/
theorem norm_i70_entry : ∀ b < 17, ∀ m < 6, ∀ s < 63, idx49.entry ((6 * b + m) * 63 + s) =
    if 63 * b + s < 1024 then 6 * (63 * b + s) + m else 6144 := by
  rw [idx49_eq]
  decide +kernel

/-- The coefficient and first two digit index maps of the norm. -/
theorem norm_linear_entries : ∀ i < 1024, idx33.entry i = i ∧
    idx34.entry i = 3 * i ∧ idx35.entry i = 3 * i + 1 := by
  rw [idx33_eq, idx34_eq, idx35_eq]
  decide +kernel

/-- The first three digit columns and their carry index maps. -/
theorem norm_digit_entries : ∀ i < 1024, idx37.entry i = 6 * i ∧ idx38.entry i = 5 * i ∧
    idx39.entry i = 6 * i + 1 ∧ idx40.entry i = 5 * i + 1 ∧
    idx41.entry i = 6 * i + 2 ∧ idx42.entry i = 5 * i + 2 := by
  rw [idx37_eq, idx38_eq, idx39_eq, idx40_eq, idx41_eq, idx42_eq]
  decide +kernel

set_option maxRecDepth 4096 in
/-- **The generic norm's identifiers and facts** at the ring's one domain. -/
@[expose] noncomputable instance : FalconNorm program where
  dA := 0
  fA := 0
  domainField := domainField0_checked
  s2 := 9
  s1 := 10
  a := 11
  sq := 12
  cc := 13
  nd := 14
  nc := 15
  D := 16
  Dc := 17
  tgt := 18
  off := 19
  z1 := 1
  z := 3
  e0 := 21
  p0 := 2
  eMax := 54
  pDc := 15
  pEncB := 16
  pRange := 17
  pHigh := 23
  pSlack := 24
  eHigh := 51
  eMid := 53
  eB := 54
  iHigh := idx54
  iMid := idx55
  i52 := idx33
  i54 := idx34
  i55 := idx35
  i56 := idx36
  i57 := idx17
  i58 := idx37
  i59 := idx38
  i60 := idx39
  i61 := idx40
  i62 := idx41
  i63 := idx42
  i64 := idx43
  i65 := idx44
  i66 := idx45
  i67 := idx46
  i68 := idx47
  i69 := idx48
  i70 := idx49
  i71 := idx50
  i72 := idx51
  i73 := idx52
  i74 := idx53
  refsOrdered := Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.refsOrdered
  inSource_A := by
    intro v hv
    change v ∈ [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨predicate_norm_2ecenter_role.1, program.inSource_of_source predicate_norm_2ecenter_role.2⟩
    · exact ⟨predicate_norm_2etop_role.1, program.inSource_of_source predicate_norm_2etop_role.2⟩
    · exact ⟨predicate_norm_2ecolumn0_role.1, program.inSource_of_source predicate_norm_2ecolumn0_role.2⟩
    · exact ⟨predicate_norm_2ecolumn1_role.1, program.inSource_of_source predicate_norm_2ecolumn1_role.2⟩
    · exact ⟨predicate_norm_2ecolumn2_role.1, program.inSource_of_source predicate_norm_2ecolumn2_role.2⟩
    · exact ⟨predicate_norm_2ecolumn3_role.1, program.inSource_of_source predicate_norm_2ecolumn3_role.2⟩
    · exact ⟨predicate_norm_2ecolumn4_role.1, program.inSource_of_source predicate_norm_2ecolumn4_role.2⟩
    · exact ⟨predicate_norm_2ecolumn5_role.1, program.inSource_of_source predicate_norm_2ecolumn5_role.2⟩
    · exact ⟨predicate_norm_2enormalize_role.1, program.inSource_of_source predicate_norm_2enormalize_role.2⟩
    · exact ⟨predicate_norm_2ecomplement_role.1, program.inSource_of_source predicate_norm_2ecomplement_role.2⟩
    · exact ⟨predicate_norm_2eDc_2eboolean_role.1, program.inSource_of_type predicate_norm_2eDc_2eboolean_role.2 (valueShape_role value_norm_2eDc_header.2)⟩
    · exact ⟨predicate_enc_2eb_2eboolean_role.1, program.inSource_of_source predicate_enc_2eb_2eboolean_role.2⟩
    · exact ⟨predicate_norm_2ea_role.1, program.inSource_of_source predicate_norm_2ea_role.2⟩
    · exact ⟨predicate_norm_2esq_role.1, program.inSource_of_source predicate_norm_2esq_role.2⟩
    · exact ⟨predicate_norm_2ecc_role.1, program.inSource_of_source predicate_norm_2ecc_role.2⟩
    · exact ⟨predicate_norm_2end_role.1, program.inSource_of_source predicate_norm_2end_role.2⟩
    · exact ⟨predicate_norm_2enc_role.1, program.inSource_of_source predicate_norm_2enc_role.2⟩
    · exact ⟨predicate_norm_2eD_role.1, program.inSource_of_source predicate_norm_2eD_role.2⟩
    · exact ⟨predicate_enc_2ehigh_role.1, program.inSource_of_source predicate_enc_2ehigh_role.2⟩
    · exact ⟨predicate_enc_2eslack_role.1, program.inSource_of_source predicate_enc_2eslack_role.2⟩
  center := norm_center
  top := norm_top
  col0 := norm_col0
  col1 := norm_col1
  col2 := norm_col2
  col3 := norm_col3
  col4 := norm_col4
  col5 := norm_col5
  normalize := norm_normalize
  complement := norm_complement
  dcBool := norm_dcBool
  encB := norm_encB
  rangeA := norm_rangeA
  rangeSq := norm_rangeSq
  rangeCc := norm_rangeCc
  rangeNd := norm_rangeNd
  rangeNc := norm_rangeNc
  rangeD := norm_rangeD
  high := norm_high
  slack := norm_slack
  exprs_norm := ⟨expr_norm_2ecenter_2eshape_2eleft_2efirst_2efirst_eq,
    expr_norm_2ecenter_2eshape_2eleft_2esecond_2efirst_2efirst_2efirst_2efirst_eq,
    expr_norm_2ecenter_2eshape_2eleft_2esecond_2efirst_2efirst_2efirst_2esecond_2efirst_eq,
    expr_norm_2ecenter_2eshape_2eleft_2esecond_2efirst_2efirst_2esecond_2efirst_eq,
    expr_norm_2etop_2eshape_2eleft_eq,
    expr_norm_2ecolumn0_2eshape_2eleft_2efirst_eq,
    expr_norm_2ecolumn0_2eshape_2eright_2efirst_eq,
    expr_norm_2ecolumn0_2eshape_2eright_2esecond_2efirst_eq,
    expr_norm_2ecolumn1_2eshape_2eleft_2efirst_2efirst_2esecond_eq,
    expr_norm_2ecolumn1_2eshape_2eleft_2esecond_eq,
    expr_norm_2ecolumn1_2eshape_2eright_2efirst_eq,
    expr_norm_2ecolumn1_2eshape_2eright_2esecond_2efirst_eq,
    expr_norm_2ecolumn4_2eshape_2eleft_2efirst_2efirst_eq,
    expr_norm_2ecolumn2_2eshape_2eleft_2esecond_eq,
    expr_norm_2ecolumn2_2eshape_2eright_2efirst_eq,
    expr_norm_2ecolumn2_2eshape_2eright_2esecond_2efirst_eq,
    expr_norm_2ecolumn3_2eshape_2eleft_2esecond_eq,
    expr_norm_2ecolumn3_2eshape_2eright_2efirst_eq,
    expr_norm_2ecolumn3_2eshape_2eright_2esecond_2efirst_eq,
    expr_norm_2ecolumn4_2eshape_2eleft_2esecond_eq,
    expr_norm_2ecolumn4_2eshape_2eright_2efirst_eq,
    expr_norm_2ecolumn4_2eshape_2eright_2esecond_2efirst_eq,
    expr_norm_2ecolumn5_2eshape_2eleft_eq,
    expr_norm_2ecolumn5_2eshape_2eright_eq,
    expr_norm_2enormalize_2eshape_2eleft_2efirst_2efirst_eq,
    expr_norm_2enormalize_2eshape_2eleft_2efirst_2esecond_2efirst_eq,
    expr_norm_2enormalize_2eshape_2eleft_2esecond_eq,
    expr_norm_2enormalize_2eshape_2eright_2esecond_2efirst_eq,
    expr_norm_2ecomplement_2eshape_2eleft_2efirst_2efirst_eq,
    expr_norm_2ecomplement_2eshape_2eleft_2esecond_eq⟩
  exprs_enc := ⟨expr_enc_2eb_2eboolean_2eshape_2eright_2eshared_2esecond_2efirst_eq, expr_enc_2eb_2eboolean_2eshape_2eright_2eshared_2efirst_eq, expr_enc_2eb_2eboolean_2eshape_2eright_eq⟩
  norm_le := by decide
  enc_le := by decide
  idx_enc := by rw [idx54_eq, idx55_eq]; decide +kernel
  exprs_length := by
    apply program.expr_lt_of_ne_default
    rw [expr_enc_2eb_2eboolean_2eshape_2eright_eq]
    intro h
    contradiction
  sizes_A := ⟨valueShape_size value_s2_header.2, valueShape_size value_signature_2es1_header.2, valueShape_size value_norm_2ea_header.2, valueShape_size value_norm_2esq_header.2, valueShape_size value_norm_2ecc_header.2, valueShape_size value_norm_2end_header.2, valueShape_size value_norm_2enc_header.2, valueShape_size value_norm_2eD_header.2, valueShape_size value_norm_2eDc_header.2, valueShape_size value_member_2ezero_header.2, valueShape_size value_norm_2ecenter_2ezero_header.2⟩
  primeA_all := by
    intro v hv
    change v ∈ [9, 10, 11, 12, 13, 14, 15, 16] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨value_s2_header.1, valueShape_role value_s2_header.2, valueShape_typeSource value_s2_header.2, value_s2_type.2, valueShape_field value_s2_header.2, isConstant_of_priv value_s2_kind⟩
    · exact ⟨value_signature_2es1_header.1, valueShape_role value_signature_2es1_header.2, valueShape_typeSource value_signature_2es1_header.2, value_signature_2es1_type.2, valueShape_field value_signature_2es1_header.2, isConstant_of_priv value_signature_2es1_kind⟩
    · exact ⟨value_norm_2ea_header.1, valueShape_role value_norm_2ea_header.2, valueShape_typeSource value_norm_2ea_header.2, value_norm_2ea_type.2, valueShape_field value_norm_2ea_header.2, isConstant_of_priv value_norm_2ea_kind⟩
    · exact ⟨value_norm_2esq_header.1, valueShape_role value_norm_2esq_header.2, valueShape_typeSource value_norm_2esq_header.2, value_norm_2esq_type.2, valueShape_field value_norm_2esq_header.2, isConstant_of_priv value_norm_2esq_kind⟩
    · exact ⟨value_norm_2ecc_header.1, valueShape_role value_norm_2ecc_header.2, valueShape_typeSource value_norm_2ecc_header.2, value_norm_2ecc_type.2, valueShape_field value_norm_2ecc_header.2, isConstant_of_priv value_norm_2ecc_kind⟩
    · exact ⟨value_norm_2end_header.1, valueShape_role value_norm_2end_header.2, valueShape_typeSource value_norm_2end_header.2, value_norm_2end_type.2, valueShape_field value_norm_2end_header.2, isConstant_of_priv value_norm_2end_kind⟩
    · exact ⟨value_norm_2enc_header.1, valueShape_role value_norm_2enc_header.2, valueShape_typeSource value_norm_2enc_header.2, value_norm_2enc_type.2, valueShape_field value_norm_2enc_header.2, isConstant_of_priv value_norm_2enc_kind⟩
    · exact ⟨value_norm_2eD_header.1, valueShape_role value_norm_2eD_header.2, valueShape_typeSource value_norm_2eD_header.2, value_norm_2eD_type.2, valueShape_field value_norm_2eD_header.2, isConstant_of_priv value_norm_2eD_kind⟩
  fields_A := ⟨valueShape_field value_norm_2eDc_header.2, isConstant_of_priv value_norm_2eDc_kind⟩
  noBound := by
    intro v hv
    cases hk : (program.value v).kind with
    | bound e =>
      have hb : (program.value v).kind.isBound = true := by rw [hk]; rfl
      have hs := (program.boundRecsV_sound (boundRecsV_of_completionB Generated.Falcon512.Ring.Native.QROMParams.conditions.completion hv) hb).1
      obtain ⟨r, hr⟩ := Generated.Falcon512.Ring.Native.QROMParams.SourceRoleFacts.rolesOk.bound_covered hv hs hb
      obtain ⟨hm, he⟩ := sourceRoleTable_mem hr
      rw [Generated.Falcon512.Ring.Native.QROMParams.SourceRoles.roles_eq] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · change 4 = v at he
        subst v
        rw [value_statement_2ering_kind] at hk
        contradiction
      · change 5 = v at he
        subst v
        rw [value_statement_2ec_kind] at hk
        contradiction
      · change 6 = v at he
        subst v
        rw [value_key_2espectrum_kind] at hk
        contradiction
      · change 7 = v at he
        subst v
        rw [value_member_2esigner_2eindex_kind] at hk
        contradiction
      · change 9 = v at he
        subst v
        rw [value_s2_kind] at hk
        contradiction
      · change 10 = v at he
        subst v
        rw [value_signature_2es1_kind] at hk
        contradiction
      · change 11 = v at he
        subst v
        rw [value_norm_2ea_kind] at hk
        contradiction
      · change 12 = v at he
        subst v
        rw [value_norm_2esq_kind] at hk
        contradiction
      · change 13 = v at he
        subst v
        rw [value_norm_2ecc_kind] at hk
        contradiction
      · change 14 = v at he
        subst v
        rw [value_norm_2end_kind] at hk
        contradiction
      · change 15 = v at he
        subst v
        rw [value_norm_2enc_kind] at hk
        contradiction
      · change 16 = v at he
        subst v
        rw [value_norm_2eD_kind] at hk
        contradiction
      · change 17 = v at he
        subst v
        rw [value_norm_2eDc_kind] at hk
        contradiction
    | _ => rfl
  consts_A := by
    refine ⟨isConstant_of_kind value_member_2ezero_kind, valueShape_field value_member_2ezero_header.2, ?_, isConstant_of_kind value_norm_2ecenter_2ezero_kind, valueShape_field value_norm_2ecenter_2ezero_header.2, ?_, isConstant_of_kind value_enc_2eslack_2eoffset_kind, valueShape_field value_enc_2eslack_2eoffset_header.2, ?_⟩
    · rw [constEntries_of_kind value_member_2ezero_kind]; rfl
    · rw [constEntries_of_kind value_norm_2ecenter_2ezero_kind]; rfl
    · rw [constEntries_of_kind value_enc_2eslack_2eoffset_kind]; rfl
  const41 := ⟨[0], value_member_2ezero_kind, rfl⟩
  const555 := ⟨valueShape_field value_norm_2etarget_header.2, [38, 16, 53, 1, 2, 0], value_norm_2etarget_kind, by decide⟩
  i52_entry := fun i hi => (norm_linear_entries i hi).1
  i54_entry := fun i hi => (norm_linear_entries i hi).2.1
  i55_entry := fun i hi => (norm_linear_entries i hi).2.2
  i56_entry := by rw [idx36_eq]; decide +kernel
  i58_entry := fun i hi => (norm_digit_entries i hi).1
  i59_entry := fun i hi => (norm_digit_entries i hi).2.1
  i60_entry := fun i hi => (norm_digit_entries i hi).2.2.1
  i61_entry := fun i hi => (norm_digit_entries i hi).2.2.2.1
  i62_entry := fun i hi => (norm_digit_entries i hi).2.2.2.2.1
  i63_entry := fun i hi => (norm_digit_entries i hi).2.2.2.2.2
  i64_entry := by rw [idx43_eq]; decide +kernel
  i65_entry := by rw [idx44_eq]; decide +kernel
  i66_entry := by rw [idx45_eq]; decide +kernel
  i67_entry := by rw [idx46_eq]; decide +kernel
  i68_entry := by rw [idx47_eq]; decide +kernel
  i52_size := by rw [idx33_eq]; decide +kernel
  i54_size := by rw [idx34_eq]; decide +kernel
  i55_size := by rw [idx35_eq]; decide +kernel
  i56_size := by rw [idx36_eq]; decide +kernel
  i67_size := by rw [idx46_eq]; decide +kernel
  i69_entry := by rw [idx48_eq]; decide +kernel
  i71_entry := by rw [idx50_eq]; decide +kernel
  i72_entry := by rw [idx51_eq]; decide +kernel
  i73_entry := by rw [idx52_eq]; decide +kernel
  i74_entry := by rw [idx53_eq]; decide +kernel
  i57_entry := by rw [idx17_eq]; decide +kernel
  i70_entry := norm_i70_entry
  idx_sizes := by rw [idx48_eq, idx49_eq, idx50_eq, idx51_eq, idx52_eq, idx53_eq]; decide +kernel


/-- The honest norm's source cells are private by their checked kinds. -/
instance : FalconNormHonest program where
  privCell := by
    intro v h
    change v ∈ [9, 10, 11, 12, 13, 14, 15, 16, 17] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_s2_header.1 value_s2_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_signature_2es1_header.1 value_signature_2es1_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2ea_header.1 value_norm_2ea_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2esq_header.1 value_norm_2esq_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2ecc_header.1 value_norm_2ecc_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2end_header.1 value_norm_2end_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2enc_header.1 value_norm_2enc_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2eD_header.1 value_norm_2eD_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2eDc_header.1 value_norm_2eDc_kind

/-- The finite honest-role schema keeps its original meanings and checked private cells. -/
instance : FalconRingRoleFacts program where
  roles := by decide +kernel
  privCell := by
    intro p h
    change p ∈ [(6, .spec), (7, .bit), (9, .nat .s2), (10, .nat .s1), (11, .nat .a), (12, .nat .sq), (13, .nat .cc), (14, .nat .nd), (15, .nat .nc), (16, .nat .D), (17, .nat .Dc)] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_key_2espectrum_header.1 value_key_2espectrum_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_member_2esigner_2eindex_header.1 value_member_2esigner_2eindex_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_s2_header.1 value_s2_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_signature_2es1_header.1 value_signature_2es1_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2ea_header.1 value_norm_2ea_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2esq_header.1 value_norm_2esq_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2ecc_header.1 value_norm_2ecc_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2end_header.1 value_norm_2end_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2enc_header.1 value_norm_2enc_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2eD_header.1 value_norm_2eD_kind
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2eDc_header.1 value_norm_2eDc_kind

/-- The native strategy's predicate coverage follows from the checked complete count and
ownership facts for the two realization predicates. -/
instance : FalconRingHonest program where
  dA_eq := rfl
  fA_eq := rfl
  s2_eq := rfl
  s1_eq := rfl
  cover := by
    intro q hq hs
    rw [predicates_length] at hq
    have h12 : q ≠ 12 := by
      intro h
      subst q
      rw [program.inSource_of_realization predicate_range_2eenc_2eslack_2ereconstruct_role.2] at hs
      contradiction
    have h13 : q ≠ 13 := by
      intro h
      subst q
      rw [program.inSource_of_realization predicate_range_2eenc_2eslack_2etop_role.2] at hs
      contradiction
    change q ∈ [0, 1, 14] ∨ q ∈ [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

/-- The source strategy reads the complete checked statement and cell summaries. -/
instance : FalconRingSource program where
  wf := Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed
  bounds := by
    intro vN hv
    rw [statement_ranges] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨Or.inl rfl, Nat.le_refl _⟩
    · exact ⟨Or.inr rfl, Nat.le_refl _⟩
  noCross := by
    intro q hq
    have hn : (program.predicate q).body.isCross ≠ true := by
      intro hc
      have hm := mem_crossPredicateIds_iff.mpr ⟨hq, hc⟩
      rw [cross_predicates] at hm
      exact List.not_mem_nil hm
    cases hb : (program.predicate q).body with
    | cross _ _ _ _ _ _ => exact False.elim (hn (by rw [hb]; rfl))
    | equal _ _ _ _ | mem _ _ _ _ | mod _ _ _ _ _ => rfl
  cells := by
    intro v hv hc
    have hcheck := cellB_of_completionB Generated.Falcon512.Ring.Native.QROMParams.conditions.completion hv
    obtain ⟨nr, hn, hm⟩ := cellNodeInB_spec (cellNodeInB_of_cellB program hcheck hc)
    change (_, nr.name) ∈ Generated.Falcon512.Ring.Native.QROMParams.Honest.nodes at hm
    rw [Generated.Falcon512.Ring.Native.QROMParams.Honest.nodes_eq] at hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    exact ⟨by simp only [hn, Option.map_some, hm.2],
      (program.isCellValue_valueField hc).trans hm.1, hm.1⟩
  checks := by
    intro m hm
    rw [statement_checks] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · refine ⟨Or.inl ?_, by decide⟩
      apply memberValue?_of_memberValuesB
        (ProgramData.memberValuesB_of_programOk GordieHoweCheck.Falcon512.Ring.Native.QROMParams.programOk) (k := 0)
      · rw [statement_checks]; rfl
      · rw [Structure.memberValueTab_eq, Generated.Falcon512.Ring.Native.QROMParams.Structure.memberValues_eq]; rfl
    · refine ⟨Or.inr ?_, by decide⟩
      apply memberValue?_of_memberValuesB
        (ProgramData.memberValuesB_of_programOk GordieHoweCheck.Falcon512.Ring.Native.QROMParams.programOk) (k := 1)
      · rw [statement_checks]; rfl
      · rw [Structure.memberValueTab_eq, Generated.Falcon512.Ring.Native.QROMParams.Structure.memberValues_eq]; rfl


end GordieHowe.Falcon512.Ring.Native.QROMParams

