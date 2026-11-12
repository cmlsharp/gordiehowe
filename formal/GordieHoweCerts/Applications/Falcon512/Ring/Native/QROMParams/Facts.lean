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

theorem ring_member : ∃ t, (program.predicate 0).body = .equal 0 (.add (.apply (.sum 512)
    (.mul (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.leaf 5))) (.reindex [(0, 1, 512)] (.leaf 21))))
    (.scale (.const 12288) (.mux (.reindex [(5, 0, 1)] (.leaf 6)) (.reindex [(1, 0, 1)] (.ref 20))
      (.reindex [(0, 0, 1)] (.ref 20))))) (.leaf 1) t := predicate_member_2esigner_body

theorem ring_sig : ∃ t, (program.predicate 1).body =
    .equal 0 (sigLhs (.add (.leaf 4) (.scale (.const 12288) (.leaf 9))) 5 8 10 23 24 25 12288)
      (.leaf 1) t := predicate_signature_2eequation_body

theorem ring_idxBool :
    ∃ t, (program.predicate 14).body = .equal 0 (.mul (.leaf 6) (.leaf 6)) (.leaf 6) t := predicate_member_2esigner_2eindex_2eboolean_body

/-- The membership's facts: the ring `4`, the spectrum `6`, the powers `20`, the zero constant `1`,
`ψ = 10302`, `−1 = 12288`, the index bits' check `14`. -/
@[expose] instance : FalconRingMember program where
  ring := 3
  spec := 5
  pow := 21
  zero := 1
  psi := 10302
  mOne := 12288
  idxPred := 14
  chal := 4
  s2 := 8
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
    change v ∈ [0, 1, 3, 5, 6, 7, 21, 22, 4, 8] at hv
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
  isSourceChal_zero := by
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed,
      source_challenges]
    simp
  values_length := value_member_2eone_header.1
  privKinds := ⟨value_key_2espectrum_kind, value_member_2esigner_2eindex_kind, value_s2_kind⟩

/-- The native ring's facts outside the membership. -/
instance : FalconRingBase program where
  s1 := 9
  q := 10
  r := 11
  rChal := 1
  one := 0
  zero1 := 1
  pw := 23
  lam := 24
  rn := 25
  pwRef := 37
  r256Ref := 36
  sigPred := 1
  sigE := .add (.leaf 4) (.scale (.const 12288) (.leaf 9))
  nInv := 12265
  psiInv := 8974
  consts := ⟨rfl, rfl⟩
  invConsts := ⟨rfl, rfl⟩
  sigE_eq := rfl
  sigELen := rfl
  sig := ring_sig
  inSourceSig := ⟨predicate_signature_2eequation_role.1, program.inSource_of_source predicate_signature_2eequation_role.2⟩
  const0 := ⟨isConstant_of_kind value_signature_2ezero_kind, by rw [constEntries_of_kind value_signature_2ezero_kind]⟩
  sigFields := by
    intro v hv
    change v ∈ [1, 10, 23, 24, 25] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact valueShape_field value_signature_2ezero_header.2
    · exact valueShape_field value_signature_2eQ_header.2
    · exact valueShape_field value_signature_2eequation_2epublic0_header.2
    · exact valueShape_field value_signature_2elambda_header.2
    · exact valueShape_field value_signature_2eequation_2epublic1_header.2
  sizes := ⟨valueShape_size value_signature_2es1_header.2, valueShape_size value_signature_2eQ_header.2,
    valueShape_size value_signature_2eequation_2epublic0_header.2,
    valueShape_size value_signature_2elambda_header.2,
    valueShape_size value_signature_2eequation_2epublic1_header.2,
    valueShape_size value_signature_2ezero_header.2⟩
  primeVals := by
    intro v hv
    change v ∈ [8, 9] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨value_s2_header.1, valueShape_role value_s2_header.2, valueShape_typeSource value_s2_header.2, value_s2_type.2⟩
    · exact ⟨value_signature_2es1_header.1, valueShape_role value_signature_2es1_header.2, valueShape_typeSource value_signature_2es1_header.2, value_signature_2es1_type.2⟩
  s1Field := valueShape_field value_signature_2es1_header.2
  s1Priv := value_signature_2es1_kind
  qPriv := value_signature_2eQ_kind
  rPow :=
    { consts := ⟨isConstant_of_kind value_member_2eone_kind,
        by rw [constEntries_of_kind value_member_2eone_kind]; rfl⟩
      kind := value_signature_2er_kind
      chalField := challenge_signature_2er_full.2.2.1
      fields := ⟨valueShape_field value_member_2eone_header.2, valueShape_field value_signature_2er_header.2⟩
      sizes := ⟨valueShape_size value_member_2eone_header.2, valueShape_size value_signature_2er_header.2⟩
      values_pos := value_member_2eone_header.1 }
  chalR := ⟨challenge_signature_2er_full.2.2.2, challenge_signature_2er_full.2.1⟩
  isSourceChal_iff := fun j => by
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed,
      source_challenges]
    simp
  rChal_ne := by decide
  pwKind := value_signature_2eequation_2epublic0_definition
  lamKind := value_signature_2elambda_definition
  rnKind := value_signature_2eequation_2epublic1_definition
  refsOrdered := Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.refsOrdered
  exprs_pos := by rw [exprs_length]; decide
  powPw := by
    rw [powSym_congr (agreesBelow_replica expr_table_holds.2 (by decide +kernel)) _ _ _
      (by decide +kernel)]
    decide +kernel
  pow256 := by
    rw [powSym_congr (agreesBelow_replica expr_table_holds.2 (by decide +kernel)) _ _ _
      (by decide +kernel)]
    decide +kernel

theorem norm_center : ∃ t, (program.predicate 2).body = .equal 0 (.add (.mul (.ref 38) (.ref 38))
    (.scale (.const 12288) (.mul (.add (.add (.ref 39) (.scale (.const 64) (.ref 40)))
      (.scale (.const 4096) (.ref 41))) (.add (.add (.ref 39) (.scale (.const 64) (.ref 40)))
        (.scale (.const 4096) (.ref 41)))))) (.leaf 2) t := predicate_norm_2ecenter_body
theorem norm_top : ∃ t, (program.predicate 3).body = .equal 0 (.ref 42) (.leaf 1) t := predicate_norm_2etop_body
theorem norm_col0 : ∃ real, (program.predicate 4).body = .mod 0 0 (.mul (.ref 43) (.ref 43))
    (.add (.ref 44) (.scale (.const 64) (.ref 45))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn0_body
  exact ⟨real, h⟩
theorem norm_col1 : ∃ real, (program.predicate 5).body = .mod 0 0
    (.add (.scale (.const 2) (.mul (.ref 43) (.ref 46))) (.ref 47))
    (.add (.ref 48) (.scale (.const 64) (.ref 49))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn1_body
  exact ⟨real, h⟩
theorem norm_col2 : ∃ real, (program.predicate 6).body = .mod 0 0
    (.add (.add (.scale (.const 2) (.mul (.ref 43) (.ref 50))) (.mul (.ref 46) (.ref 46)))
      (.ref 51)) (.add (.ref 52) (.scale (.const 64) (.ref 53))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn2_body
  exact ⟨real, h⟩
theorem norm_col3 : ∃ real, (program.predicate 7).body = .mod 0 0
    (.add (.scale (.const 2) (.mul (.ref 46) (.ref 50))) (.ref 54))
    (.add (.ref 55) (.scale (.const 64) (.ref 56))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn3_body
  exact ⟨real, h⟩
theorem norm_col4 : ∃ real, (program.predicate 8).body = .mod 0 0
    (.add (.mul (.ref 50) (.ref 50)) (.ref 57)) (.add (.ref 58) (.scale (.const 64) (.ref 59)))
    real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn4_body
  exact ⟨real, h⟩
theorem norm_col5 : ∃ real, (program.predicate 9).body = .mod 0 0 (.ref 60) (.ref 61) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn5_body
  exact ⟨real, h⟩
theorem norm_normalize : ∃ real, (program.predicate 10).body = .mod 0 0
    (.add (.add (.ref 62) (.apply (.batched 102 (.sum 63)) (.ref 63))) (.ref 64))
    (.add (.leaf 15) (.scale (.const 64) (.ref 65))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2enormalize_body
  exact ⟨real, h⟩
theorem norm_complement : ∃ real, (program.predicate 11).body = .mod 0 0
    (.add (.add (.ref 66) (.leaf 17)) (.ref 67)) (.add (.leaf 19) (.scale (.const 64) (.leaf 18)))
    real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecomplement_body
  exact ⟨real, h⟩
theorem norm_dcBool : ∃ t, (program.predicate 15).body =
    .equal 0 (.mul (.leaf 18) (.leaf 18)) (.leaf 18) t := predicate_norm_2eDc_2eboolean_body
theorem norm_encB : ∃ t, (program.predicate 16).body =
    .equal 0 (.mul (.ref 71) (.ref 71)) (.ref 71) t := predicate_enc_2eb_2eboolean_body
theorem norm_rangeA : ∃ real, (program.predicate 17).body = .mem 0 [.leaf 12] (.range 64) real := predicate_norm_2ea_body
theorem norm_rangeSq : ∃ real, (program.predicate 18).body = .mem 0 [.leaf 13] (.range 64) real := predicate_norm_2esq_body
theorem norm_rangeCc : ∃ real, (program.predicate 19).body = .mem 0 [.leaf 14] (.range 189) real := predicate_norm_2ecc_body
theorem norm_rangeNd : ∃ real, (program.predicate 20).body = .mem 0 [.leaf 15] (.range 64) real := predicate_norm_2end_body
theorem norm_rangeNc : ∃ real, (program.predicate 21).body = .mem 0 [.leaf 16] (.range 64) real := predicate_norm_2enc_body
theorem norm_rangeD : ∃ real, (program.predicate 22).body = .mem 0 [.leaf 17] (.range 64) real := predicate_norm_2eD_body
theorem norm_high : ∃ real, (program.predicate 23).body = .mem 0 [.ref 68] (.range 16) real := predicate_enc_2ehigh_body
theorem norm_slack : ∃ real, (program.predicate 24).body =
    .mem 0 [.add (.scale (.const 12288) (.apply (.sum 512) (.ref 68))) (.leaf 20)] (.range 393)
      real := predicate_enc_2eslack_body

/-- The norm's index maps of the batches (`6426` entries, decided coordinate by coordinate). -/
theorem norm_i70_entry : ∀ b < 17, ∀ m < 6, ∀ s < 63, idx50.entry ((6 * b + m) * 63 + s) =
    if 63 * b + s < 1024 then 6 * (63 * b + s) + m else 6144 := by
  rw [idx50_eq]
  decide +kernel

/-- The coefficient and first two digit index maps of the norm. -/
theorem norm_linear_entries : ∀ i < 1024, idx34.entry i = i ∧
    idx35.entry i = 3 * i ∧ idx36.entry i = 3 * i + 1 := by
  rw [idx34_eq, idx35_eq, idx36_eq]
  decide +kernel

/-- The first three digit columns and their carry index maps. -/
theorem norm_digit_entries : ∀ i < 1024, idx38.entry i = 6 * i ∧ idx39.entry i = 5 * i ∧
    idx40.entry i = 6 * i + 1 ∧ idx41.entry i = 5 * i + 1 ∧
    idx42.entry i = 6 * i + 2 ∧ idx43.entry i = 5 * i + 2 := by
  rw [idx38_eq, idx39_eq, idx40_eq, idx41_eq, idx42_eq, idx43_eq]
  decide +kernel

-- The `decide +kernel` checks of this instance decide closed goals about literals: the named
-- generated facts (`…_kind`, `expr_…_eq`, `idx…_eq`) are rewritten into them first.
/-- **The generic norm's identifiers and facts** at the ring's one domain. -/
@[expose] noncomputable instance : FalconNorm program where
  dA := 0
  fA := 0
  domainField := domainField0_checked
  s2 := 8
  s1 := 9
  a := 12
  sq := 13
  cc := 14
  nd := 15
  nc := 16
  D := 17
  Dc := 18
  tgt := 19
  off := 20
  z1 := 1
  z := 2
  e0 := 38
  p0 := 2
  eMax := 71
  pDc := 15
  pEncB := 16
  pRange := 17
  pHigh := 23
  pSlack := 24
  eHigh := 68
  eMid := 70
  eB := 71
  iHigh := idx55
  iMid := idx56
  i52 := idx34
  i54 := idx35
  i55 := idx36
  i56 := idx37
  i57 := idx17
  i58 := idx38
  i59 := idx39
  i60 := idx40
  i61 := idx41
  i62 := idx42
  i63 := idx43
  i64 := idx44
  i65 := idx45
  i66 := idx46
  i67 := idx47
  i68 := idx48
  i69 := idx49
  i70 := idx50
  i71 := idx51
  i72 := idx52
  i73 := idx53
  i74 := idx54
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
  idx_enc := by rw [idx55_eq, idx56_eq]; decide +kernel
  exprs_length := by
    apply program.expr_lt_of_ne_default
    rw [expr_enc_2eb_2eboolean_2eshape_2eright_eq]
    intro h
    contradiction
  sizes_A := ⟨valueShape_size value_s2_header.2, valueShape_size value_signature_2es1_header.2, valueShape_size value_norm_2ea_header.2, valueShape_size value_norm_2esq_header.2, valueShape_size value_norm_2ecc_header.2, valueShape_size value_norm_2end_header.2, valueShape_size value_norm_2enc_header.2, valueShape_size value_norm_2eD_header.2, valueShape_size value_norm_2eDc_header.2, valueShape_size value_member_2ezero_header.2, valueShape_size value_norm_2ecenter_2ezero_header.2⟩
  primeA_all := by
    intro v hv
    change v ∈ [8, 9, 12, 13, 14, 15, 16, 17] at hv
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
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · change 3 = v at he
        subst v
        rw [value_statement_2ering_kind] at hk
        contradiction
      · change 4 = v at he
        subst v
        rw [value_statement_2ec_kind] at hk
        contradiction
      · change 5 = v at he
        subst v
        rw [value_key_2espectrum_kind] at hk
        contradiction
      · change 6 = v at he
        subst v
        rw [value_member_2esigner_2eindex_kind] at hk
        contradiction
      · change 8 = v at he
        subst v
        rw [value_s2_kind] at hk
        contradiction
      · change 9 = v at he
        subst v
        rw [value_signature_2es1_kind] at hk
        contradiction
      · change 10 = v at he
        subst v
        rw [value_signature_2eQ_kind] at hk
        contradiction
      · change 12 = v at he
        subst v
        rw [value_norm_2ea_kind] at hk
        contradiction
      · change 13 = v at he
        subst v
        rw [value_norm_2esq_kind] at hk
        contradiction
      · change 14 = v at he
        subst v
        rw [value_norm_2ecc_kind] at hk
        contradiction
      · change 15 = v at he
        subst v
        rw [value_norm_2end_kind] at hk
        contradiction
      · change 16 = v at he
        subst v
        rw [value_norm_2enc_kind] at hk
        contradiction
      · change 17 = v at he
        subst v
        rw [value_norm_2eD_kind] at hk
        contradiction
      · change 18 = v at he
        subst v
        rw [value_norm_2eDc_kind] at hk
        contradiction
    | _ => rfl
  consts_A := by
    refine ⟨isConstant_of_kind value_member_2ezero_kind, valueShape_field value_member_2ezero_header.2, ?_, isConstant_of_kind value_norm_2ecenter_2ezero_kind, valueShape_field value_norm_2ecenter_2ezero_header.2, ?_, isConstant_of_kind value_enc_2eslack_2eoffset_kind, valueShape_field value_enc_2eslack_2eoffset_header.2, ?_⟩
    · rw [constEntries_of_kind value_member_2ezero_kind]; decide +kernel
    · rw [constEntries_of_kind value_norm_2ecenter_2ezero_kind]; decide +kernel
    · rw [constEntries_of_kind value_enc_2eslack_2eoffset_kind]; decide +kernel
  const41 := ⟨[0], value_member_2ezero_kind, rfl⟩
  const555 := ⟨valueShape_field value_norm_2etarget_header.2, [38, 16, 53, 1, 2, 0], value_norm_2etarget_kind, by decide⟩
  i52_entry := fun i hi => (norm_linear_entries i hi).1
  i54_entry := fun i hi => (norm_linear_entries i hi).2.1
  i55_entry := fun i hi => (norm_linear_entries i hi).2.2
  i56_entry := by rw [idx37_eq]; decide +kernel
  i58_entry := fun i hi => (norm_digit_entries i hi).1
  i59_entry := fun i hi => (norm_digit_entries i hi).2.1
  i60_entry := fun i hi => (norm_digit_entries i hi).2.2.1
  i61_entry := fun i hi => (norm_digit_entries i hi).2.2.2.1
  i62_entry := fun i hi => (norm_digit_entries i hi).2.2.2.2.1
  i63_entry := fun i hi => (norm_digit_entries i hi).2.2.2.2.2
  i64_entry := by rw [idx44_eq]; decide +kernel
  i65_entry := by rw [idx45_eq]; decide +kernel
  i66_entry := by rw [idx46_eq]; decide +kernel
  i67_entry := by rw [idx47_eq]; decide +kernel
  i68_entry := by rw [idx48_eq]; decide +kernel
  i52_size := by rw [idx34_eq]; decide +kernel
  i54_size := by rw [idx35_eq]; decide +kernel
  i55_size := by rw [idx36_eq]; decide +kernel
  i56_size := by rw [idx37_eq]; decide +kernel
  i67_size := by rw [idx47_eq]; decide +kernel
  i69_entry := by rw [idx49_eq]; decide +kernel
  i71_entry := by rw [idx51_eq]; decide +kernel
  i72_entry := by rw [idx52_eq]; decide +kernel
  i73_entry := by rw [idx53_eq]; decide +kernel
  i74_entry := by rw [idx54_eq]; decide +kernel
  i57_entry := by rw [idx17_eq]; decide +kernel
  i70_entry := norm_i70_entry
  idx_sizes := by rw [idx49_eq, idx50_eq, idx51_eq, idx52_eq, idx53_eq, idx54_eq]; decide +kernel


/-- The honest norm's source cells are private by their checked kinds. -/
instance : FalconNormHonest program where
  privCell := by
    intro v h
    change v ∈ [8, 9, 12, 13, 14, 15, 16, 17, 18] at h
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
    change p ∈ [(5, .spec), (6, .bit), (8, .nat .s2), (9, .nat .s1), (12, .nat .a), (13, .nat .sq), (14, .nat .cc), (15, .nat .nd), (16, .nat .nc), (17, .nat .D), (18, .nat .Dc), (10, .nat .quot)] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Generated.Falcon512.Ring.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_signature_2eQ_header.1 value_signature_2eQ_kind

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

