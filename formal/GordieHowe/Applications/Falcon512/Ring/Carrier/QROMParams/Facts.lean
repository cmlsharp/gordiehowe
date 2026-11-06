-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.SelectionCheck
public import GordieHowe.Applications.Falcon512.Ring.Carrier.Frontend
public import GordieHowe.Applications.Falcon512.Ring.Carrier.Honest
public import GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.Structure
public import GordieHowe.Language.RealizedProgram.MemberValues
public import GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.Certified
public import GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.ShapeFacts

public section

/-!
# GordieHowe: the frontend's program facts of `Falcon512.Ring.Carrier.QROMParams`

The program facts the Falcon ring frontend reads (the table's selection `GordieHowe.Falcon512.Ring.FalconRingPowers`,
`GordieHowe.Falcon512.Ring.FalconRingSelect`, `GordieHowe.Falcon512.Ring.FalconRingMember`, `GordieHowe.Falcon512.Ring.FalconCarrierBase`),
derived from the checked shapes, completion and source-role facts of `GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.Program.program` (export
`5d775ae1`) or read off its shape facts (`GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.ShapeFacts`:
the values' kinds and the predicates' bodies), and domain `A`'s field Goldilocks⁴
(`GordieHowe.Falcon512.EField`).
-/

namespace GordieHowe.Falcon512.Ring.Carrier.QROMParams

open Generated.Falcon512.Ring.Carrier.QROMParams.Program
open Generated.Falcon512.Ring.Carrier.QROMParams (interp)
open Generated.Falcon512.Ring.Carrier.QROMParams.ShapeFacts
open Ring RealizedProgram


/-- Every field of the program has characteristic `p`. -/
instance (n : ℕ) : ExpChar (interp.field n).K pGold :=
  inferInstanceAs (ExpChar GoldilocksExt4 pGold)

/-- Domain `A`'s field is Goldilocks⁴. -/
@[expose] instance : EField (interp 0) := inferInstanceAs (EField RealizedProgram.gold4)

/-- Domain zero has the field recorded by the checked field table. -/
theorem domainField0_checked : program.domainField 0 = 0 :=
  Generated.Falcon512.Ring.Carrier.QROMParams.conditions.fieldTable.domainField_eq 0 (by decide)

/-- **The table's selection** (`member.signer`): the program check's certificate
(`GordieHowe.RealizedProgram.TableSelect.ofSelections` at `Generated.Falcon512.Ring.Carrier.QROMParams.selections`): the
record `key.spectrum`, the rows `statement.ring`, the natural-order transform of length `512`. -/
@[expose] instance : FalconRingPowers program where
  toTableSelect := TableSelect.ofSelections (ir := program) (cs := Generated.Falcon512.Ring.Carrier.QROMParams.selections)
    Generated.Falcon512.Ring.Carrier.QROMParams.core.wellFormed
    Generated.Falcon512.Ring.Carrier.QROMParams.checked.selections ⟨0, by decide⟩

/-- The selection's identifiers. -/
instance : FalconRingSelect program := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **`member.signer`**: `Σ_k spectrum_k γ^k` less the digest the index bits select is `0`. -/
theorem carrier_member : ∃ t, (program.predicate 0).body =
    .equal 0 (memberLhs 6 17 7 mOneG) (.leaf 1) t := predicate_member_2esigner_body

/-- **`member.signer.index.boolean`**: the index bits are bits. -/
theorem carrier_idxBool :
    ∃ t, (program.predicate 9).body = .equal 0 (.mul (.leaf 7) (.leaf 7)) (.leaf 7) t :=
  predicate_member_2esigner_2eindex_2eboolean_body

set_option maxRecDepth 4096 in
/-- The membership's facts: the ring `4`, the challenge `5`, the spectrum `6`, `s2` `9`, the powers
`17`, the zero constant `1`, `ψ = psiG`, `−1 = p − 1`, the index bits' check `9`. -/
@[expose] instance : FalconRingMember program where
  ring := 4
  spec := 6
  pow := 17
  zero := 1
  psi := psiG
  mOne := mOneG
  idxPred := 9
  chal := 5
  s2 := 9
  domainField0 := domainField0_checked
  member := carrier_member
  idxBool := carrier_idxBool
  inSource := by
    intro q hq
    change q ∈ [0, 9] at hq
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
    change v ∈ [0, 1, 4, 6, 7, 8, 17, 18, 5, 9] at hv
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
    rw [program.isSourceChal_iff_mem_sourceChallengeIds Generated.Falcon512.Ring.Carrier.QROMParams.conditions.wellFormed,
      source_challenges, List.mem_singleton]
  values_length := value_member_2eone_header.1
  privKinds := ⟨value_key_2espectrum_kind, value_member_2esigner_2eindex_kind, value_s2_kind⟩

/-- **`signature.equation`**: the spectral product form of `c − s1 ≡ h · s2 (mod q)`. -/
theorem carrier_sig : ∃ real, (program.predicate 4).body = .mod 0 12289 carrierSigP carrierSigN real ∧
    real.form = .spectralProduct ∧ real.quotient = some (.leaf 11) ∧
    real.quotientLo = -6291457 ∧ real.qmax = 12570625 :=
  predicate_signature_2eequation_body

set_option maxRecDepth 4096 in
/-- The carrier's facts outside the membership. -/
instance : FalconCarrierBase program where
  ids := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  sig := carrier_sig
  magS1 := predicate_magnitudes_2es1_body
  magS2 := predicate_magnitudes_2es2_body
  normSum := predicate_norm_2esum_body
  rMag1 := predicate_magnitudes_2emag1_body
  rMag2 := predicate_magnitudes_2emag2_body
  rLow2 := predicate_encoding_2elow2_body
  rBudget := predicate_encoding_2ebudget_body
  rNorm := predicate_norm_2ebound_body
  rQuot := predicate_signature_2eequation_2eq_body
  high2 := by
    obtain ⟨r, h, hf, -⟩ := predicate_encoding_2ehigh2_body
    exact ⟨r, h, by rw [hf]; rfl⟩
  inSource := by
    intro q hq
    change q ∈ [1, 2, 3, 4, 10, 11, 12, 13, 14, 15, 17] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨predicate_magnitudes_2es1_role.1, program.inSource_of_source predicate_magnitudes_2es1_role.2⟩
    · exact ⟨predicate_magnitudes_2es2_role.1, program.inSource_of_source predicate_magnitudes_2es2_role.2⟩
    · exact ⟨predicate_norm_2esum_role.1, program.inSource_of_source predicate_norm_2esum_role.2⟩
    · exact ⟨predicate_signature_2eequation_role.1, program.inSource_of_source predicate_signature_2eequation_role.2⟩
    · exact ⟨predicate_magnitudes_2emag1_role.1, program.inSource_of_source predicate_magnitudes_2emag1_role.2⟩
    · exact ⟨predicate_magnitudes_2emag2_role.1, program.inSource_of_source predicate_magnitudes_2emag2_role.2⟩
    · exact ⟨predicate_encoding_2elow2_role.1, program.inSource_of_source predicate_encoding_2elow2_role.2⟩
    · exact ⟨predicate_encoding_2ebudget_role.1, program.inSource_of_source predicate_encoding_2ebudget_role.2⟩
    · exact ⟨predicate_norm_2ebound_role.1, program.inSource_of_source predicate_norm_2ebound_role.2⟩
    · exact ⟨predicate_signature_2eequation_2eq_role.1, program.inSource_of_source predicate_signature_2eequation_2eq_role.2⟩
    · exact ⟨predicate_encoding_2ehigh2_role.1, program.inSource_of_source predicate_encoding_2ehigh2_role.2⟩
  consts := by
    exact ⟨RealizedProgram.isConstant_of_kind value_magnitudes_2emodulus_kind,
      by rw [RealizedProgram.constEntries_of_kind value_magnitudes_2emodulus_kind]; rfl,
      RealizedProgram.isConstant_of_kind value_magnitudes_2ezero_kind,
      by rw [RealizedProgram.constEntries_of_kind value_magnitudes_2ezero_kind]; rfl,
      RealizedProgram.isConstant_of_kind value_encoding_2ebudget_2eoffset_kind,
      by rw [RealizedProgram.constEntries_of_kind value_encoding_2ebudget_2eoffset_kind]; rfl⟩
  fields := by
    intro v hv
    change v ∈ [2, 3, 10, 11, 12, 13, 14, 15, 16] at hv
    change program.valueField v = 0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact RealizedProgram.valueShape_field value_magnitudes_2emodulus_header.2
    · exact RealizedProgram.valueShape_field value_magnitudes_2ezero_header.2
    · exact RealizedProgram.valueShape_field value_signature_2es1_header.2
    · exact RealizedProgram.valueShape_field value_signature_2eequation_2eq_header.2
    · exact RealizedProgram.valueShape_field value_magnitudes_2emag1_header.2
    · exact RealizedProgram.valueShape_field value_magnitudes_2emag2_header.2
    · exact RealizedProgram.valueShape_field value_encoding_2elow2_header.2
    · exact RealizedProgram.valueShape_field value_encoding_2ebudget_2eoffset_header.2
    · exact RealizedProgram.valueShape_field value_norm_2esquares_header.2
  sizes := ⟨RealizedProgram.valueShape_size value_signature_2es1_header.2, RealizedProgram.valueShape_size value_signature_2eequation_2eq_header.2, RealizedProgram.valueShape_size value_magnitudes_2emag1_header.2, RealizedProgram.valueShape_size value_magnitudes_2emag2_header.2, RealizedProgram.valueShape_size value_encoding_2elow2_header.2, RealizedProgram.valueShape_size value_norm_2esquares_header.2⟩
  privKinds := ⟨value_signature_2es1_kind, value_magnitudes_2emag2_kind, value_encoding_2elow2_kind⟩
  ringCheck := by
    refine ⟨⟨"ring", 0, 65536, "falcon_ring_key_u16le", [512, 12289]⟩, ?_, ?_, rfl⟩
    · rw [statement_checks]
      simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
    · apply RealizedProgram.memberValue?_of_memberValuesB
        (ProgramData.memberValuesB_of_programOk GordieHoweCheck.Falcon512.Ring.Carrier.QROMParams.programOk) (k := 0)
      · rw [statement_checks]; rfl
      · rw [RealizedProgram.Structure.memberValueTab_eq, Generated.Falcon512.Ring.Carrier.QROMParams.Structure.memberValues_eq]; rfl
  chalCheck := by
    refine ⟨⟨"c", 65536, 1024, "falcon_challenge_canonical", [12289]⟩, ?_, ?_, rfl⟩
    · rw [statement_checks]
      simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
    · apply RealizedProgram.memberValue?_of_memberValuesB
        (ProgramData.memberValuesB_of_programOk GordieHoweCheck.Falcon512.Ring.Carrier.QROMParams.programOk) (k := 1)
      · rw [statement_checks]; rfl
      · rw [RealizedProgram.Structure.memberValueTab_eq, Generated.Falcon512.Ring.Carrier.QROMParams.Structure.memberValues_eq]; rfl

/-! ## Honest source and completion facts -/

/-- Generated node-typed values receive committed cells from the completion check. -/
private theorem generatedCell {v owner : Nat} {header : ValueShape}
    (hh : v < program.values.length ∧ program.valueShape v = header)
    (ht : header.typeSource = .node) (hp : header.phase = 0)
    (hr : header.role = .realization owner) : program.privCellB v = true := by
  have hc := realTypeB_of_completionB Generated.Falcon512.Ring.Carrier.QROMParams.conditions.completion hh.1
  exact privCellB_of_realTypeB program hc ((valueShape_typeSource hh.2).trans ht)
    (program.not_IsLate_of_phase_zero ((valueShape_phase hh.2).trans hp))
    (program.not_IsSourceValue_of_realization ((valueShape_role hh.2).trans hr))

/-- The finite role schema is unchanged; cell ownership comes from checked facts. -/
instance : FalconRingRoleFacts program where
  roles := by decide +kernel
  privCell := by
    intro p hp
    change p ∈ [(6, .spec), (7, .bit), (9, .nat .s2), (10, .nat .s1), (13, .nat .mag2), (14, .nat .low2), (36, .nat (.quotD 0)), (37, .nat (.quotD 1)), (38, .nat (.quotD 2)), (19, .nat (.mag1D 0)), (20, .nat (.mag1D 1)), (29, .nat (.normD 0)), (30, .nat (.normD 1)), (31, .nat (.normD 2))] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Generated.Falcon512.Ring.Carrier.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_key_2espectrum_header.1 value_key_2espectrum_kind
    · exact Generated.Falcon512.Ring.Carrier.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_member_2esigner_2eindex_header.1 value_member_2esigner_2eindex_kind
    · exact Generated.Falcon512.Ring.Carrier.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_s2_header.1 value_s2_kind
    · exact Generated.Falcon512.Ring.Carrier.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_signature_2es1_header.1 value_signature_2es1_kind
    · exact Generated.Falcon512.Ring.Carrier.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_magnitudes_2emag2_header.1 value_magnitudes_2emag2_kind
    · exact Generated.Falcon512.Ring.Carrier.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_encoding_2elow2_header.1 value_encoding_2elow2_kind
    · exact generatedCell value_range_2esignature_2eequation_2eq_2ed0_header rfl rfl rfl
    · exact generatedCell value_range_2esignature_2eequation_2eq_2ed1_header rfl rfl rfl
    · exact generatedCell value_range_2esignature_2eequation_2eq_2ed2_header rfl rfl rfl
    · exact generatedCell value_range_2emagnitudes_2emag1_2ed0_header rfl rfl rfl
    · exact generatedCell value_range_2emagnitudes_2emag1_2ed1_header rfl rfl rfl
    · exact generatedCell value_range_2enorm_2ebound_2ed0_header rfl rfl rfl
    · exact generatedCell value_range_2enorm_2ebound_2ed1_header rfl rfl rfl
    · exact generatedCell value_range_2enorm_2ebound_2ed2_header rfl rfl rfl

/-- The source strategy reads the complete checked statement and cell summaries. -/
instance : FalconRingSource program where
  wf := Generated.Falcon512.Ring.Carrier.QROMParams.conditions.wellFormed
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
    have hcheck := cellB_of_completionB Generated.Falcon512.Ring.Carrier.QROMParams.conditions.completion hv
    obtain ⟨nr, hn, hm⟩ := cellNodeInB_spec (cellNodeInB_of_cellB program hcheck hc)
    change (_, nr.name) ∈ Generated.Falcon512.Ring.Carrier.QROMParams.Honest.nodes at hm
    rw [Generated.Falcon512.Ring.Carrier.QROMParams.Honest.nodes_eq] at hm
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
        (ProgramData.memberValuesB_of_programOk GordieHoweCheck.Falcon512.Ring.Carrier.QROMParams.programOk) (k := 0)
      · rw [statement_checks]; rfl
      · rw [Structure.memberValueTab_eq, Generated.Falcon512.Ring.Carrier.QROMParams.Structure.memberValues_eq]; rfl
    · refine ⟨Or.inr ?_, by decide⟩
      apply memberValue?_of_memberValuesB
        (ProgramData.memberValuesB_of_programOk GordieHoweCheck.Falcon512.Ring.Carrier.QROMParams.programOk) (k := 1)
      · rw [statement_checks]; rfl
      · rw [Structure.memberValueTab_eq, Generated.Falcon512.Ring.Carrier.QROMParams.Structure.memberValues_eq]; rfl

/-- The realization fields, sizes and ownership follow from named checked metadata. -/
instance : FalconCarrierHonest program where
  refsOrdered := Generated.Falcon512.Ring.Carrier.QROMParams.conditions.wellFormed.refsOrdered
  idx9 := rfl
  realPreds := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact program.inSource_of_realization predicate_range_2emagnitudes_2emag1_2etop_role.2
    · exact program.inSource_of_realization predicate_range_2eencoding_2ebudget_2ereconstruct_role.2
    · exact program.inSource_of_realization predicate_range_2eencoding_2ebudget_2etop_role.2
    · exact program.inSource_of_realization predicate_range_2enorm_2ebound_2etop_role.2
    · exact program.inSource_of_realization predicate_encoding_2ehigh2_2eq_role.2
  quotKind := value_signature_2eequation_2eq_kind
  mag1Kind := value_magnitudes_2emag1_kind
  sqKind := value_norm_2esquares_kind
  fields := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact valueShape_field value_signature_2eequation_2eq_header.2
    · exact valueShape_field value_magnitudes_2emag1_header.2
    · exact valueShape_field value_norm_2esquares_header.2
  roleFields := by
    intro p hp
    change p ∈ [(9, .s2), (10, .s1), (13, .mag2), (14, .low2), (36, (.quotD 0)), (37, (.quotD 1)), (38, (.quotD 2)), (19, (.mag1D 0)), (20, (.mag1D 1)), (29, (.normD 0)), (30, (.normD 1)), (31, (.normD 2))] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact valueShape_field value_s2_header.2
    · exact valueShape_field value_signature_2es1_header.2
    · exact valueShape_field value_magnitudes_2emag2_header.2
    · exact valueShape_field value_encoding_2elow2_header.2
    · exact valueShape_field value_range_2esignature_2eequation_2eq_2ed0_header.2
    · exact valueShape_field value_range_2esignature_2eequation_2eq_2ed1_header.2
    · exact valueShape_field value_range_2esignature_2eequation_2eq_2ed2_header.2
    · exact valueShape_field value_range_2emagnitudes_2emag1_2ed0_header.2
    · exact valueShape_field value_range_2emagnitudes_2emag1_2ed1_header.2
    · exact valueShape_field value_range_2enorm_2ebound_2ed0_header.2
    · exact valueShape_field value_range_2enorm_2ebound_2ed1_header.2
    · exact valueShape_field value_range_2enorm_2ebound_2ed2_header.2
  sizes512 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact valueShape_size value_s2_header.2
    · exact valueShape_size value_range_2esignature_2eequation_2eq_2ed0_header.2
    · exact valueShape_size value_range_2esignature_2eequation_2eq_2ed1_header.2
    · exact valueShape_size value_range_2esignature_2eequation_2eq_2ed2_header.2
    · exact valueShape_size value_range_2emagnitudes_2emag1_2ed0_header.2
    · exact valueShape_size value_range_2emagnitudes_2emag1_2ed1_header.2
  sizes1 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact valueShape_size value_range_2enorm_2ebound_2ed0_header.2
    · exact valueShape_size value_range_2enorm_2ebound_2ed1_header.2
    · exact valueShape_size value_range_2enorm_2ebound_2ed2_header.2
  lens := by rw [values_length]; decide
  bound := Generated.Falcon512.Ring.Carrier.QROMParams.conditions.derivable.elim fun _ hD => hD.bound
  cover := predicates_length


end GordieHowe.Falcon512.Ring.Carrier.QROMParams
