-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.Falcon512.Native.QROMParams.Certified
public import GordieHoweCerts.Generated.Falcon512.Native.QROMParams.SourceRoleFacts
public import GordieHoweCerts.Applications.Falcon512.Native.HonestFull
public import GordieHowe.Language.Honest.SourceRoles
public import GordieHoweCerts.Applications.Falcon512.Native.QROMParams.Frontend.HashFacts
public import GordieHoweCerts.Applications.Falcon512.Native.QROMParams.Frontend.AlgebraFacts

@[expose] public section

/-!
# GordieHowe: the gadget facts of `Falcon512.Native.QROMParams`

The program's instances of the honest strategy's classes, from its checked shape facts and source
roles: the hash's, the selection's, the norm's and domain `A`'s facts, the values' distinctness, the
operands of every cross-field `equal`, the covering of the source predicates and the committed
source cells' classes (`FalconHonestFull`).
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open RealizedProgram
open Generated.Falcon512.Native.QROMParams.Program
open Generated.Falcon512.Native.QROMParams.ShapeFacts
open HashShapeFacts

/-- The honest hash facts of the program of `Falcon512.Native.QROMParams`. -/
instance : FalconHHonest program where
  words_checks := words_checks
  state_checks := ⟨isBitsB_of_kind value_h2p_2eshake_2estate_kind, Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_h2p_2eshake_2estate_2ewords_header.1 value_h2p_2eshake_2estate_2ewords_kind,
    valueShape_field value_h2p_2eshake_2estate_header.2, valueShape_field value_h2p_2eshake_2estate_2ewords_header.2, valueShape_size value_h2p_2eshake_2estate_header.2, valueShape_size value_h2p_2eshake_2estate_2ewords_header.2, valueType_nodeName value_h2p_2eshake_2estate_2ewords_type.2⟩
  buf_checks := ⟨Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_nonce_header.1 value_nonce_kind, Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_message_header.1 value_message_kind, Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_message_2ein_5fmessage_header.1 value_message_2ein_5fmessage_kind, valueShape_field value_nonce_header.2, valueShape_field value_message_header.2, valueShape_field value_message_2ein_5fmessage_header.2⟩

/-- The selection values of the program of `Falcon512.Native.QROMParams`. -/
instance : FalconHSelHonest program where
  sel_checks := ⟨Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_h2p_2eselect_2eraw_2ewords_header.1 value_h2p_2eselect_2eraw_2ewords_kind, Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_h2p_2eselect_2ecount_header.1 value_h2p_2eselect_2ecount_kind, Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_h2p_2eselect_2efull_header.1 value_h2p_2eselect_2efull_kind, isBitsB_of_kind value_h2p_2eselect_2eraw_kind,
    valueShape_field value_h2p_2eselect_2eraw_2ewords_header.2, valueShape_field value_h2p_2eselect_2eraw_header.2, valueShape_field value_h2p_2eselect_2ecount_header.2, valueShape_field value_h2p_2eselect_2efull_header.2, valueShape_size value_h2p_2eselect_2eraw_2ewords_header.2, valueShape_size value_h2p_2eselect_2eraw_header.2, valueShape_size value_h2p_2eselect_2ecount_header.2, valueShape_size value_h2p_2eselect_2efull_header.2,
    by decide +kernel, by decide +kernel, valueType_nodeName value_h2p_2eselect_2eraw_2ewords_type.2⟩

/-- The honest norm facts of the program of `Falcon512.Native.QROMParams` (`Norm.FalconNormHonest`): the
norm's values are private committed cells. -/
noncomputable instance : Norm.FalconNormHonest program where
  privCell := by
    intro v hv
    change v ∈ [595, 596, 597, 598, 599, 600, 601, 602, 603] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_s2_header.1 value_s2_kind
    · exact Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_signature_2es1_header.1 value_signature_2es1_kind
    · exact Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2ea_header.1 value_norm_2ea_kind
    · exact Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2esq_header.1 value_norm_2esq_kind
    · exact Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2ecc_header.1 value_norm_2ecc_kind
    · exact Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2end_header.1 value_norm_2end_kind
    · exact Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2enc_header.1 value_norm_2enc_kind
    · exact Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2eD_header.1 value_norm_2eD_kind
    · exact Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2eDc_header.1 value_norm_2eDc_kind

/-- The facts of honest domain A of the program of `Falcon512.Native.QROMParams`: the norm at domain and
field `1`, the field-form signature `289`, `c_A`'s check `292` and `mac.equal` `309`. -/
noncomputable instance : FalconAHonest program where
  toFalconAAlg := inferInstance
  norm_dA := rfl
  norm_fA := rfl
  norm_ids := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  pSigE := 289
  pCA := 292
  pMac := 309
  a_checks := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_crossing_2ec_5fA_header.1 value_crossing_2ec_5fA_kind, valueShape_field value_crossing_2ec_5fA_header.2, isConstant_of_priv value_crossing_2ec_5fA_kind⟩
    · exact ⟨Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_s2_header.1 value_s2_kind, valueShape_field value_s2_header.2, isConstant_of_priv value_s2_kind⟩
    · exact ⟨Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_signature_2es1_header.1 value_signature_2es1_kind, valueShape_field value_signature_2es1_header.2, isConstant_of_priv value_signature_2es1_kind⟩
    · exact ⟨Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2ea_header.1 value_norm_2ea_kind, valueShape_field value_norm_2ea_header.2, isConstant_of_priv value_norm_2ea_kind⟩
    · exact ⟨Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2esq_header.1 value_norm_2esq_kind, valueShape_field value_norm_2esq_header.2, isConstant_of_priv value_norm_2esq_kind⟩
    · exact ⟨Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2ecc_header.1 value_norm_2ecc_kind, valueShape_field value_norm_2ecc_header.2, isConstant_of_priv value_norm_2ecc_kind⟩
    · exact ⟨Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2end_header.1 value_norm_2end_kind, valueShape_field value_norm_2end_header.2, isConstant_of_priv value_norm_2end_kind⟩
    · exact ⟨Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2enc_header.1 value_norm_2enc_kind, valueShape_field value_norm_2enc_header.2, isConstant_of_priv value_norm_2enc_kind⟩
    · exact ⟨Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2eD_header.1 value_norm_2eD_kind, valueShape_field value_norm_2eD_header.2, isConstant_of_priv value_norm_2eD_kind⟩
    · exact ⟨Generated.Falcon512.Native.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_norm_2eDc_header.1 value_norm_2eDc_kind, valueShape_field value_norm_2eDc_header.2, isConstant_of_priv value_norm_2eDc_kind⟩
  sizes_H := valueShape_size value_crossing_2ec_5fA_header.2
  const44 := ⟨isConstant_of_kind value_signature_2eequation_2erealized_2econstant_2eright_kind, valueShape_field value_signature_2eequation_2erealized_2econstant_2eright_header.2, by
    rw [constEntries_of_kind value_signature_2eequation_2erealized_2econstant_2eright_kind]; decide +kernel⟩
  sigE_body := predicate_signature_2eequation_2erealized_body
  sigE_len := by
    simp only [exprLen, Expr.len, NamedOp.rows, valueShape_size value_statement_2ehhat_header.2, valueShape_size value_crossing_2ec_5fA_header.2, valueShape_size value_s2_header.2, valueShape_size value_signature_2es1_header.2]
  ca_body := predicate_crossing_2ec_5fA_2eboolean_body
  mac_body := by
    obtain ⟨real, h⟩ := predicate_mac_2eequal_body
    exact ⟨_, real, h, by decide⟩
  cross_fields := ⟨valueShape_field value_h2p_2eselect_2eraw_header.2, valueShape_field value_crossing_2ec_5fA_header.2⟩

/-! ## The honest strategy's program facts -/

/-- The values of the program of `Falcon512.Native.QROMParams` are distinct where the honest valuation reads them. -/
instance : FalconHValues program where
  not_hash_sel := by decide +kernel
  not_hash_norm := by
    intro v hv
    change v ∈ [594, 595, 596, 597, 598, 599, 600, 601, 602, 603] at hv
    revert v
    decide +kernel

private theorem source_cell_role {v : ℕ} (hlt : v < program.values.length)
    (hs : program.IsSourceValue v) (hp : program.privCellB v = true) :
    ∃ r ∈ Generated.Falcon512.Native.QROMParams.SourceRoles.roles, r.value = v := by
  have hk : (program.value v).needsSourceRole = true := by
    simp only [Value.needsSourceRole, show (program.value v).role = .source from hs, decide_true,
      Bool.true_and]
    rw [kind_of_privCellB hp]
  obtain ⟨r, hr⟩ := Generated.Falcon512.Native.QROMParams.SourceRoleFacts.rolesOk.covered v hlt hk
  obtain ⟨hm, he⟩ := sourceRoleTable_mem hr
  exact ⟨r, hm, he⟩

private theorem not_cover_274 : program.inSource (program.predicate 274) = true ∨
    program.fieldRowRealB 274 = true → False := by
  rintro (h | h)
  · rw [program.inSource_of_realization predicate_mac_2eH_role.2] at h
    contradiction
  · rw [fieldRowRealB_of_not_field predicate_mac_2eH_role.2 (by
      intro d q' a b real hb hf
      obtain ⟨c, h0⟩ := predicate_mac_2eequal_body; rw [h0] at hb; cases hb)] at h
    contradiction

private theorem not_cover_285 : program.inSource (program.predicate 285) = true ∨
    program.fieldRowRealB 285 = true → False := by
  rintro (h | h)
  · rw [program.inSource_of_realization predicate_mac_2eA_2eg0_role.2] at h
    contradiction
  · rw [fieldRowRealB_of_not_field predicate_mac_2eA_2eg0_role.2 (by
      intro d q' a b real hb hf
      obtain ⟨r, h0, hform, -⟩ := predicate_mac_body; rw [h0] at hb; cases hb; rw [hform] at hf; cases hf)] at h
    contradiction

private theorem not_cover_286 : program.inSource (program.predicate 286) = true ∨
    program.fieldRowRealB 286 = true → False := by
  rintro (h | h)
  · rw [program.inSource_of_realization predicate_mac_2eA_2eg1_role.2] at h
    contradiction
  · rw [fieldRowRealB_of_not_field predicate_mac_2eA_2eg1_role.2 (by
      intro d q' a b real hb hf
      obtain ⟨r, h0, hform, -⟩ := predicate_mac_body; rw [h0] at hb; cases hb; rw [hform] at hf; cases hf)] at h
    contradiction

private theorem not_cover_287 : program.inSource (program.predicate 287) = true ∨
    program.fieldRowRealB 287 = true → False := by
  rintro (h | h)
  · rw [program.inSource_of_realization predicate_mac_2eA_2eg2_role.2] at h
    contradiction
  · rw [fieldRowRealB_of_not_field predicate_mac_2eA_2eg2_role.2 (by
      intro d q' a b real hb hf
      obtain ⟨r, h0, hform, -⟩ := predicate_mac_body; rw [h0] at hb; cases hb; rw [hform] at hf; cases hf)] at h
    contradiction

private theorem not_cover_288 : program.inSource (program.predicate 288) = true ∨
    program.fieldRowRealB 288 = true → False := by
  rintro (h | h)
  · rw [program.inSource_of_realization predicate_mac_2eA_2eg3_role.2] at h
    contradiction
  · rw [fieldRowRealB_of_not_field predicate_mac_2eA_2eg3_role.2 (by
      intro d q' a b real hb hf
      obtain ⟨r, h0, hform, -⟩ := predicate_mac_body; rw [h0] at hb; cases hb; rw [hform] at hf; cases hf)] at h
    contradiction

private theorem not_cover_290 : program.inSource (program.predicate 290) = true ∨
    program.fieldRowRealB 290 = true → False := by
  rintro (h | h)
  · rw [program.inSource_of_realization predicate_range_2eencoding_2eslack_2ereconstruct_role.2] at h
    contradiction
  · rw [fieldRowRealB_of_not_field predicate_range_2eencoding_2eslack_2ereconstruct_role.2 (by
      intro d q' a b real hb hf
      obtain ⟨r, h0⟩ := predicate_encoding_2eslack_body; rw [h0] at hb; cases hb)] at h
    contradiction

private theorem not_cover_291 : program.inSource (program.predicate 291) = true ∨
    program.fieldRowRealB 291 = true → False := by
  rintro (h | h)
  · rw [program.inSource_of_realization predicate_range_2eencoding_2eslack_2etop_role.2] at h
    contradiction
  · rw [fieldRowRealB_of_not_field predicate_range_2eencoding_2eslack_2etop_role.2 (by
      intro d q' a b real hb hf
      obtain ⟨r, h0⟩ := predicate_encoding_2eslack_body; rw [h0] at hb; cases hb)] at h
    contradiction

private theorem not_cover_294 : program.inSource (program.predicate 294) = true ∨
    program.fieldRowRealB 294 = true → False := by
  rintro (h | h)
  · rw [program.inSource_of_type_realization predicate_mac_2eblind_2eboolean_role.2 (valueShape_role value_mac_2eblind_header.2)] at h
    contradiction
  · rw [fieldRowRealB_of_role_type predicate_mac_2eblind_2eboolean_role.2] at h
    contradiction

private theorem not_cover_296 : program.inSource (program.predicate 296) = true ∨
    program.fieldRowRealB 296 = true → False := by
  rintro (h | h)
  · rw [program.inSource_of_realization predicate_mac_2er_2eboolean_role.2] at h
    contradiction
  · rw [fieldRowRealB_of_not_field predicate_mac_2er_2eboolean_role.2 (by
      intro d q' a b real hb hf
      obtain ⟨r, h0, hform, -⟩ := predicate_mac_body; rw [h0] at hb; cases hb; rw [hform] at hf; cases hf)] at h
    contradiction

private theorem not_cover_305 : program.inSource (program.predicate 305) = true ∨
    program.fieldRowRealB 305 = true → False := by
  rintro (h | h)
  · rw [program.inSource_of_realization predicate_mac_2egq_role.2] at h
    contradiction
  · rw [fieldRowRealB_of_not_field predicate_mac_2egq_role.2 (by
      intro d q' a b real hb hf
      obtain ⟨r, h0, hform, -⟩ := predicate_mac_body; rw [h0] at hb; cases hb; rw [hform] at hf; cases hf)] at h
    contradiction

private theorem not_cover_306 : program.inSource (program.predicate 306) = true ∨
    program.fieldRowRealB 306 = true → False := by
  rintro (h | h)
  · rw [program.inSource_of_realization predicate_mac_2efinal_2eq_role.2] at h
    contradiction
  · rw [fieldRowRealB_of_not_field predicate_mac_2efinal_2eq_role.2 (by
      intro d q' a b real hb hf
      obtain ⟨r, h0, hform, -⟩ := predicate_mac_body; rw [h0] at hb; cases hb; rw [hform] at hf; cases hf)] at h
    contradiction

private theorem not_cover_307 : program.inSource (program.predicate 307) = true ∨
    program.fieldRowRealB 307 = true → False := by
  rintro (h | h)
  · rw [program.inSource_of_realization predicate_mac_role.2] at h
    contradiction
  · rw [fieldRowRealB_of_not_field predicate_mac_role.2 (by
      intro d q' a b real hb hf
      obtain ⟨c, h0⟩ := predicate_mac_2eequal_body; rw [h0] at hb; cases hb)] at h
    contradiction

namespace Facts

/-- Every source predicate and field-form row is the hash's or of `aPreds`. -/
theorem src_cover : ∀ q < program.predicates.length,
    (program.inSource (program.predicate q) = true ∨ program.fieldRowRealB q = true) →
      q < 270 ∨ q ∈ aPreds program := by
  intro q hq hs
  rw [predicates_length] at hq
  by_cases h1 : q < 270
  · exact Or.inl h1
  refine Or.inr ?_
  have hl : aPreds program = [270, 271, 272, 273, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284,
      289, 292, 293, 295, 297, 298, 299, 300, 301, 302, 303, 304, 308, 309] := rfl
  rw [hl]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  have hne : ∀ p, p ∈ [274, 285, 286, 287, 288, 290, 291, 294, 296, 305, 306, 307] → q ≠ p := by
    intro p hp hq'
    subst hq'
    revert hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact not_cover_274
    · exact not_cover_285
    · exact not_cover_286
    · exact not_cover_287
    · exact not_cover_288
    · exact not_cover_290
    · exact not_cover_291
    · exact not_cover_294
    · exact not_cover_296
    · exact not_cover_305
    · exact not_cover_306
    · exact not_cover_307
  have := hne
  simp only [List.forall_mem_cons, List.forall_mem_nil, and_true] at this
  omega

/-- The committed source values' classes. -/
theorem cell_classes : (List.range program.values.length).all (fun v =>
    !program.privCellB v || !decide (program.IsSourceValue v) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(2^16)" &&
        (v == 96 || (wordsOwner? v).isSome || v == 588 || v == 590)) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "bit" &&
        [45, 46, 47, 591].contains v) ||
      (program.valueField v == 1 && (program.value v).node.map (·.name) == some "GF(p^1)" &&
        (NormValues program).contains v)) = true := by
  rw [List.all_eq_true]
  intro v hv
  have hlt := List.mem_range.1 hv
  by_cases hp : program.privCellB v = true
  swap
  · simp [hp]
  by_cases hs : program.IsSourceValue v
  swap
  · simp [hs]
  obtain ⟨r, hm, rfl⟩ := source_cell_role hlt hs hp
  rcases HashShapeFacts.role_value_cases r hm with ho | hl
  · obtain ⟨⟨p, t⟩, hw⟩ := Option.isSome_iff_exists.1 ho
    have hv' := wordsOwner?_eq hw
    obtain ⟨_, _, _, _, _, hf, _, _, _, hn⟩ := word_facts p t
    simp only at hv'
    have hf' := hf
    rw [hv'] at hf' hn
    simp [hf', hn, ho]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl
    · rw [hl] at hp ⊢; simp [valueShape_field value_nonce_header.2, valueShape_node value_nonce_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_message_header.2, valueShape_node value_message_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_message_2ein_5fmessage_header.2, valueShape_node value_message_2ein_5fmessage_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_h2p_2eshake_2estate_2ewords_header.2, valueShape_node value_h2p_2eshake_2estate_2ewords_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_h2p_2eselect_2eraw_2ewords_header.2, valueShape_node value_h2p_2eselect_2eraw_2ewords_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_h2p_2eselect_2ecount_header.2, valueShape_node value_h2p_2eselect_2ecount_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_h2p_2eselect_2efull_header.2, valueShape_node value_h2p_2eselect_2efull_header.2, NormValues]
    · rw [hl] at hp; have hk := kind_of_privCellB hp; rw [value_statement_2ehhat_kind] at hk; cases hk
    · rw [hl] at hp ⊢; simp [valueShape_field value_crossing_2ec_5fA_header.2, valueShape_node value_crossing_2ec_5fA_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_s2_header.2, valueShape_node value_s2_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_signature_2es1_header.2, valueShape_node value_signature_2es1_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_norm_2ea_header.2, valueShape_node value_norm_2ea_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_norm_2esq_header.2, valueShape_node value_norm_2esq_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_norm_2ecc_header.2, valueShape_node value_norm_2ecc_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_norm_2end_header.2, valueShape_node value_norm_2end_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_norm_2enc_header.2, valueShape_node value_norm_2enc_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_norm_2eD_header.2, valueShape_node value_norm_2eD_header.2, NormValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_norm_2eDc_header.2, valueShape_node value_norm_2eDc_header.2, NormValues]

end Facts

/-- The program's one statement bound: the key's entries `hhat` below `q`. -/
theorem bounds : program.declaredRanges = [(593, 12289)] := statement_ranges

open Facts in
/-- **The honest-strategy facts of the program of `Falcon512.Native.QROMParams`**: the operands of every
cross-field `equal`, the covering of the source predicates, the committed source cells' classes. -/
noncomputable instance : FalconHonestFull program
    (RealizedProgram.primeNodesOf Generated.Falcon512.Native.QROMParams.Plan.plan program) where
  bounds := bounds
  crossOperands := by
    refine crossOperandsB_of_crossPredicateIds cross_predicates ?_
    intro q hq
    rw [List.mem_singleton] at hq
    subst q
    obtain ⟨c, h⟩ := predicate_mac_2eequal_body
    rw [h]
    simp [Expr.beq]
  src_cover := Facts.src_cover
  checks_list := statement_checks
  cell_classes := Facts.cell_classes

end GordieHowe.Falcon512.Native.QROMParams
