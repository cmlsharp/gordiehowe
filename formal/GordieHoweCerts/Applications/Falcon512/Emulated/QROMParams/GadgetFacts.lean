-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.Falcon512.Emulated.QROMParams.Certified
public import GordieHoweCerts.Generated.Falcon512.Emulated.QROMParams.SourceRoleFacts
public import GordieHoweCerts.Applications.Falcon512.Emulated.HonestFull
public import GordieHowe.Language.Honest.SourceRoles
public import GordieHoweCerts.Applications.Falcon512.Emulated.QROMParams.Frontend.HashFacts
public import GordieHoweCerts.Applications.Falcon512.Emulated.QROMParams.Frontend.AlgebraFacts

@[expose] public section

/-!
# GordieHowe: the gadget facts of `Falcon512.Emulated.QROMParams`

The program's instances of the honest strategy's classes, from its checked shape facts and source
roles: the hash's, the selection's and domain `A`'s facts, the operands of every cross-field
`equal`, the covering of the source predicates and the committed source cells' classes
(`FalconEHonestFull`).
-/

namespace GordieHowe.Falcon512.Emulated.QROMParams

open RealizedProgram
open Generated.Falcon512.Emulated.QROMParams.Program
open Generated.Falcon512.Emulated.QROMParams.ShapeFacts
open HashShapeFacts

/-- The honest hash facts of the program of `Falcon512.Emulated.QROMParams`. -/
instance : FalconHHonest program where
  words_checks := words_checks
  state_checks := ⟨isBitsB_of_kind value_h2p_2eshake_2estate_kind, Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_h2p_2eshake_2estate_2ewords_header.1 value_h2p_2eshake_2estate_2ewords_kind,
    valueShape_field value_h2p_2eshake_2estate_header.2, valueShape_field value_h2p_2eshake_2estate_2ewords_header.2, valueShape_size value_h2p_2eshake_2estate_header.2, valueShape_size value_h2p_2eshake_2estate_2ewords_header.2, valueType_nodeName value_h2p_2eshake_2estate_2ewords_type.2⟩
  buf_checks := ⟨Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_nonce_header.1 value_nonce_kind, Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_message_header.1 value_message_kind, Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_message_2ein_5fmessage_header.1 value_message_2ein_5fmessage_kind, valueShape_field value_nonce_header.2, valueShape_field value_message_header.2, valueShape_field value_message_2ein_5fmessage_header.2⟩

/-- The selection values of the program of `Falcon512.Emulated.QROMParams`. -/
instance : FalconHSelHonest program where
  sel_checks := ⟨Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_h2p_2eselect_2eraw_2ewords_header.1 value_h2p_2eselect_2eraw_2ewords_kind, Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_h2p_2eselect_2ecount_header.1 value_h2p_2eselect_2ecount_kind, Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_h2p_2eselect_2efull_header.1 value_h2p_2eselect_2efull_kind, isBitsB_of_kind value_h2p_2eselect_2eraw_kind,
    valueShape_field value_h2p_2eselect_2eraw_2ewords_header.2, valueShape_field value_h2p_2eselect_2eraw_header.2, valueShape_field value_h2p_2eselect_2ecount_header.2, valueShape_field value_h2p_2eselect_2efull_header.2, valueShape_size value_h2p_2eselect_2eraw_2ewords_header.2, valueShape_size value_h2p_2eselect_2eraw_header.2, valueShape_size value_h2p_2eselect_2ecount_header.2, valueShape_size value_h2p_2eselect_2efull_header.2,
    by decide +kernel, by decide +kernel, valueType_nodeName value_h2p_2eselect_2eraw_2ewords_type.2⟩

/-- The facts of honest domain `A` of the program of `Falcon512.Emulated.QROMParams`. -/
instance : FalconEHonest program where
  mag1Kind := value_magnitudes_2emag1_kind
  sqKind := value_norm_2esquares_kind
  bound := Generated.Falcon512.Emulated.QROMParams.conditions.derivable.elim fun _ hD => hD.bound
  a_cells := by
    intro v hv
    change v ∈ [595, 596, 597, 599, 600, 612, 613, 622, 623, 624] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_crossing_2ec_5fA_header.1 value_crossing_2ec_5fA_kind, valueShape_field value_crossing_2ec_5fA_header.2⟩
    · exact ⟨Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_s2_header.1 value_s2_kind, valueShape_field value_s2_header.2⟩
    · exact ⟨Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_signature_2es1_header.1 value_signature_2es1_kind, valueShape_field value_signature_2es1_header.2⟩
    · exact ⟨Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_magnitudes_2emag2_header.1 value_magnitudes_2emag2_kind, valueShape_field value_magnitudes_2emag2_header.2⟩
    · exact ⟨Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_encoding_2elow2_header.1 value_encoding_2elow2_kind, valueShape_field value_encoding_2elow2_header.2⟩
    · exact ⟨Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_range_2emagnitudes_2emag1_2ed0_header.1 value_range_2emagnitudes_2emag1_2ed0_kind, valueShape_field value_range_2emagnitudes_2emag1_2ed0_header.2⟩
    · exact ⟨Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_range_2emagnitudes_2emag1_2ed1_header.1 value_range_2emagnitudes_2emag1_2ed1_kind, valueShape_field value_range_2emagnitudes_2emag1_2ed1_header.2⟩
    · exact ⟨Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_range_2enorm_2ebound_2ed0_header.1 value_range_2enorm_2ebound_2ed0_kind, valueShape_field value_range_2enorm_2ebound_2ed0_header.2⟩
    · exact ⟨Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_range_2enorm_2ebound_2ed1_header.1 value_range_2enorm_2ebound_2ed1_kind, valueShape_field value_range_2enorm_2ebound_2ed1_header.2⟩
    · exact ⟨Generated.Falcon512.Emulated.QROMParams.conditions.wellFormed.privCellB_of_kind_priv value_range_2enorm_2ebound_2ed2_header.1 value_range_2enorm_2ebound_2ed2_kind, valueShape_field value_range_2enorm_2ebound_2ed2_header.2⟩
  digitSizes := ⟨valueShape_size value_range_2emagnitudes_2emag1_2ed0_header.2, valueShape_size value_range_2emagnitudes_2emag1_2ed1_header.2, valueShape_size value_range_2enorm_2ebound_2ed0_header.2, valueShape_size value_range_2enorm_2ebound_2ed1_header.2, valueShape_size value_range_2enorm_2ebound_2ed2_header.2⟩
  lens := value_norm_2esquares_header.1
  sigForm := by
    obtain ⟨real, h, hf, -⟩ := predicate_signature_2eequation_2esource_body
    exact ⟨real, h, by rw [hf]; rfl⟩
  high2Form := by
    obtain ⟨real, h, hf, -⟩ := predicate_encoding_2ehigh2_body
    exact ⟨real, h, by rw [hf]; rfl⟩
  caBody := predicate_crossing_2ec_5fA_2eboolean_body
  macBody := by
    obtain ⟨real, h⟩ := predicate_mac_2eequal_body
    exact ⟨_, real, h, by decide⟩
  rawField := valueShape_field value_h2p_2eselect_2eraw_header.2

/-! ## The honest strategy's program facts -/

private theorem source_cell_role {v : ℕ} (hlt : v < program.values.length)
    (hs : program.IsSourceValue v) (hp : program.privCellB v = true) :
    ∃ r ∈ Generated.Falcon512.Emulated.QROMParams.SourceRoles.roles, r.value = v := by
  have hk : (program.value v).needsSourceRole = true := by
    simp only [Value.needsSourceRole, show (program.value v).role = .source from hs, decide_true,
      Bool.true_and]
    rw [kind_of_privCellB hp]
  obtain ⟨r, hr⟩ := Generated.Falcon512.Emulated.QROMParams.SourceRoleFacts.rolesOk.covered v hlt hk
  obtain ⟨hm, he⟩ := sourceRoleTable_mem hr
  exact ⟨r, hm, he⟩

namespace Facts

/-- Every source predicate is the hash's or of `aPreds`. -/
theorem src_cover : ∀ q < program.predicates.length,
    program.inSource (program.predicate q) = true → q < 270 ∨ q ∈ aPreds := by
  intro q hq hs
  rw [predicates_length] at hq
  by_cases h1 : q < 270
  · exact Or.inl h1
  refine Or.inr ?_
  have hl : aPreds = [270, 271, 272, 273, 275, 276, 277, 284, 286, 287, 288, 289, 290, 297, 298,
      299] := rfl
  rw [hl]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  have hq' : q ∈ [274, 278, 279, 280, 281, 282, 283, 285, 291, 292, 293, 294, 295, 296] ∨ q ∈ [270, 271, 272, 273, 275, 276, 277, 284, 286,
      287, 288, 289, 290, 297, 298, 299] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  rcases hq' with hx | hx
  · exfalso
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [program.inSource_of_realization predicate_mac_2eH_role.2] at hs; cases hs
    · rw [program.inSource_of_realization predicate_mac_2eA_role.2] at hs; cases hs
    · rw [program.inSource_of_realization predicate_signature_2eequation_2erealized_role.2] at hs; cases hs
    · rw [program.inSource_of_realization predicate_range_2emagnitudes_2emag1_2etop_role.2] at hs; cases hs
    · rw [program.inSource_of_realization predicate_range_2eencoding_2ebudget_2ereconstruct_role.2] at hs; cases hs
    · rw [program.inSource_of_realization predicate_range_2eencoding_2ebudget_2etop_role.2] at hs; cases hs
    · rw [program.inSource_of_realization predicate_range_2enorm_2ebound_2etop_role.2] at hs; cases hs
    · rw [program.inSource_of_type_realization predicate_mac_2eblind_2eboolean_role.2 (valueShape_role value_mac_2eblind_header.2)] at hs; cases hs
    · rw [program.inSource_of_realization predicate_mac_2elow_role.2] at hs; cases hs
    · rw [program.inSource_of_realization predicate_mac_2ehigh_role.2] at hs; cases hs
    · rw [program.inSource_of_realization predicate_mac_2enowrap_role.2] at hs; cases hs
    · rw [program.inSource_of_realization predicate_signature_2eequation_2eq_role.2] at hs; cases hs
    · rw [program.inSource_of_realization predicate_encoding_2ehigh2_2eq_role.2] at hs; cases hs
    · rw [program.inSource_of_realization predicate_mac_role.2] at hs; cases hs
  · simpa only [List.mem_cons, List.not_mem_nil, or_false] using hx

/-- The committed source values' classes. -/
theorem cell_classes : (List.range program.values.length).all (fun v =>
    !program.privCellB v || !decide (program.IsSourceValue v) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(2^16)" &&
        (v == 96 || (wordsOwner? v).isSome || v == 588 || v == 590)) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "bit" &&
        [45, 46, 47, 591].contains v) ||
      (program.valueField v == 1 && (program.value v).node.map (·.name) == some "GF(p^1)" &&
        aValues.contains v)) = true := by
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
    rcases hl with hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl
    · rw [hl] at hp ⊢; simp [valueShape_field value_nonce_header.2, valueShape_node value_nonce_header.2, aValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_message_header.2, valueShape_node value_message_header.2, aValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_message_2ein_5fmessage_header.2, valueShape_node value_message_2ein_5fmessage_header.2, aValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_h2p_2eshake_2estate_2ewords_header.2, valueShape_node value_h2p_2eshake_2estate_2ewords_header.2, aValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_h2p_2eselect_2eraw_2ewords_header.2, valueShape_node value_h2p_2eselect_2eraw_2ewords_header.2, aValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_h2p_2eselect_2ecount_header.2, valueShape_node value_h2p_2eselect_2ecount_header.2, aValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_h2p_2eselect_2efull_header.2, valueShape_node value_h2p_2eselect_2efull_header.2, aValues]
    · rw [hl] at hp; have hk := kind_of_privCellB hp; rw [value_statement_2ehhat_kind] at hk; cases hk
    · rw [hl] at hp; have hk := kind_of_privCellB hp; rw [value_key_2ecoefficients_kind] at hk; cases hk
    · rw [hl] at hp ⊢; simp [valueShape_field value_crossing_2ec_5fA_header.2, valueShape_node value_crossing_2ec_5fA_header.2, aValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_s2_header.2, valueShape_node value_s2_header.2, aValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_signature_2es1_header.2, valueShape_node value_signature_2es1_header.2, aValues]
    · rw [hl] at hp; have hk := kind_of_privCellB hp; rw [value_magnitudes_2emag1_kind] at hk; cases hk
    · rw [hl] at hp ⊢; simp [valueShape_field value_magnitudes_2emag2_header.2, valueShape_node value_magnitudes_2emag2_header.2, aValues]
    · rw [hl] at hp ⊢; simp [valueShape_field value_encoding_2elow2_header.2, valueShape_node value_encoding_2elow2_header.2, aValues]
    · rw [hl] at hp; have hk := kind_of_privCellB hp; rw [value_norm_2esquares_kind] at hk; cases hk

end Facts

/-- The program's statement bounds: `hhat` and the key's coefficients below `q`. -/
theorem bounds : program.declaredRanges = [(593, 12289), (594, 12289)] := statement_ranges

/-- **The honest-strategy facts of the program of `Falcon512.Emulated.QROMParams`**: the operands of
every cross-field `equal`, the covering of the source predicates, the committed source cells'
classes. -/
noncomputable instance : FalconEHonestFull program
    (RealizedProgram.primeNodesOf Generated.Falcon512.Emulated.QROMParams.Plan.plan program) where
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

end GordieHowe.Falcon512.Emulated.QROMParams
